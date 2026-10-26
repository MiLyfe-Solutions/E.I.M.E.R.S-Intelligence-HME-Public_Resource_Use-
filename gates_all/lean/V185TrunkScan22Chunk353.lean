import V185TrunkScan22Chunk352

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3150125 : List Nat := [1, 5, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3150125 : Nat := 118140960795 + 3150125 * 2 ^ 59
def prefixEnd_3150125 : Nat := 4983230072969 + 3 ^ 40 * 3150125 * 2
def baseEnd_3150125 : Nat := 1078352164496395236766897

theorem tailTrace_3150125 : CollatzResearch.WordTrace tailWord_3150125 prefixEnd_3150125 1078352164496395236766897 := by
  unfold tailWord_3150125
  simp only [CollatzResearch.WordTrace]
  refine ⟨114894497712642598362859829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76596331808428398908573219 114894497712642598362859829)
  ·
    refine ⟨10771359160560243596518109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114894497712642598362859829 10771359160560243596518109)
    ·
      refine ⟨4039259685210091348694291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10771359160560243596518109 4039259685210091348694291)
      ·
        refine ⟨6058889527815137023041437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4039259685210091348694291 6058889527815137023041437)
        ·
          refine ⟨2272083572930676383640539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6058889527815137023041437 2272083572930676383640539)
          ·
            refine ⟨3408125359396014575460809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272083572930676383640539 3408125359396014575460809)
            ·
              refine ⟨2556094019547010931595607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3408125359396014575460809 2556094019547010931595607)
              ·
                refine ⟨3834141029320516397393411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556094019547010931595607 3834141029320516397393411)
                ·
                  refine ⟨5751211543980774596090117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834141029320516397393411 5751211543980774596090117)
                  ·
                    refine ⟨1078352164496395236766897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5751211543980774596090117 1078352164496395236766897)
                    ·
                      rfl

theorem cell22_3150125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3150125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150125 prefixEnd_3150125 := by exact prefixLift 3150125
  have htrace : WordTrace (prefixWord ++ tailWord_3150125) baseStart_3150125 baseEnd_3150125 := by
    simpa [prefixWord, tailWord_3150125, baseEnd_3150125] using wordTrace_append hprefix tailTrace_3150125
  have hstable : (prefixWord ++ tailWord_3150125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150125).length < 2 ^ (prefixWord ++ tailWord_3150125).sum := by decide
  have hdescent : baseEnd_3150125 < baseStart_3150125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150162 : List Nat := [3, 2, 2, 1, 1, 1, 2, 5, 5]
def baseStart_3150162 : Nat := 118140960795 + 3150162 * 2 ^ 59
def prefixEnd_3150162 : Nat := 4983230072969 + 3 ^ 40 * 3150162 * 2
def baseEnd_3150162 : Nat := 359454943450846491197261

theorem tailTrace_3150162 : CollatzResearch.WordTrace tailWord_3150162 prefixEnd_3150162 359454943450846491197261 := by
  unfold tailWord_3150162
  simp only [CollatzResearch.WordTrace]
  refine ⟨28723961803377138420489185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76597231475672369121304493 28723961803377138420489185)
  ·
    refine ⟨21542971352532853815366889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28723961803377138420489185 21542971352532853815366889)
    ·
      refine ⟨16157228514399640361525167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21542971352532853815366889 16157228514399640361525167)
      ·
        refine ⟨24235842771599460542287751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16157228514399640361525167 24235842771599460542287751)
        ·
          refine ⟨36353764157399190813431627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24235842771599460542287751 36353764157399190813431627)
          ·
            refine ⟨54530646236098786220147441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36353764157399190813431627 54530646236098786220147441)
            ·
              refine ⟨40897984677074089665110581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54530646236098786220147441 40897984677074089665110581)
              ·
                refine ⟨3834186063475695906104117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40897984677074089665110581 3834186063475695906104117)
                ·
                  refine ⟨359454943450846491197261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3834186063475695906104117 359454943450846491197261)
                  ·
                    rfl

theorem cell22_3150162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_3150162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150162 prefixEnd_3150162 := by exact prefixLift 3150162
  have htrace : WordTrace (prefixWord ++ tailWord_3150162) baseStart_3150162 baseEnd_3150162 := by
    simpa [prefixWord, tailWord_3150162, baseEnd_3150162] using wordTrace_append hprefix tailTrace_3150162
  have hstable : (prefixWord ++ tailWord_3150162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150162).length < 2 ^ (prefixWord ++ tailWord_3150162).sum := by decide
  have hdescent : baseEnd_3150162 < baseStart_3150162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150174 : List Nat := [4, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_3150174 : Nat := 118140960795 + 3150174 * 2 ^ 59
def prefixEnd_3150174 : Nat := 4983230072969 + 3 ^ 40 * 3150174 * 2
def baseEnd_3150174 : Nat := 359456312732591814097249

theorem tailTrace_3150174 : CollatzResearch.WordTrace tailWord_3150174 prefixEnd_3150174 359456312732591814097249 := by
  unfold tailWord_3150174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14362035611183134966424197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76597523259643386487595717 14362035611183134966424197)
  ·
    refine ⟨2692881677096837806204537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14362035611183134966424197 2692881677096837806204537)
    ·
      refine ⟨2019661257822628354653403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2692881677096837806204537 2019661257822628354653403)
      ·
        refine ⟨3029491886733942531980105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2019661257822628354653403 3029491886733942531980105)
        ·
          refine ⟨2272118915050456898985079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3029491886733942531980105 2272118915050456898985079)
          ·
            refine ⟨3408178372575685348477619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272118915050456898985079 3408178372575685348477619)
            ·
              refine ⟨5112267558863528022716429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3408178372575685348477619 5112267558863528022716429)
              ·
                refine ⟨1917100334573823008518661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5112267558863528022716429 1917100334573823008518661)
                ·
                  refine ⟨359456312732591814097249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1917100334573823008518661 359456312732591814097249)
                  ·
                    rfl

theorem cell22_3150174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_3150174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150174 prefixEnd_3150174 := by exact prefixLift 3150174
  have htrace : WordTrace (prefixWord ++ tailWord_3150174) baseStart_3150174 baseEnd_3150174 := by
    simpa [prefixWord, tailWord_3150174, baseEnd_3150174] using wordTrace_append hprefix tailTrace_3150174
  have hstable : (prefixWord ++ tailWord_3150174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150174).length < 2 ^ (prefixWord ++ tailWord_3150174).sum := by decide
  have hdescent : baseEnd_3150174 < baseStart_3150174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150183 : List Nat := [1, 1, 5, 1, 3, 3, 1, 3, 1, 3]
def baseStart_3150183 : Nat := 118140960795 + 3150183 * 2 ^ 59
def prefixEnd_3150183 : Nat := 4983230072969 + 3 ^ 40 * 3150183 * 2
def baseEnd_3150183 : Nat := 1078372019081702418816719

theorem tailTrace_3150183 : CollatzResearch.WordTrace tailWord_3150183 prefixEnd_3150183 1078372019081702418816719 := by
  unfold tailWord_3150183
  simp only [CollatzResearch.WordTrace]
  refine ⟨114896613146432474268471203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76597742097621649512314135 114896613146432474268471203)
  ·
    refine ⟨172344919719648711402706805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114896613146432474268471203 172344919719648711402706805)
    ·
      refine ⟨16157336223717066694003763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172344919719648711402706805 16157336223717066694003763)
      ·
        refine ⟨24236004335575600041005645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16157336223717066694003763 24236004335575600041005645)
        ·
          refine ⟨9088501625840850015377117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24236004335575600041005645 9088501625840850015377117)
          ·
            refine ⟨3408188109690318755766419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9088501625840850015377117 3408188109690318755766419)
            ·
              refine ⟨5112282164535478133649629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3408188109690318755766419 5112282164535478133649629)
              ·
                refine ⟨1917105811700804300118611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5112282164535478133649629 1917105811700804300118611)
                ·
                  refine ⟨2875658717551206450177917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917105811700804300118611 2875658717551206450177917)
                  ·
                    refine ⟨1078372019081702418816719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2875658717551206450177917 1078372019081702418816719)
                    ·
                      rfl

theorem cell22_3150183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_3150183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150183 prefixEnd_3150183 := by exact prefixLift 3150183
  have htrace : WordTrace (prefixWord ++ tailWord_3150183) baseStart_3150183 baseEnd_3150183 := by
    simpa [prefixWord, tailWord_3150183, baseEnd_3150183] using wordTrace_append hprefix tailTrace_3150183
  have hstable : (prefixWord ++ tailWord_3150183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150183).length < 2 ^ (prefixWord ++ tailWord_3150183).sum := by decide
  have hdescent : baseEnd_3150183 < baseStart_3150183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150269 : List Nat := [1, 4, 1, 2, 2, 4, 1, 7]
def baseStart_3150269 : Nat := 118140960795 + 3150269 * 2 ^ 59
def prefixEnd_3150269 : Nat := 4983230072969 + 3 ^ 40 * 3150269 * 2
def baseEnd_3150269 : Nat := 119822384293247429018495

theorem tailTrace_3150269 : CollatzResearch.WordTrace tailWord_3150269 prefixEnd_3150269 119822384293247429018495 := by
  unfold tailWord_3150269
  simp only [CollatzResearch.WordTrace]
  refine ⟨114899749824120910956101861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76599833216080607304067907 114899749824120910956101861)
  ·
    refine ⟨21543703092022670804269099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114899749824120910956101861 21543703092022670804269099)
    ·
      refine ⟨32315554638034006206403649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21543703092022670804269099 32315554638034006206403649)
      ·
        refine ⟨24236665978525504654802737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32315554638034006206403649 24236665978525504654802737)
        ·
          refine ⟨18177499483894128491102053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24236665978525504654802737 18177499483894128491102053)
          ·
            refine ⟨3408281153230149092081635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18177499483894128491102053 3408281153230149092081635)
            ·
              refine ⟨5112421729845223638122453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3408281153230149092081635 5112421729845223638122453)
              ·
                refine ⟨119822384293247429018495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5112421729845223638122453 119822384293247429018495)
                ·
                  rfl

theorem cell22_3150269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 7].length) (baseStart_3150269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150269 prefixEnd_3150269 := by exact prefixLift 3150269
  have htrace : WordTrace (prefixWord ++ tailWord_3150269) baseStart_3150269 baseEnd_3150269 := by
    simpa [prefixWord, tailWord_3150269, baseEnd_3150269] using wordTrace_append hprefix tailTrace_3150269
  have hstable : (prefixWord ++ tailWord_3150269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150269).length < 2 ^ (prefixWord ++ tailWord_3150269).sum := by decide
  have hdescent : baseEnd_3150269 < baseStart_3150269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150282 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_3150282 : Nat := 118140960795 + 3150282 * 2 ^ 59
def prefixEnd_3150282 : Nat := 4983230072969 + 3 ^ 40 * 3150282 * 2
def baseEnd_3150282 : Nat := 1078405908804899160591415

theorem tailTrace_3150282 : CollatzResearch.WordTrace tailWord_3150282 prefixEnd_3150282 1078405908804899160591415 := by
  unfold tailWord_3150282
  simp only [CollatzResearch.WordTrace]
  refine ⟨28725055993268453544081275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76600149315382542784216733 28725055993268453544081275)
  ·
    refine ⟨43087583989902680316121913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28725055993268453544081275 43087583989902680316121913)
    ·
      refine ⟨32315687992427010237091435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43087583989902680316121913 32315687992427010237091435)
      ·
        refine ⟨48473531988640515355637153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32315687992427010237091435 48473531988640515355637153)
        ·
          refine ⟨36355148991480386516727865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48473531988640515355637153 36355148991480386516727865)
          ·
            refine ⟨27266361743610289887545899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36355148991480386516727865 27266361743610289887545899)
            ·
              refine ⟨40899542615415434831318849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27266361743610289887545899 40899542615415434831318849)
              ·
                refine ⟨30674656961561576123489137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40899542615415434831318849 30674656961561576123489137)
                ·
                  refine ⟨23005992721171182092616853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30674656961561576123489137 23005992721171182092616853)
                  ·
                    refine ⟨1078405908804899160591415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23005992721171182092616853 1078405908804899160591415)
                    ·
                      rfl

theorem cell22_3150282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_3150282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150282 prefixEnd_3150282 := by exact prefixLift 3150282
  have htrace : WordTrace (prefixWord ++ tailWord_3150282) baseStart_3150282 baseEnd_3150282 := by
    simpa [prefixWord, tailWord_3150282, baseEnd_3150282] using wordTrace_append hprefix tailTrace_3150282
  have hstable : (prefixWord ++ tailWord_3150282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150282).length < 2 ^ (prefixWord ++ tailWord_3150282).sum := by decide
  have hdescent : baseEnd_3150282 < baseStart_3150282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150297 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 7]
def baseStart_3150297 : Nat := 118140960795 + 3150297 * 2 ^ 59
def prefixEnd_3150297 : Nat := 4983230072969 + 3 ^ 40 * 3150297 * 2
def baseEnd_3150297 : Nat := 359470347870481373822123

theorem tailTrace_3150297 : CollatzResearch.WordTrace tailWord_3150297 prefixEnd_3150297 359470347870481373822123 := by
  unfold tailWord_3150297
  simp only [CollatzResearch.WordTrace]
  refine ⟨114900771068019471738121145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76600514045346314492080763 114900771068019471738121145)
  ·
    refine ⟨86175578301014603803590859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114900771068019471738121145 86175578301014603803590859)
    ·
      refine ⟨129263367451521905705386289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86175578301014603803590859 129263367451521905705386289)
      ·
        refine ⟨96947525588641429279039717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129263367451521905705386289 96947525588641429279039717)
        ·
          refine ⟨18177661047870267989819947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96947525588641429279039717 18177661047870267989819947)
          ·
            refine ⟨27266491571805401984729921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18177661047870267989819947 27266491571805401984729921)
            ·
              refine ⟨20449868678854051488547441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27266491571805401984729921 20449868678854051488547441)
              ·
                refine ⟨15337401509140538616410581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20449868678854051488547441 15337401509140538616410581)
                ·
                  refine ⟨359470347870481373822123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15337401509140538616410581 359470347870481373822123)
                  ·
                    rfl

theorem cell22_3150297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_3150297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150297 prefixEnd_3150297 := by exact prefixLift 3150297
  have htrace : WordTrace (prefixWord ++ tailWord_3150297) baseStart_3150297 baseEnd_3150297 := by
    simpa [prefixWord, tailWord_3150297, baseEnd_3150297] using wordTrace_append hprefix tailTrace_3150297
  have hstable : (prefixWord ++ tailWord_3150297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150297).length < 2 ^ (prefixWord ++ tailWord_3150297).sum := by decide
  have hdescent : baseEnd_3150297 < baseStart_3150297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150314 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 7]
def baseStart_3150314 : Nat := 118140960795 + 3150314 * 2 ^ 59
def prefixEnd_3150314 : Nat := 4983230072969 + 3 ^ 40 * 3150314 * 2
def baseEnd_3150314 : Nat := 359472287686287247930439

theorem tailTrace_3150314 : CollatzResearch.WordTrace tailWord_3150314 prefixEnd_3150314 359472287686287247930439 := by
  unfold tailWord_3150314
  simp only [CollatzResearch.WordTrace]
  refine ⟨28725347777239470910372499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76600927405971922427659997 28725347777239470910372499)
  ·
    refine ⟨43088021665859206365558749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28725347777239470910372499 43088021665859206365558749)
    ·
      refine ⟨16158008124697202387084531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43088021665859206365558749 16158008124697202387084531)
      ·
        refine ⟨24237012187045803580626797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16158008124697202387084531 24237012187045803580626797)
        ·
          refine ⟨9088879570142176342735049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24237012187045803580626797 9088879570142176342735049)
          ·
            refine ⟨6816659677606632257051287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9088879570142176342735049 6816659677606632257051287)
            ·
              refine ⟨10224989516409948385576931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816659677606632257051287 10224989516409948385576931)
              ·
                refine ⟨15337484274614922578365397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10224989516409948385576931 15337484274614922578365397)
                ·
                  refine ⟨359472287686287247930439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15337484274614922578365397 359472287686287247930439)
                  ·
                    rfl

theorem cell22_3150314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_3150314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150314 prefixEnd_3150314 := by exact prefixLift 3150314
  have htrace : WordTrace (prefixWord ++ tailWord_3150314) baseStart_3150314 baseEnd_3150314 := by
    simpa [prefixWord, tailWord_3150314, baseEnd_3150314] using wordTrace_append hprefix tailTrace_3150314
  have hstable : (prefixWord ++ tailWord_3150314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150314).length < 2 ^ (prefixWord ++ tailWord_3150314).sum := by decide
  have hdescent : baseEnd_3150314 < baseStart_3150314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150318 : List Nat := [4, 1, 2, 1, 2, 2, 2, 4, 1, 3]
def baseStart_3150318 : Nat := 118140960795 + 3150318 * 2 ^ 59
def prefixEnd_3150318 : Nat := 4983230072969 + 3 ^ 40 * 3150318 * 2
def baseEnd_3150318 : Nat := 1078418232340607066691305

theorem tailTrace_3150318 : CollatzResearch.WordTrace tailWord_3150318 prefixEnd_3150318 1078418232340607066691305 := by
  unfold tailWord_3150318
  simp only [CollatzResearch.WordTrace]
  refine ⟨14362692125117924040579451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76601024667295594883090405 14362692125117924040579451)
  ·
    refine ⟨21544038187676886060869177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14362692125117924040579451 21544038187676886060869177)
    ·
      refine ⟨16158028640757664545651883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21544038187676886060869177 16158028640757664545651883)
      ·
        refine ⟨24237042961136496818477825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16158028640757664545651883 24237042961136496818477825)
        ·
          refine ⟨18177782220852372613858369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24237042961136496818477825 18177782220852372613858369)
          ·
            refine ⟨13633336665639279460393777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18177782220852372613858369 13633336665639279460393777)
            ·
              refine ⟨10225002499229459595295333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13633336665639279460393777 10225002499229459595295333)
              ·
                refine ⟨1917187968605523674117875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10225002499229459595295333 1917187968605523674117875)
                ·
                  refine ⟨2875781952908285511176813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917187968605523674117875 2875781952908285511176813)
                  ·
                    refine ⟨1078418232340607066691305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2875781952908285511176813 1078418232340607066691305)
                    ·
                      rfl

theorem cell22_3150318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_3150318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150318 prefixEnd_3150318 := by exact prefixLift 3150318
  have htrace : WordTrace (prefixWord ++ tailWord_3150318) baseStart_3150318 baseEnd_3150318 := by
    simpa [prefixWord, tailWord_3150318, baseEnd_3150318] using wordTrace_append hprefix tailTrace_3150318
  have hstable : (prefixWord ++ tailWord_3150318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150318).length < 2 ^ (prefixWord ++ tailWord_3150318).sum := by decide
  have hdescent : baseEnd_3150318 < baseStart_3150318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150376 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 6]
def baseStart_3150376 : Nat := 118140960795 + 3150376 * 2 ^ 59
def prefixEnd_3150376 : Nat := 4983230072969 + 3 ^ 40 * 3150376 * 2
def baseEnd_3150376 : Nat := 359479362308638082913709

theorem tailTrace_3150376 : CollatzResearch.WordTrace tailWord_3150376 prefixEnd_3150376 359479362308638082913709 := by
  unfold tailWord_3150376
  simp only [CollatzResearch.WordTrace]
  refine ⟨57451826217366634115123491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76602434956488845486831321 57451826217366634115123491)
  ·
    refine ⟨86177739326049951172685237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57451826217366634115123491 86177739326049951172685237)
    ·
      refine ⟨8079163061817182922439241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86177739326049951172685237 8079163061817182922439241)
      ·
        refine ⟨6059372296362887191829431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8079163061817182922439241 6059372296362887191829431)
        ·
          refine ⟨9089058444544330787744147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6059372296362887191829431 9089058444544330787744147)
          ·
            refine ⟨13633587666816496181616221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9089058444544330787744147 13633587666816496181616221)
            ·
              refine ⟨5112595375056186068106083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13633587666816496181616221 5112595375056186068106083)
              ·
                refine ⟨7668893062584279102159125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5112595375056186068106083 7668893062584279102159125)
                ·
                  refine ⟨359479362308638082913709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7668893062584279102159125 359479362308638082913709)
                  ·
                    rfl

theorem cell22_3150376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 6].length) (baseStart_3150376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150376 prefixEnd_3150376 := by exact prefixLift 3150376
  have htrace : WordTrace (prefixWord ++ tailWord_3150376) baseStart_3150376 baseEnd_3150376 := by
    simpa [prefixWord, tailWord_3150376, baseEnd_3150376] using wordTrace_append hprefix tailTrace_3150376
  have hstable : (prefixWord ++ tailWord_3150376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150376).length < 2 ^ (prefixWord ++ tailWord_3150376).sum := by decide
  have hdescent : baseEnd_3150376 < baseStart_3150376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150389 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_3150389 : Nat := 118140960795 + 3150389 * 2 ^ 59
def prefixEnd_3150389 : Nat := 4983230072969 + 3 ^ 40 * 3150389 * 2
def baseEnd_3150389 : Nat := 1078442537091586548166087

theorem tailTrace_3150389 : CollatzResearch.WordTrace tailWord_3150389 prefixEnd_3150389 1078442537091586548166087 := by
  unfold tailWord_3150389
  simp only [CollatzResearch.WordTrace]
  refine ⟨114904126583686171450470221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76602751055790780966980147 114904126583686171450470221)
  ·
    refine ⟨43089047468882314293926333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114904126583686171450470221 43089047468882314293926333)
    ·
      refine ⟨16158392800830867860222375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43089047468882314293926333 16158392800830867860222375)
      ·
        refine ⟨24237589201246301790333563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16158392800830867860222375 24237589201246301790333563)
        ·
          refine ⟨36356383801869452685500345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24237589201246301790333563 36356383801869452685500345)
          ·
            refine ⟨27267287851402089514125259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36356383801869452685500345 27267287851402089514125259)
            ·
              refine ⟨40900931777103134271187889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27267287851402089514125259 40900931777103134271187889)
              ·
                refine ⟨30675698832827350703390917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40900931777103134271187889 30675698832827350703390917)
                ·
                  refine ⟨5751693531155128256885797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30675698832827350703390917 5751693531155128256885797)
                  ·
                    refine ⟨1078442537091586548166087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5751693531155128256885797 1078442537091586548166087)
                    ·
                      rfl

theorem cell22_3150389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_3150389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150389 prefixEnd_3150389 := by exact prefixLift 3150389
  have htrace : WordTrace (prefixWord ++ tailWord_3150389) baseStart_3150389 baseEnd_3150389 := by
    simpa [prefixWord, tailWord_3150389, baseEnd_3150389] using wordTrace_append hprefix tailTrace_3150389
  have hstable : (prefixWord ++ tailWord_3150389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150389).length < 2 ^ (prefixWord ++ tailWord_3150389).sum := by decide
  have hdescent : baseEnd_3150389 < baseStart_3150389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150391 : List Nat := [1, 1, 3, 1, 2, 3, 3, 3, 2, 3]
def baseStart_3150391 : Nat := 118140960795 + 3150391 * 2 ^ 59
def prefixEnd_3150391 : Nat := 4983230072969 + 3 ^ 40 * 3150391 * 2
def baseEnd_3150391 : Nat := 1078443221732459209616081

theorem tailTrace_3150391 : CollatzResearch.WordTrace tailWord_3150391 prefixEnd_3150391 1078443221732459209616081 := by
  unfold tailWord_3150391
  simp only [CollatzResearch.WordTrace]
  refine ⟨114904199529678925792043027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76602799686452617194695351 114904199529678925792043027)
  ·
    refine ⟨172356299294518388688064541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114904199529678925792043027 172356299294518388688064541)
    ·
      refine ⟨64633612235444395758024203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172356299294518388688064541 64633612235444395758024203)
      ·
        refine ⟨96950418353166593637036305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64633612235444395758024203 96950418353166593637036305)
        ·
          refine ⟨72712813764874945227777229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96950418353166593637036305 72712813764874945227777229)
          ·
            refine ⟨27267305161828104460416461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72712813764874945227777229 27267305161828104460416461)
            ·
              refine ⟨10225239435685539172656173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27267305161828104460416461 10225239435685539172656173)
              ·
                refine ⟨3834464788382077189746065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10225239435685539172656173 3834464788382077189746065)
                ·
                  refine ⟨2875848591286557892309549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3834464788382077189746065 2875848591286557892309549)
                  ·
                    refine ⟨1078443221732459209616081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2875848591286557892309549 1078443221732459209616081)
                    ·
                      rfl

theorem cell22_3150391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_3150391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150391 prefixEnd_3150391 := by exact prefixLift 3150391
  have htrace : WordTrace (prefixWord ++ tailWord_3150391) baseStart_3150391 baseEnd_3150391 := by
    simpa [prefixWord, tailWord_3150391, baseEnd_3150391] using wordTrace_append hprefix tailTrace_3150391
  have hstable : (prefixWord ++ tailWord_3150391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150391).length < 2 ^ (prefixWord ++ tailWord_3150391).sum := by decide
  have hdescent : baseEnd_3150391 < baseStart_3150391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150436 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_3150436 : Nat := 118140960795 + 3150436 * 2 ^ 59
def prefixEnd_3150436 : Nat := 4983230072969 + 3 ^ 40 * 3150436 * 2
def baseEnd_3150436 : Nat := 1078458626152094092240943

theorem tailTrace_3150436 : CollatzResearch.WordTrace tailWord_3150436 prefixEnd_3150436 1078458626152094092240943 := by
  unfold tailWord_3150436
  simp only [CollatzResearch.WordTrace]
  refine ⟨57452920407257949238715581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76603893876343932318287441 57452920407257949238715581)
  ·
    refine ⟨21544845152721730964518343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57452920407257949238715581 21544845152721730964518343)
    ·
      refine ⟨32317267729082596446777515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21544845152721730964518343 32317267729082596446777515)
      ·
        refine ⟨48475901593623894670166273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32317267729082596446777515 48475901593623894670166273)
        ·
          refine ⟨36356926195217921002624705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48475901593623894670166273 36356926195217921002624705)
          ·
            refine ⟨27267694646413440751968529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36356926195217921002624705 27267694646413440751968529)
            ·
              refine ⟨20450770984810080563976397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27267694646413440751968529 20450770984810080563976397)
              ·
                refine ⟨7669039119303780211491149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20450770984810080563976397 7669039119303780211491149)
                ·
                  refine ⟨2875889669738917579309181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7669039119303780211491149 2875889669738917579309181)
                  ·
                    refine ⟨1078458626152094092240943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2875889669738917579309181 1078458626152094092240943)
                    ·
                      rfl

theorem cell22_3150436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_3150436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150436 prefixEnd_3150436 := by exact prefixLift 3150436
  have htrace : WordTrace (prefixWord ++ tailWord_3150436) baseStart_3150436 baseEnd_3150436 := by
    simpa [prefixWord, tailWord_3150436, baseEnd_3150436] using wordTrace_append hprefix tailTrace_3150436
  have hstable : (prefixWord ++ tailWord_3150436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150436).length < 2 ^ (prefixWord ++ tailWord_3150436).sum := by decide
  have hdescent : baseEnd_3150436 < baseStart_3150436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150526 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_3150526 : Nat := 118140960795 + 3150526 * 2 ^ 59
def prefixEnd_3150526 : Nat := 4983230072969 + 3 ^ 40 * 3150526 * 2
def baseEnd_3150526 : Nat := 1078489434991363857490667

theorem tailTrace_3150526 : CollatzResearch.WordTrace tailWord_3150526 prefixEnd_3150526 1078489434991363857490667 := by
  unfold tailWord_3150526
  simp only [CollatzResearch.WordTrace]
  refine ⟨14363640423023730481025929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76606082256126562565471621 14363640423023730481025929)
  ·
    refine ⟨10772730317267797860769447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14363640423023730481025929 10772730317267797860769447)
    ·
      refine ⟨16159095475901696791154171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10772730317267797860769447 16159095475901696791154171)
      ·
        refine ⟨24238643213852545186731257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16159095475901696791154171 24238643213852545186731257)
        ·
          refine ⟨18178982410389408890048443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24238643213852545186731257 18178982410389408890048443)
          ·
            refine ⟨27268473615584113335072665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18178982410389408890048443 27268473615584113335072665)
            ·
              refine ⟨20451355211688085001304499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27268473615584113335072665 20451355211688085001304499)
              ·
                refine ⟨30677032817532127501956749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20451355211688085001304499 30677032817532127501956749)
                ·
                  refine ⟨11503887306574547813233781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30677032817532127501956749 11503887306574547813233781)
                  ·
                    refine ⟨1078489434991363857490667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11503887306574547813233781 1078489434991363857490667)
                    ·
                      rfl

theorem cell22_3150526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_3150526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150526 prefixEnd_3150526 := by exact prefixLift 3150526
  have htrace : WordTrace (prefixWord ++ tailWord_3150526) baseStart_3150526 baseEnd_3150526 := by
    simpa [prefixWord, tailWord_3150526, baseEnd_3150526] using wordTrace_append hprefix tailTrace_3150526
  have hstable : (prefixWord ++ tailWord_3150526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150526).length < 2 ^ (prefixWord ++ tailWord_3150526).sum := by decide
  have hdescent : baseEnd_3150526 < baseStart_3150526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150528 : List Nat := [2, 1, 1, 2, 4, 2, 3, 3, 4]
def baseStart_3150528 : Nat := 118140960795 + 3150528 * 2 ^ 59
def prefixEnd_3150528 : Nat := 4983230072969 + 3 ^ 40 * 3150528 * 2
def baseEnd_3150528 : Nat := 359496706544078839646887

theorem tailTrace_3150528 : CollatzResearch.WordTrace tailWord_3150528 prefixEnd_3150528 359496706544078839646887 := by
  unfold tailWord_3150528
  simp only [CollatzResearch.WordTrace]
  refine ⟨57454598165091299094890119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76606130886788398793186825 57454598165091299094890119)
  ·
    refine ⟨86181897247636948642335179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57454598165091299094890119 86181897247636948642335179)
    ·
      refine ⟨129272845871455422963502769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86181897247636948642335179 129272845871455422963502769)
      ·
        refine ⟨96954634403591567222627077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129272845871455422963502769 96954634403591567222627077)
        ·
          refine ⟨18178993950673418854242577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96954634403591567222627077 18178993950673418854242577)
          ·
            refine ⟨13634245463005064140681933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18178993950673418854242577 13634245463005064140681933)
            ·
              refine ⟨5112842048626899052755725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13634245463005064140681933 5112842048626899052755725)
              ·
                refine ⟨1917315768235087144783397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5112842048626899052755725 1917315768235087144783397)
                ·
                  refine ⟨359496706544078839646887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1917315768235087144783397 359496706544078839646887)
                  ·
                    rfl

theorem cell22_3150528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3, 4].length) (baseStart_3150528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150528 prefixEnd_3150528 := by exact prefixLift 3150528
  have htrace : WordTrace (prefixWord ++ tailWord_3150528) baseStart_3150528 baseEnd_3150528 := by
    simpa [prefixWord, tailWord_3150528, baseEnd_3150528] using wordTrace_append hprefix tailTrace_3150528
  have hstable : (prefixWord ++ tailWord_3150528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150528).length < 2 ^ (prefixWord ++ tailWord_3150528).sum := by decide
  have hdescent : baseEnd_3150528 < baseStart_3150528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150571 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 5, 3]
def baseStart_3150571 : Nat := 118140960795 + 3150571 * 2 ^ 59
def prefixEnd_3150571 : Nat := 4983230072969 + 3 ^ 40 * 3150571 * 2
def baseEnd_3150571 : Nat := 1078504839410998740115529

theorem tailTrace_3150571 : CollatzResearch.WordTrace tailWord_3150571 prefixEnd_3150571 1078504839410998740115529 := by
  unfold tailWord_3150571
  simp only [CollatzResearch.WordTrace]
  refine ⟨114910764669026816533595567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76607176446017877689063711 114910764669026816533595567)
  ·
    refine ⟨172366147003540224800393351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114910764669026816533595567 172366147003540224800393351)
    ·
      refine ⟨258549220505310337200590027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172366147003540224800393351 258549220505310337200590027)
      ·
        refine ⟨387823830757965505800885041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258549220505310337200590027 387823830757965505800885041)
        ·
          refine ⟨290867873068474129350663781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387823830757965505800885041 290867873068474129350663781)
          ·
            refine ⟨54537726200338899253249459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290867873068474129350663781 54537726200338899253249459)
            ·
              refine ⟨81806589300508348879874189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54537726200338899253249459 81806589300508348879874189)
              ·
                refine ⟨30677470987690630829952821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81806589300508348879874189 30677470987690630829952821)
                ·
                  refine ⟨2876012905095996640308077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30677470987690630829952821 2876012905095996640308077)
                  ·
                    refine ⟨1078504839410998740115529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2876012905095996640308077 1078504839410998740115529)
                    ·
                      rfl

theorem cell22_3150571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 3].length) (baseStart_3150571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150571 prefixEnd_3150571 := by exact prefixLift 3150571
  have htrace : WordTrace (prefixWord ++ tailWord_3150571) baseStart_3150571 baseEnd_3150571 := by
    simpa [prefixWord, tailWord_3150571, baseEnd_3150571] using wordTrace_append hprefix tailTrace_3150571
  have hstable : (prefixWord ++ tailWord_3150571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150571).length < 2 ^ (prefixWord ++ tailWord_3150571).sum := by decide
  have hdescent : baseEnd_3150571 < baseStart_3150571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150601 : List Nat := [1, 2, 1, 1, 3, 2, 3, 4, 5]
def baseStart_3150601 : Nat := 118140960795 + 3150601 * 2 ^ 59
def prefixEnd_3150601 : Nat := 4983230072969 + 3 ^ 40 * 3150601 * 2
def baseEnd_3150601 : Nat := 359505036341362887288479

theorem tailTrace_3150601 : CollatzResearch.WordTrace tailWord_3150601 prefixEnd_3150601 359505036341362887288479 := by
  unfold tailWord_3150601
  simp only [CollatzResearch.WordTrace]
  refine ⟨114911858858918131657187657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76607905905945421104791771 114911858858918131657187657)
  ·
    refine ⟨86183894144188598742890743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114911858858918131657187657 86183894144188598742890743)
    ·
      refine ⟨129275841216282898114336115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86183894144188598742890743 129275841216282898114336115)
      ·
        refine ⟨193913761824424347171504173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129275841216282898114336115 193913761824424347171504173)
        ·
          refine ⟨72717660684159130189314065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193913761824424347171504173 72717660684159130189314065)
          ·
            refine ⟨54538245513119347641985549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72717660684159130189314065 54538245513119347641985549)
            ·
              refine ⟨20451842067419755365744581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54538245513119347641985549 20451842067419755365744581)
              ·
                refine ⟨3834720387641204131077109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20451842067419755365744581 3834720387641204131077109)
                ·
                  refine ⟨359505036341362887288479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3834720387641204131077109 359505036341362887288479)
                  ·
                    rfl

theorem cell22_3150601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 5].length) (baseStart_3150601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150601 prefixEnd_3150601 := by exact prefixLift 3150601
  have htrace : WordTrace (prefixWord ++ tailWord_3150601) baseStart_3150601 baseEnd_3150601 := by
    simpa [prefixWord, tailWord_3150601, baseEnd_3150601] using wordTrace_append hprefix tailTrace_3150601
  have hstable : (prefixWord ++ tailWord_3150601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150601).length < 2 ^ (prefixWord ++ tailWord_3150601).sum := by decide
  have hdescent : baseEnd_3150601 < baseStart_3150601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150648 : List Nat := [2, 1, 2, 1, 3, 2, 3, 3, 1, 4]
def baseStart_3150648 : Nat := 118140960795 + 3150648 * 2 ^ 59
def prefixEnd_3150648 : Nat := 4983230072969 + 3 ^ 40 * 3150648 * 2
def baseEnd_3150648 : Nat := 1078531198084596205940293

theorem tailTrace_3150648 : CollatzResearch.WordTrace tailWord_3150648 prefixEnd_3150648 1078531198084596205940293 := by
  unfold tailWord_3150648
  simp only [CollatzResearch.WordTrace]
  refine ⟨57456786544873929342074299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76609048726498572456099065 57456786544873929342074299)
  ·
    refine ⟨86185179817310894013111449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57456786544873929342074299 86185179817310894013111449)
    ·
      refine ⟨64638884862983170509833587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86185179817310894013111449 64638884862983170509833587)
      ·
        refine ⟨96958327294474755764750381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64638884862983170509833587 96958327294474755764750381)
        ·
          refine ⟨36359372735428033411781393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96958327294474755764750381 36359372735428033411781393)
          ·
            refine ⟨27269529551571025058836045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36359372735428033411781393 27269529551571025058836045)
            ·
              refine ⟨10226073581839134397063517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27269529551571025058836045 10226073581839134397063517)
              ·
                refine ⟨3834777593189675398898819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10226073581839134397063517 3834777593189675398898819)
                ·
                  refine ⟨5752166389784513098348229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834777593189675398898819 5752166389784513098348229)
                  ·
                    refine ⟨1078531198084596205940293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5752166389784513098348229 1078531198084596205940293)
                    ·
                      rfl

theorem cell22_3150648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_3150648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150648 prefixEnd_3150648 := by exact prefixLift 3150648
  have htrace : WordTrace (prefixWord ++ tailWord_3150648) baseStart_3150648 baseEnd_3150648 := by
    simpa [prefixWord, tailWord_3150648, baseEnd_3150648] using wordTrace_append hprefix tailTrace_3150648
  have hstable : (prefixWord ++ tailWord_3150648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150648).length < 2 ^ (prefixWord ++ tailWord_3150648).sum := by decide
  have hdescent : baseEnd_3150648 < baseStart_3150648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150710 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_3150710 : Nat := 118140960795 + 3150710 * 2 ^ 59
def prefixEnd_3150710 : Nat := 4983230072969 + 3 ^ 40 * 3150710 * 2
def baseEnd_3150710 : Nat := 1078552421951648710890103

theorem tailTrace_3150710 : CollatzResearch.WordTrace tailWord_3150710 prefixEnd_3150710 1078552421951648710890103 := by
  unfold tailWord_3150710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7182239650970202704556599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76610556277015495515270389 7182239650970202704556599)
  ·
    refine ⟨10773359476455304056834899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7182239650970202704556599 10773359476455304056834899)
    ·
      refine ⟨16160039214682956085252349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10773359476455304056834899 16160039214682956085252349)
      ·
        refine ⟨6060014705506108531969631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16160039214682956085252349 6060014705506108531969631)
        ·
          refine ⟨9090022058259162797954447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6060014705506108531969631 9090022058259162797954447)
          ·
            refine ⟨13635033087388744196931671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9090022058259162797954447 13635033087388744196931671)
            ·
              refine ⟨20452549631083116295397507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13635033087388744196931671 20452549631083116295397507)
              ·
                refine ⟨30678824446624674443096261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20452549631083116295397507 30678824446624674443096261)
                ·
                  refine ⟨5752279583742126458080549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30678824446624674443096261 5752279583742126458080549)
                  ·
                    refine ⟨1078552421951648710890103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5752279583742126458080549 1078552421951648710890103)
                    ·
                      rfl

theorem cell22_3150710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_3150710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150710 prefixEnd_3150710 := by exact prefixLift 3150710
  have htrace : WordTrace (prefixWord ++ tailWord_3150710) baseStart_3150710 baseEnd_3150710 := by
    simpa [prefixWord, tailWord_3150710, baseEnd_3150710] using wordTrace_append hprefix tailTrace_3150710
  have hstable : (prefixWord ++ tailWord_3150710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150710).length < 2 ^ (prefixWord ++ tailWord_3150710).sum := by decide
  have hdescent : baseEnd_3150710 < baseStart_3150710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150740 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_3150740 : Nat := 118140960795 + 3150740 * 2 ^ 59
def prefixEnd_3150740 : Nat := 4983230072969 + 3 ^ 40 * 3150740 * 2
def baseEnd_3150740 : Nat := 1078562691564738632640011

theorem tailTrace_3150740 : CollatzResearch.WordTrace tailWord_3150740 prefixEnd_3150740 1078562691564738632640011 := by
  unfold tailWord_3150740
  simp only [CollatzResearch.WordTrace]
  refine ⟨57458464302707279198248837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76611285736943038930998449 57458464302707279198248837)
  ·
    refine ⟨10773462056757614849671657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57458464302707279198248837 10773462056757614849671657)
    ·
      refine ⟨8080096542568211137253743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10773462056757614849671657 8080096542568211137253743)
      ·
        refine ⟨12120144813852316705880615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8080096542568211137253743 12120144813852316705880615)
        ·
          refine ⟨18180217220778475058820923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12120144813852316705880615 18180217220778475058820923)
          ·
            refine ⟨27270325831167712588231385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18180217220778475058820923 27270325831167712588231385)
            ·
              refine ⟨20452744373375784441173539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27270325831167712588231385 20452744373375784441173539)
              ·
                refine ⟨30679116560063676661760309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20452744373375784441173539 30679116560063676661760309)
                ·
                  refine ⟨2876167177505969687040029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30679116560063676661760309 2876167177505969687040029)
                  ·
                    refine ⟨1078562691564738632640011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2876167177505969687040029 1078562691564738632640011)
                    ·
                      rfl

theorem cell22_3150740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_3150740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150740 prefixEnd_3150740 := by exact prefixLift 3150740
  have htrace : WordTrace (prefixWord ++ tailWord_3150740) baseStart_3150740 baseEnd_3150740 := by
    simpa [prefixWord, tailWord_3150740, baseEnd_3150740] using wordTrace_append hprefix tailTrace_3150740
  have hstable : (prefixWord ++ tailWord_3150740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150740).length < 2 ^ (prefixWord ++ tailWord_3150740).sum := by decide
  have hdescent : baseEnd_3150740 < baseStart_3150740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150742 : List Nat := [5, 3, 1, 1, 1, 1, 2, 8]
def baseStart_3150742 : Nat := 118140960795 + 3150742 * 2 ^ 59
def prefixEnd_3150742 : Nat := 4983230072969 + 3 ^ 40 * 3150742 * 2
def baseEnd_3150742 : Nat := 119840375133956810454445

theorem tailTrace_3150742 : CollatzResearch.WordTrace tailWord_3150742 prefixEnd_3150742 119840375133956810454445 := by
  unfold tailWord_3150742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7182312596962957046129405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76611334367604875158713653 7182312596962957046129405)
  ·
    refine ⟨2693367223861108892298527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7182312596962957046129405 2693367223861108892298527)
    ·
      refine ⟨4040050835791663338447791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2693367223861108892298527 4040050835791663338447791)
      ·
        refine ⟨6060076253687495007671687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4040050835791663338447791 6060076253687495007671687)
        ·
          refine ⟨9090114380531242511507531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6060076253687495007671687 9090114380531242511507531)
          ·
            refine ⟨13635171570796863767261297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9090114380531242511507531 13635171570796863767261297)
            ·
              refine ⟨10226378678097647825445973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13635171570796863767261297 10226378678097647825445973)
              ·
                refine ⟨119840375133956810454445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10226378678097647825445973 119840375133956810454445)
                ·
                  rfl

theorem cell22_3150742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_3150742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150742 prefixEnd_3150742 := by exact prefixLift 3150742
  have htrace : WordTrace (prefixWord ++ tailWord_3150742) baseStart_3150742 baseEnd_3150742 := by
    simpa [prefixWord, tailWord_3150742, baseEnd_3150742] using wordTrace_append hprefix tailTrace_3150742
  have hstable : (prefixWord ++ tailWord_3150742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150742).length < 2 ^ (prefixWord ++ tailWord_3150742).sum := by decide
  have hdescent : baseEnd_3150742 < baseStart_3150742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150798 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_3150798 : Nat := 118140960795 + 3150798 * 2 ^ 59
def prefixEnd_3150798 : Nat := 4983230072969 + 3 ^ 40 * 3150798 * 2
def baseEnd_3150798 : Nat := 359527515383348604896611

theorem tailTrace_3150798 : CollatzResearch.WordTrace tailWord_3150798 prefixEnd_3150798 359527515383348604896611 := by
  unfold tailWord_3150798
  simp only [CollatzResearch.WordTrace]
  refine ⟨14364880504900554287763631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76612696026136289534739365 14364880504900554287763631)
  ·
    refine ⟨21547320757350831431645447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14364880504900554287763631 21547320757350831431645447)
    ·
      refine ⟨32320981136026247147468171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21547320757350831431645447 32320981136026247147468171)
      ·
        refine ⟨48481471704039370721202257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32320981136026247147468171 48481471704039370721202257)
        ·
          refine ⟨36361103778029528040901693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48481471704039370721202257 36361103778029528040901693)
          ·
            refine ⟨13635413916761073015338135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36361103778029528040901693 13635413916761073015338135)
            ·
              refine ⟨20453120875141609523007203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13635413916761073015338135 20453120875141609523007203)
              ·
                refine ⟨30679681312712414284510805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20453120875141609523007203 30679681312712414284510805)
                ·
                  refine ⟨359527515383348604896611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30679681312712414284510805 359527515383348604896611)
                  ·
                    rfl

theorem cell22_3150798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_3150798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150798 prefixEnd_3150798 := by exact prefixLift 3150798
  have htrace : WordTrace (prefixWord ++ tailWord_3150798) baseStart_3150798 baseEnd_3150798 := by
    simpa [prefixWord, tailWord_3150798, baseEnd_3150798] using wordTrace_append hprefix tailTrace_3150798
  have hstable : (prefixWord ++ tailWord_3150798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150798).length < 2 ^ (prefixWord ++ tailWord_3150798).sum := by decide
  have hdescent : baseEnd_3150798 < baseStart_3150798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150860 : List Nat := [2, 2, 1, 2, 3, 2, 4, 6]
def baseStart_3150860 : Nat := 118140960795 + 3150860 * 2 ^ 59
def prefixEnd_3150860 : Nat := 4983230072969 + 3 ^ 40 * 3150860 * 2
def baseEnd_3150860 : Nat := 119844863335233146626627

theorem tailTrace_3150860 : CollatzResearch.WordTrace tailWord_3150860 prefixEnd_3150860 119844863335233146626627 := by
  unfold tailWord_3150860
  simp only [CollatzResearch.WordTrace]
  refine ⟨57460652682489909445433017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76614203576653212593910689 57460652682489909445433017)
  ·
    refine ⟨43095489511867432084074763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57460652682489909445433017 43095489511867432084074763)
    ·
      refine ⟨64643234267801148126112145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43095489511867432084074763 64643234267801148126112145)
      ·
        refine ⟨48482425700850861094584109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64643234267801148126112145 48482425700850861094584109)
        ·
          refine ⟨18180909637819072910469041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48482425700850861094584109 18180909637819072910469041)
          ·
            refine ⟨13635682228364304682851781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18180909637819072910469041 13635682228364304682851781)
            ·
              refine ⟨2556690417818307128034709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13635682228364304682851781 2556690417818307128034709)
              ·
                refine ⟨119844863335233146626627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2556690417818307128034709 119844863335233146626627)
                ·
                  rfl

theorem cell22_3150860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 6].length) (baseStart_3150860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150860 prefixEnd_3150860 := by exact prefixLift 3150860
  have htrace : WordTrace (prefixWord ++ tailWord_3150860) baseStart_3150860 baseEnd_3150860 := by
    simpa [prefixWord, tailWord_3150860, baseEnd_3150860] using wordTrace_append hprefix tailTrace_3150860
  have hstable : (prefixWord ++ tailWord_3150860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150860).length < 2 ^ (prefixWord ++ tailWord_3150860).sum := by decide
  have hdescent : baseEnd_3150860 < baseStart_3150860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150877 : List Nat := [1, 4, 2, 2, 4, 1, 8]
def baseStart_3150877 : Nat := 118140960795 + 3150877 * 2 ^ 59
def prefixEnd_3150877 : Nat := 4983230072969 + 3 ^ 40 * 3150877 * 2
def baseEnd_3150877 : Nat := 39948503313500590443133

theorem tailTrace_3150877 : CollatzResearch.WordTrace tailWord_3150877 prefixEnd_3150877 39948503313500590443133 := by
  unfold tailWord_3150877
  simp only [CollatzResearch.WordTrace]
  refine ⟨114921925405918230794234885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76614616937278820529489923 114921925405918230794234885)
  ·
    refine ⟨21547861013609668273919041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114921925405918230794234885 21547861013609668273919041)
    ·
      refine ⟨16160895760207251205439281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21547861013609668273919041 16160895760207251205439281)
      ·
        refine ⟨12120671820155438404079461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16160895760207251205439281 12120671820155438404079461)
        ·
          refine ⟨2272625966279144700764899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12120671820155438404079461 2272625966279144700764899)
          ·
            refine ⟨3408938949418717051147349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272625966279144700764899 3408938949418717051147349)
            ·
              refine ⟨39948503313500590443133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3408938949418717051147349 39948503313500590443133)
              ·
                rfl

theorem cell22_3150877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 8].length) (baseStart_3150877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150877 prefixEnd_3150877 := by exact prefixLift 3150877
  have htrace : WordTrace (prefixWord ++ tailWord_3150877) baseStart_3150877 baseEnd_3150877 := by
    simpa [prefixWord, tailWord_3150877, baseEnd_3150877] using wordTrace_append hprefix tailTrace_3150877
  have hstable : (prefixWord ++ tailWord_3150877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150877).length < 2 ^ (prefixWord ++ tailWord_3150877).sum := by decide
  have hdescent : baseEnd_3150877 < baseStart_3150877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150903 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 1, 7]
def baseStart_3150903 : Nat := 118140960795 + 3150903 * 2 ^ 59
def prefixEnd_3150903 : Nat := 4983230072969 + 3 ^ 40 * 3150903 * 2
def baseEnd_3150903 : Nat := 1078618489795860540814511

theorem tailTrace_3150903 : CollatzResearch.WordTrace tailWord_3150903 prefixEnd_3150903 1078618489795860540814511 := by
  unfold tailWord_3150903
  simp only [CollatzResearch.WordTrace]
  refine ⟨114922873703824037234681363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76615249135882691489787575 114922873703824037234681363)
  ·
    refine ⟨172384310555736055852022045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114922873703824037234681363 172384310555736055852022045)
    ·
      refine ⟨64644116458401020944508267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172384310555736055852022045 64644116458401020944508267)
      ·
        refine ⟨96966174687601531416762401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64644116458401020944508267 96966174687601531416762401)
        ·
          refine ⟨72724631015701148562571801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96966174687601531416762401 72724631015701148562571801)
          ·
            refine ⟨54543473261775861421928851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72724631015701148562571801 54543473261775861421928851)
            ·
              refine ⟨81815209892663792132893277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54543473261775861421928851 81815209892663792132893277)
              ·
                refine ⟨30680703709748922049834979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81815209892663792132893277 30680703709748922049834979)
                ·
                  refine ⟨46021055564623383074752469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30680703709748922049834979 46021055564623383074752469)
                  ·
                    refine ⟨1078618489795860540814511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46021055564623383074752469 1078618489795860540814511)
                    ·
                      rfl

theorem cell22_3150903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_3150903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150903 prefixEnd_3150903 := by exact prefixLift 3150903
  have htrace : WordTrace (prefixWord ++ tailWord_3150903) baseStart_3150903 baseEnd_3150903 := by
    simpa [prefixWord, tailWord_3150903, baseEnd_3150903] using wordTrace_append hprefix tailTrace_3150903
  have hstable : (prefixWord ++ tailWord_3150903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150903).length < 2 ^ (prefixWord ++ tailWord_3150903).sum := by decide
  have hdescent : baseEnd_3150903 < baseStart_3150903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3150999 : List Nat := [1, 1, 3, 3, 3, 1, 3, 2, 2, 3]
def baseStart_3150999 : Nat := 118140960795 + 3150999 * 2 ^ 59
def prefixEnd_3150999 : Nat := 4983230072969 + 3 ^ 40 * 3150999 * 2
def baseEnd_3150999 : Nat := 1078651352557748290414217

theorem tailTrace_3150999 : CollatzResearch.WordTrace tailWord_3150999 prefixEnd_3150999 1078651352557748290414217 := by
  unfold tailWord_3150999
  simp only [CollatzResearch.WordTrace]
  refine ⟨114926375111476245630176051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76617583407650830420117367 114926375111476245630176051)
  ·
    refine ⟨172389562667214368445264077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114926375111476245630176051 172389562667214368445264077)
    ·
      refine ⟨64646086000205388166974029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172389562667214368445264077 64646086000205388166974029)
      ·
        refine ⟨24242282250077020562615261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64646086000205388166974029 24242282250077020562615261)
        ·
          refine ⟨9090855843778882710980723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24242282250077020562615261 9090855843778882710980723)
          ·
            refine ⟨13636283765668324066471085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9090855843778882710980723 13636283765668324066471085)
            ·
              refine ⟨5113606412125621524926657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13636283765668324066471085 5113606412125621524926657)
              ·
                refine ⟨3835204809094216143694993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5113606412125621524926657 3835204809094216143694993)
                ·
                  refine ⟨2876403606820662107771245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3835204809094216143694993 2876403606820662107771245)
                  ·
                    refine ⟨1078651352557748290414217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2876403606820662107771245 1078651352557748290414217)
                    ·
                      rfl

theorem cell22_3150999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_3150999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3150999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3150999 prefixEnd_3150999 := by exact prefixLift 3150999
  have htrace : WordTrace (prefixWord ++ tailWord_3150999) baseStart_3150999 baseEnd_3150999 := by
    simpa [prefixWord, tailWord_3150999, baseEnd_3150999] using wordTrace_append hprefix tailTrace_3150999
  have hstable : (prefixWord ++ tailWord_3150999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3150999).length < 2 ^ (prefixWord ++ tailWord_3150999).sum := by decide
  have hdescent : baseEnd_3150999 < baseStart_3150999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3150999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151027 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 3, 3]
def baseStart_3151027 : Nat := 118140960795 + 3151027 * 2 ^ 59
def prefixEnd_3151027 : Nat := 4983230072969 + 3 ^ 40 * 3151027 * 2
def baseEnd_3151027 : Nat := 1078660937529965550714131

theorem tailTrace_3151027 : CollatzResearch.WordTrace tailWord_3151027 prefixEnd_3151027 1078660937529965550714131 := by
  unfold tailWord_3151027
  simp only [CollatzResearch.WordTrace]
  refine ⟨114927396355374806412195335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76618264236916537608130223 114927396355374806412195335)
  ·
    refine ⟨172391094533062209618293003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114927396355374806412195335 172391094533062209618293003)
    ·
      refine ⟨258586641799593314427439505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172391094533062209618293003 258586641799593314427439505)
      ·
        refine ⟨193939981349694985820579629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258586641799593314427439505 193939981349694985820579629)
        ·
          refine ⟨72727493006135619682717361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193939981349694985820579629 72727493006135619682717361)
          ·
            refine ⟨54545619754601714762038021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72727493006135619682717361 54545619754601714762038021)
            ·
              refine ⟨10227303703987821517882129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54545619754601714762038021 10227303703987821517882129)
              ·
                refine ⟨7670477777990866138411597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10227303703987821517882129 7670477777990866138411597)
                ·
                  refine ⟨2876429166746574801904349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7670477777990866138411597 2876429166746574801904349)
                  ·
                    refine ⟨1078660937529965550714131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2876429166746574801904349 1078660937529965550714131)
                    ·
                      rfl

theorem cell22_3151027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 3, 3].length) (baseStart_3151027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151027 prefixEnd_3151027 := by exact prefixLift 3151027
  have htrace : WordTrace (prefixWord ++ tailWord_3151027) baseStart_3151027 baseEnd_3151027 := by
    simpa [prefixWord, tailWord_3151027, baseEnd_3151027] using wordTrace_append hprefix tailTrace_3151027
  have hstable : (prefixWord ++ tailWord_3151027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151027).length < 2 ^ (prefixWord ++ tailWord_3151027).sum := by decide
  have hdescent : baseEnd_3151027 < baseStart_3151027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151055 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 2, 5]
def baseStart_3151055 : Nat := 118140960795 + 3151055 * 2 ^ 59
def prefixEnd_3151055 : Nat := 4983230072969 + 3 ^ 40 * 3151055 * 2
def baseEnd_3151055 : Nat := 1078670522502182811014045

theorem tailTrace_3151055 : CollatzResearch.WordTrace tailWord_3151055 prefixEnd_3151055 1078670522502182811014045 := by
  unfold tailWord_3151055
  simp only [CollatzResearch.WordTrace]
  refine ⟨114928417599273367194214619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76618945066182244796143079 114928417599273367194214619)
  ·
    refine ⟨172392626398910050791321929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114928417599273367194214619 172392626398910050791321929)
    ·
      refine ⟨129294469799182538093491447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172392626398910050791321929 129294469799182538093491447)
      ·
        refine ⟨193941704698773807140237171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129294469799182538093491447 193941704698773807140237171)
        ·
          refine ⟨290912557048160710710355757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193941704698773807140237171 290912557048160710710355757)
          ·
            refine ⟨109092208893060266516383409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 290912557048160710710355757 109092208893060266516383409)
            ·
              refine ⟨81819156669795199887287557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109092208893060266516383409 81819156669795199887287557)
              ·
                refine ⟨15341091875586599978866417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81819156669795199887287557 15341091875586599978866417)
                ·
                  refine ⟨11505818906689949984149813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15341091875586599978866417 11505818906689949984149813)
                  ·
                    refine ⟨1078670522502182811014045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11505818906689949984149813 1078670522502182811014045)
                    ·
                      rfl

theorem cell22_3151055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_3151055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151055 prefixEnd_3151055 := by exact prefixLift 3151055
  have htrace : WordTrace (prefixWord ++ tailWord_3151055) baseStart_3151055 baseEnd_3151055 := by
    simpa [prefixWord, tailWord_3151055, baseEnd_3151055] using wordTrace_append hprefix tailTrace_3151055
  have hstable : (prefixWord ++ tailWord_3151055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151055).length < 2 ^ (prefixWord ++ tailWord_3151055).sum := by decide
  have hdescent : baseEnd_3151055 < baseStart_3151055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151061 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 3, 3]
def baseStart_3151061 : Nat := 118140960795 + 3151061 * 2 ^ 59
def prefixEnd_3151061 : Nat := 4983230072969 + 3 ^ 40 * 3151061 * 2
def baseEnd_3151061 : Nat := 1078672576424800795364027

theorem tailTrace_3151061 : CollatzResearch.WordTrace tailWord_3151061 prefixEnd_3151061 1078672576424800795364027 := by
  unfold tailWord_3151061
  simp only [CollatzResearch.WordTrace]
  refine ⟨114928636437251630218933037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76619090958167753479288691 114928636437251630218933037)
  ·
    refine ⟨43098238663969361332099889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114928636437251630218933037 43098238663969361332099889)
    ·
      refine ⟨32323678997977020999074917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43098238663969361332099889 32323678997977020999074917)
      ·
        refine ⟨6060689812120691437326547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32323678997977020999074917 6060689812120691437326547)
        ·
          refine ⟨9091034718181037155989821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6060689812120691437326547 9091034718181037155989821)
          ·
            refine ⟨3409138019317888933496183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9091034718181037155989821 3409138019317888933496183)
            ·
              refine ⟨5113707028976833400244275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3409138019317888933496183 5113707028976833400244275)
              ·
                refine ⟨7670560543465250100366413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5113707028976833400244275 7670560543465250100366413)
                ·
                  refine ⟨2876460203799468787637405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7670560543465250100366413 2876460203799468787637405)
                  ·
                    refine ⟨1078672576424800795364027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2876460203799468787637405 1078672576424800795364027)
                    ·
                      rfl

theorem cell22_3151061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_3151061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151061 prefixEnd_3151061 := by exact prefixLift 3151061
  have htrace : WordTrace (prefixWord ++ tailWord_3151061) baseStart_3151061 baseEnd_3151061 := by
    simpa [prefixWord, tailWord_3151061, baseEnd_3151061] using wordTrace_append hprefix tailTrace_3151061
  have hstable : (prefixWord ++ tailWord_3151061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151061).length < 2 ^ (prefixWord ++ tailWord_3151061).sum := by decide
  have hdescent : baseEnd_3151061 < baseStart_3151061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151132 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_3151132 : Nat := 118140960795 + 3151132 * 2 ^ 59
def prefixEnd_3151132 : Nat := 4983230072969 + 3 ^ 40 * 3151132 * 2
def baseEnd_3151132 : Nat := 1078696881175780276838809

theorem tailTrace_3151132 : CollatzResearch.WordTrace tailWord_3151132 prefixEnd_3151132 1078696881175780276838809 := by
  unfold tailWord_3151132
  simp only [CollatzResearch.WordTrace]
  refine ⟨57465613009997204672383825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76620817346662939563178433 57465613009997204672383825)
  ·
    refine ⟨43099209757497903504287869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57465613009997204672383825 43099209757497903504287869)
    ·
      refine ⟨16162203659061713814107951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43099209757497903504287869 16162203659061713814107951)
      ·
        refine ⟨24243305488592570721161927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16162203659061713814107951 24243305488592570721161927)
        ·
          refine ⟨36364958232888856081742891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24243305488592570721161927 36364958232888856081742891)
          ·
            refine ⟨54547437349333284122614337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36364958232888856081742891 54547437349333284122614337)
            ·
              refine ⟨40910578011999963091960753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54547437349333284122614337 40910578011999963091960753)
              ·
                refine ⟨30682933508999972318970565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40910578011999963091960753 30682933508999972318970565)
                ·
                  refine ⟨5753050032937494809806981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30682933508999972318970565 5753050032937494809806981)
                  ·
                    refine ⟨1078696881175780276838809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5753050032937494809806981 1078696881175780276838809)
                    ·
                      rfl

theorem cell22_3151132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_3151132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151132 prefixEnd_3151132 := by exact prefixLift 3151132
  have htrace : WordTrace (prefixWord ++ tailWord_3151132) baseStart_3151132 baseEnd_3151132 := by
    simpa [prefixWord, tailWord_3151132, baseEnd_3151132] using wordTrace_append hprefix tailTrace_3151132
  have hstable : (prefixWord ++ tailWord_3151132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151132).length < 2 ^ (prefixWord ++ tailWord_3151132).sum := by decide
  have hdescent : baseEnd_3151132 < baseStart_3151132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151213 : List Nat := [1, 5, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_3151213 : Nat := 118140960795 + 3151213 * 2 ^ 59
def prefixEnd_3151213 : Nat := 4983230072969 + 3 ^ 40 * 3151213 * 2
def baseEnd_3151213 : Nat := 1078724609131123065563561

theorem tailTrace_3151213 : CollatzResearch.WordTrace tailWord_3151213 prefixEnd_3151213 1078724609131123065563561 := by
  unfold tailWord_3151213
  simp only [CollatzResearch.WordTrace]
  refine ⟨114934180332700960178466293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76622786888467306785644195 114934180332700960178466293)
  ·
    refine ⟨10775079406190715016731215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114934180332700960178466293 10775079406190715016731215)
    ·
      refine ⟨16162619109286072525096823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10775079406190715016731215 16162619109286072525096823)
      ·
        refine ⟨24243928663929108787645235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16162619109286072525096823 24243928663929108787645235)
        ·
          refine ⟨36365892995893663181467853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24243928663929108787645235 36365892995893663181467853)
          ·
            refine ⟨13637209873460123693050445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36365892995893663181467853 13637209873460123693050445)
            ·
              refine ⟨5113953702547546384893917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13637209873460123693050445 5113953702547546384893917)
              ·
                refine ⟨1917732638455329894335219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5113953702547546384893917 1917732638455329894335219)
                ·
                  refine ⟨2876598957682994841502829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917732638455329894335219 2876598957682994841502829)
                  ·
                    refine ⟨1078724609131123065563561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2876598957682994841502829 1078724609131123065563561)
                    ·
                      rfl

theorem cell22_3151213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_3151213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151213 prefixEnd_3151213 := by exact prefixLift 3151213
  have htrace : WordTrace (prefixWord ++ tailWord_3151213) baseStart_3151213 baseEnd_3151213 := by
    simpa [prefixWord, tailWord_3151213, baseEnd_3151213] using wordTrace_append hprefix tailTrace_3151213
  have hstable : (prefixWord ++ tailWord_3151213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151213).length < 2 ^ (prefixWord ++ tailWord_3151213).sum := by decide
  have hdescent : baseEnd_3151213 < baseStart_3151213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151256 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 3, 4]
def baseStart_3151256 : Nat := 118140960795 + 3151256 * 2 ^ 59
def prefixEnd_3151256 : Nat := 4983230072969 + 3 ^ 40 * 3151256 * 2
def baseEnd_3151256 : Nat := 1078739328909885286738429

theorem tailTrace_3151256 : CollatzResearch.WordTrace tailWord_3151256 prefixEnd_3151256 1078739328909885286738429 := by
  unfold tailWord_3151256
  simp only [CollatzResearch.WordTrace]
  refine ⟨57467874335772589261140811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76623832447696785681521081 57467874335772589261140811)
  ·
    refine ⟨86201811503658883891711217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57467874335772589261140811 86201811503658883891711217)
    ·
      refine ⟨64651358627744162918783413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86201811503658883891711217 64651358627744162918783413)
      ·
        refine ⟨6061064871351015273635945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64651358627744162918783413 6061064871351015273635945)
        ·
          refine ⟨4545798653513261455226959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6061064871351015273635945 4545798653513261455226959)
          ·
            refine ⟨6818697980269892182840439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4545798653513261455226959 6818697980269892182840439)
            ·
              refine ⟨10228046970404838274260659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6818697980269892182840439 10228046970404838274260659)
              ·
                refine ⟨15342070455607257411390989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10228046970404838274260659 15342070455607257411390989)
                ·
                  refine ⟨5753276420852721529271621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15342070455607257411390989 5753276420852721529271621)
                  ·
                    refine ⟨1078739328909885286738429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5753276420852721529271621 1078739328909885286738429)
                    ·
                      rfl

theorem cell22_3151256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_3151256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151256 prefixEnd_3151256 := by exact prefixLift 3151256
  have htrace : WordTrace (prefixWord ++ tailWord_3151256) baseStart_3151256 baseEnd_3151256 := by
    simpa [prefixWord, tailWord_3151256, baseEnd_3151256] using wordTrace_append hprefix tailTrace_3151256
  have hstable : (prefixWord ++ tailWord_3151256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151256).length < 2 ^ (prefixWord ++ tailWord_3151256).sum := by decide
  have hdescent : baseEnd_3151256 < baseStart_3151256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151269 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 4, 3]
def baseStart_3151269 : Nat := 118140960795 + 3151269 * 2 ^ 59
def prefixEnd_3151269 : Nat := 4983230072969 + 3 ^ 40 * 3151269 * 2
def baseEnd_3151269 : Nat := 1078743779075557586163389

theorem tailTrace_3151269 : CollatzResearch.WordTrace tailWord_3151269 prefixEnd_3151269 1078743779075557586163389 := by
  unfold tailWord_3151269
  simp only [CollatzResearch.WordTrace]
  refine ⟨114936222820498081742504861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76624148546998721161669907 114936222820498081742504861)
  ·
    refine ⟨43101083557686780653439323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114936222820498081742504861 43101083557686780653439323)
    ·
      refine ⟨64651625336530170980158985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43101083557686780653439323 64651625336530170980158985)
      ·
        refine ⟨48488719002397628235119239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64651625336530170980158985 48488719002397628235119239)
        ·
          refine ⟨72733078503596442352678859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48488719002397628235119239 72733078503596442352678859)
          ·
            refine ⟨109099617755394663529018289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72733078503596442352678859 109099617755394663529018289)
            ·
              refine ⟨81824713316545997646763717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109099617755394663529018289 81824713316545997646763717)
              ·
                refine ⟨15342133746852374558768197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81824713316545997646763717 15342133746852374558768197)
                ·
                  refine ⟨2876650077534820229769037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15342133746852374558768197 2876650077534820229769037)
                  ·
                    refine ⟨1078743779075557586163389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2876650077534820229769037 1078743779075557586163389)
                    ·
                      rfl

theorem cell22_3151269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_3151269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151269 prefixEnd_3151269 := by exact prefixLift 3151269
  have htrace : WordTrace (prefixWord ++ tailWord_3151269) baseStart_3151269 baseEnd_3151269 := by
    simpa [prefixWord, tailWord_3151269, baseEnd_3151269] using wordTrace_append hprefix tailTrace_3151269
  have hstable : (prefixWord ++ tailWord_3151269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151269).length < 2 ^ (prefixWord ++ tailWord_3151269).sum := by decide
  have hdescent : baseEnd_3151269 < baseStart_3151269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151271 : List Nat := [1, 1, 6, 1, 1, 1, 2, 5, 4]
def baseStart_3151271 : Nat := 118140960795 + 3151271 * 2 ^ 59
def prefixEnd_3151271 : Nat := 4983230072969 + 3 ^ 40 * 3151271 * 2
def baseEnd_3151271 : Nat := 359581487905476749204461

theorem tailTrace_3151271 : CollatzResearch.WordTrace tailWord_3151271 prefixEnd_3151271 359581487905476749204461 := by
  unfold tailWord_3151271
  simp only [CollatzResearch.WordTrace]
  refine ⟨114936295766490836084077667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76624197177660557389385111 114936295766490836084077667)
  ·
    refine ⟨172404443649736254126116501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114936295766490836084077667 172404443649736254126116501)
    ·
      refine ⟨8081458296081386912161711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 172404443649736254126116501 8081458296081386912161711)
      ·
        refine ⟨12122187444122080368242567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8081458296081386912161711 12122187444122080368242567)
        ·
          refine ⟨18183281166183120552363851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12122187444122080368242567 18183281166183120552363851)
          ·
            refine ⟨27274921749274680828545777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18183281166183120552363851 27274921749274680828545777)
            ·
              refine ⟨20456191311956010621409333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27274921749274680828545777 20456191311956010621409333)
              ·
                refine ⟨1917767935495875995757125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20456191311956010621409333 1917767935495875995757125)
                ·
                  refine ⟨359581487905476749204461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1917767935495875995757125 359581487905476749204461)
                  ·
                    rfl

theorem cell22_3151271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 4].length) (baseStart_3151271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151271 prefixEnd_3151271 := by exact prefixLift 3151271
  have htrace : WordTrace (prefixWord ++ tailWord_3151271) baseStart_3151271 baseEnd_3151271 := by
    simpa [prefixWord, tailWord_3151271, baseEnd_3151271] using wordTrace_append hprefix tailTrace_3151271
  have hstable : (prefixWord ++ tailWord_3151271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151271).length < 2 ^ (prefixWord ++ tailWord_3151271).sum := by decide
  have hdescent : baseEnd_3151271 < baseStart_3151271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151318 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3151318 : Nat := 118140960795 + 3151318 * 2 ^ 59
def prefixEnd_3151318 : Nat := 4983230072969 + 3 ^ 40 * 3151318 * 2
def baseEnd_3151318 : Nat := 1078760552776937791688239

theorem tailTrace_3151318 : CollatzResearch.WordTrace tailWord_3151318 prefixEnd_3151318 1078760552776937791688239 := by
  unfold tailWord_3151318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7183625624832535194439913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76625339998213708740692405 7183625624832535194439913)
  ·
    refine ⟨5387719218624401395829935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7183625624832535194439913 5387719218624401395829935)
    ·
      refine ⟨8081578827936602093744903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5387719218624401395829935 8081578827936602093744903)
      ·
        refine ⟨12122368241904903140617355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8081578827936602093744903 12122368241904903140617355)
        ·
          refine ⟨18183552362857354710926033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12122368241904903140617355 18183552362857354710926033)
          ·
            refine ⟨13637664272143016033194525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18183552362857354710926033 13637664272143016033194525)
            ·
              refine ⟨5114124102053631012447947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13637664272143016033194525 5114124102053631012447947)
              ·
                refine ⟨7671186153080446518671921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5114124102053631012447947 7671186153080446518671921)
                ·
                  refine ⟨5753389614810334889003941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7671186153080446518671921 5753389614810334889003941)
                  ·
                    refine ⟨1078760552776937791688239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5753389614810334889003941 1078760552776937791688239)
                    ·
                      rfl

theorem cell22_3151318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3151318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151318 prefixEnd_3151318 := by exact prefixLift 3151318
  have htrace : WordTrace (prefixWord ++ tailWord_3151318) baseStart_3151318 baseEnd_3151318 := by
    simpa [prefixWord, tailWord_3151318, baseEnd_3151318] using wordTrace_append hprefix tailTrace_3151318
  have hstable : (prefixWord ++ tailWord_3151318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151318).length < 2 ^ (prefixWord ++ tailWord_3151318).sum := by decide
  have hdescent : baseEnd_3151318 < baseStart_3151318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151344 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 7]
def baseStart_3151344 : Nat := 118140960795 + 3151344 * 2 ^ 59
def prefixEnd_3151344 : Nat := 4983230072969 + 3 ^ 40 * 3151344 * 2
def baseEnd_3151344 : Nat := 359589817702760796846053

theorem tailTrace_3151344 : CollatzResearch.WordTrace tailWord_3151344 prefixEnd_3151344 359589817702760796846053 := by
  unfold tailWord_3151344
  simp only [CollatzResearch.WordTrace]
  refine ⟨57469479147613184775742543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76625972196817579700990057 57469479147613184775742543)
  ·
    refine ⟨86204218721419777163613815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57469479147613184775742543 86204218721419777163613815)
    ·
      refine ⟨129306328082129665745420723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86204218721419777163613815 129306328082129665745420723)
      ·
        refine ⟨193959492123194498618131085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129306328082129665745420723 193959492123194498618131085)
        ·
          refine ⟨72734809546197936981799157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193959492123194498618131085 72734809546197936981799157)
          ·
            refine ⟨6818888394956056592043671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72734809546197936981799157 6818888394956056592043671)
            ·
              refine ⟨10228332592434084888065507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6818888394956056592043671 10228332592434084888065507)
              ·
                refine ⟨15342498888651127332098261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10228332592434084888065507 15342498888651127332098261)
                ·
                  refine ⟨359589817702760796846053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15342498888651127332098261 359589817702760796846053)
                  ·
                    rfl

theorem cell22_3151344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 7].length) (baseStart_3151344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151344 prefixEnd_3151344 := by exact prefixLift 3151344
  have htrace : WordTrace (prefixWord ++ tailWord_3151344) baseStart_3151344 baseEnd_3151344 := by
    simpa [prefixWord, tailWord_3151344, baseEnd_3151344] using wordTrace_append hprefix tailTrace_3151344
  have hstable : (prefixWord ++ tailWord_3151344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151344).length < 2 ^ (prefixWord ++ tailWord_3151344).sum := by decide
  have hdescent : baseEnd_3151344 < baseStart_3151344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151391 : List Nat := [1, 1, 2, 4, 1, 1, 4, 3, 1, 4]
def baseStart_3151391 : Nat := 118140960795 + 3151391 * 2 ^ 59
def prefixEnd_3151391 : Nat := 4983230072969 + 3 ^ 40 * 3151391 * 2
def baseEnd_3151391 : Nat := 1078785542168789934613015

theorem tailTrace_3151391 : CollatzResearch.WordTrace tailWord_3151391 prefixEnd_3151391 1078785542168789934613015 := by
  unfold tailWord_3151391
  simp only [CollatzResearch.WordTrace]
  refine ⟨114940672526056096578446027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76627115017370731052297351 114940672526056096578446027)
  ·
    refine ⟨172411008789084144867669041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114940672526056096578446027 172411008789084144867669041)
    ·
      refine ⟨129308256591813108650751781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172411008789084144867669041 129308256591813108650751781)
      ·
        refine ⟨24245298110964957872015959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129308256591813108650751781 24245298110964957872015959)
        ·
          refine ⟨36367947166447436808023939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24245298110964957872015959 36367947166447436808023939)
          ·
            refine ⟨54551920749671155212035909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36367947166447436808023939 54551920749671155212035909)
            ·
              refine ⟨10228485140563341602256733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54551920749671155212035909 10228485140563341602256733)
              ·
                refine ⟨3835681927711253100846275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10228485140563341602256733 3835681927711253100846275)
                ·
                  refine ⟨5753522891566879651269413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3835681927711253100846275 5753522891566879651269413)
                  ·
                    refine ⟨1078785542168789934613015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5753522891566879651269413 1078785542168789934613015)
                    ·
                      rfl

theorem cell22_3151391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_3151391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151391 prefixEnd_3151391 := by exact prefixLift 3151391
  have htrace : WordTrace (prefixWord ++ tailWord_3151391) baseStart_3151391 baseEnd_3151391 := by
    simpa [prefixWord, tailWord_3151391, baseEnd_3151391] using wordTrace_append hprefix tailTrace_3151391
  have hstable : (prefixWord ++ tailWord_3151391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151391).length < 2 ^ (prefixWord ++ tailWord_3151391).sum := by decide
  have hdescent : baseEnd_3151391 < baseStart_3151391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151434 : List Nat := [3, 1, 2, 1, 1, 3, 1, 10]
def baseStart_3151434 : Nat := 118140960795 + 3151434 * 2 ^ 59
def prefixEnd_3151434 : Nat := 4983230072969 + 3 ^ 40 * 3151434 * 2
def baseEnd_3151434 : Nat := 119866695771950239531987

theorem tailTrace_3151434 : CollatzResearch.WordTrace tailWord_3151434 prefixEnd_3151434 119866695771950239531987 := by
  unfold tailWord_3151434
  simp only [CollatzResearch.WordTrace]
  refine ⟨28735560216225078730565339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76628160576600209948174237 28735560216225078730565339)
  ·
    refine ⟨43103340324337618095848009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28735560216225078730565339 43103340324337618095848009)
    ·
      refine ⟨32327505243253213571886007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43103340324337618095848009 32327505243253213571886007)
      ·
        refine ⟨48491257864879820357829011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32327505243253213571886007 48491257864879820357829011)
        ·
          refine ⟨72736886797319730536743517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48491257864879820357829011 72736886797319730536743517)
          ·
            refine ⟨27276332548994898951278819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72736886797319730536743517 27276332548994898951278819)
            ·
              refine ⟨40914498823492348426918229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27276332548994898951278819 40914498823492348426918229)
              ·
                refine ⟨119866695771950239531987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40914498823492348426918229 119866695771950239531987)
                ·
                  rfl

theorem cell22_3151434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_3151434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151434 prefixEnd_3151434 := by exact prefixLift 3151434
  have htrace : WordTrace (prefixWord ++ tailWord_3151434) baseStart_3151434 baseEnd_3151434 := by
    simpa [prefixWord, tailWord_3151434, baseEnd_3151434] using wordTrace_append hprefix tailTrace_3151434
  have hstable : (prefixWord ++ tailWord_3151434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151434).length < 2 ^ (prefixWord ++ tailWord_3151434).sum := by decide
  have hdescent : baseEnd_3151434 < baseStart_3151434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151436 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_3151436 : Nat := 118140960795 + 3151436 * 2 ^ 59
def prefixEnd_3151436 : Nat := 4983230072969 + 3 ^ 40 * 3151436 * 2
def baseEnd_3151436 : Nat := 1078800946588424817237877

theorem tailTrace_3151436 : CollatzResearch.WordTrace tailWord_3151436 prefixEnd_3151436 1078800946588424817237877 := by
  unfold tailWord_3151436
  simp only [CollatzResearch.WordTrace]
  refine ⟨57471156905446534631917081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76628209207262046175889441 57471156905446534631917081)
  ·
    refine ⟨43103367679084900973937811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57471156905446534631917081 43103367679084900973937811)
    ·
      refine ⟨64655051518627351460906717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43103367679084900973937811 64655051518627351460906717)
      ·
        refine ⟨24245644319485256797840019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64655051518627351460906717 24245644319485256797840019)
        ·
          refine ⟨36368466479227885196760029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24245644319485256797840019 36368466479227885196760029)
          ·
            refine ⟨13638174929710456948785011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36368466479227885196760029 13638174929710456948785011)
            ·
              refine ⟨20457262394565685423177517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13638174929710456948785011 20457262394565685423177517)
              ·
                refine ⟨7671473397962132033691569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20457262394565685423177517 7671473397962132033691569)
                ·
                  refine ⟨5753605048471599025268677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7671473397962132033691569 5753605048471599025268677)
                  ·
                    refine ⟨1078800946588424817237877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5753605048471599025268677 1078800946588424817237877)
                    ·
                      rfl

theorem cell22_3151436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_3151436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151436 prefixEnd_3151436 := by exact prefixLift 3151436
  have htrace : WordTrace (prefixWord ++ tailWord_3151436) baseStart_3151436 baseEnd_3151436 := by
    simpa [prefixWord, tailWord_3151436, baseEnd_3151436] using wordTrace_append hprefix tailTrace_3151436
  have hstable : (prefixWord ++ tailWord_3151436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151436).length < 2 ^ (prefixWord ++ tailWord_3151436).sum := by decide
  have hdescent : baseEnd_3151436 < baseStart_3151436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151479 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 9]
def baseStart_3151479 : Nat := 118140960795 + 3151479 * 2 ^ 59
def prefixEnd_3151479 : Nat := 4983230072969 + 3 ^ 40 * 3151479 * 2
def baseEnd_3151479 : Nat := 359605222122395679470915

theorem tailTrace_3151479 : CollatzResearch.WordTrace tailWord_3151479 prefixEnd_3151479 359605222122395679470915 := by
  unfold tailWord_3151479
  simp only [CollatzResearch.WordTrace]
  refine ⟨114943882149737287607649491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76629254766491525071766327 114943882149737287607649491)
  ·
    refine ⟨172415823224605931411474237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114943882149737287607649491 172415823224605931411474237)
    ·
      refine ⟨64655933709227224279302839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172415823224605931411474237 64655933709227224279302839)
      ·
        refine ⟨96983900563840836418954259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64655933709227224279302839 96983900563840836418954259)
        ·
          refine ⟨145475850845761254628431389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96983900563840836418954259 145475850845761254628431389)
          ·
            refine ⟨54553444067160470485661771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145475850845761254628431389 54553444067160470485661771)
            ·
              refine ⟨81830166100740705728492657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54553444067160470485661771 81830166100740705728492657)
              ·
                refine ⟨61372624575555529296369493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81830166100740705728492657 61372624575555529296369493)
                ·
                  refine ⟨359605222122395679470915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61372624575555529296369493 359605222122395679470915)
                  ·
                    rfl

theorem cell22_3151479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 9].length) (baseStart_3151479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151479 prefixEnd_3151479 := by exact prefixLift 3151479
  have htrace : WordTrace (prefixWord ++ tailWord_3151479) baseStart_3151479 baseEnd_3151479 := by
    simpa [prefixWord, tailWord_3151479, baseEnd_3151479] using wordTrace_append hprefix tailTrace_3151479
  have hstable : (prefixWord ++ tailWord_3151479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151479).length < 2 ^ (prefixWord ++ tailWord_3151479).sum := by decide
  have hdescent : baseEnd_3151479 < baseStart_3151479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151500 : List Nat := [2, 2, 1, 2, 1, 1, 6, 3, 1, 3]
def baseStart_3151500 : Nat := 118140960795 + 3151500 * 2 ^ 59
def prefixEnd_3151500 : Nat := 4983230072969 + 3 ^ 40 * 3151500 * 2
def baseEnd_3151500 : Nat := 1078822855096349983637681

theorem tailTrace_3151500 : CollatzResearch.WordTrace tailWord_3151500 prefixEnd_3151500 1078822855096349983637681 := by
  unfold tailWord_3151500
  simp only [CollatzResearch.WordTrace]
  refine ⟨57472324041330604097081977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76629765388440805462775969 57472324041330604097081977)
  ·
    refine ⟨43104243030997953072811483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57472324041330604097081977 43104243030997953072811483)
    ·
      refine ⟨64656364546496929609217225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43104243030997953072811483 64656364546496929609217225)
      ·
        refine ⟨48492273409872697206912919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64656364546496929609217225 48492273409872697206912919)
        ·
          refine ⟨72738410114809045810369379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48492273409872697206912919 72738410114809045810369379)
          ·
            refine ⟨109107615172213568715554069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72738410114809045810369379 109107615172213568715554069)
            ·
              refine ⟨5114419461197511033541597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109107615172213568715554069 5114419461197511033541597)
              ·
                refine ⟨1917907297949066637578099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5114419461197511033541597 1917907297949066637578099)
                ·
                  refine ⟨2876860946923599956367149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1917907297949066637578099 2876860946923599956367149)
                  ·
                    refine ⟨1078822855096349983637681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2876860946923599956367149 1078822855096349983637681)
                    ·
                      rfl

theorem cell22_3151500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_3151500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151500 prefixEnd_3151500 := by exact prefixLift 3151500
  have htrace : WordTrace (prefixWord ++ tailWord_3151500) baseStart_3151500 baseEnd_3151500 := by
    simpa [prefixWord, tailWord_3151500, baseEnd_3151500] using wordTrace_append hprefix tailTrace_3151500
  have hstable : (prefixWord ++ tailWord_3151500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151500).length < 2 ^ (prefixWord ++ tailWord_3151500).sum := by decide
  have hdescent : baseEnd_3151500 < baseStart_3151500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151511 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 2, 5]
def baseStart_3151511 : Nat := 118140960795 + 3151511 * 2 ^ 59
def prefixEnd_3151511 : Nat := 4983230072969 + 3 ^ 40 * 3151511 * 2
def baseEnd_3151511 : Nat := 1078826620621149621612647

theorem tailTrace_3151511 : CollatzResearch.WordTrace tailWord_3151511 prefixEnd_3151511 1078826620621149621612647 := by
  unfold tailWord_3151511
  simp only [CollatzResearch.WordTrace]
  refine ⟨114945049285621357072814387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76630032857080904715209591 114945049285621357072814387)
  ·
    refine ⟨172417573928432035609221581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114945049285621357072814387 172417573928432035609221581)
    ·
      refine ⟨64656590223162013353458093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172417573928432035609221581 64656590223162013353458093)
      ·
        refine ⟨24246221333685755007546785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64656590223162013353458093 24246221333685755007546785)
        ·
          refine ⟨18184666000264316255660089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24246221333685755007546785 18184666000264316255660089)
          ·
            refine ⟨13638499500198237191745067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18184666000264316255660089 13638499500198237191745067)
            ·
              refine ⟨20457749250297355787617601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13638499500198237191745067 20457749250297355787617601)
              ·
                refine ⟨15343311937723016840713201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20457749250297355787617601 15343311937723016840713201)
                ·
                  refine ⟨11507483953292262630534901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15343311937723016840713201 11507483953292262630534901)
                  ·
                    refine ⟨1078826620621149621612647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11507483953292262630534901 1078826620621149621612647)
                    ·
                      rfl

theorem cell22_3151511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_3151511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151511 prefixEnd_3151511 := by exact prefixLift 3151511
  have htrace : WordTrace (prefixWord ++ tailWord_3151511) baseStart_3151511 baseEnd_3151511 := by
    simpa [prefixWord, tailWord_3151511, baseEnd_3151511] using wordTrace_append hprefix tailTrace_3151511
  have hstable : (prefixWord ++ tailWord_3151511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151511).length < 2 ^ (prefixWord ++ tailWord_3151511).sum := by decide
  have hdescent : baseEnd_3151511 < baseStart_3151511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151543 : List Nat := [1, 1, 3, 1, 5, 1, 1, 4, 1, 4]
def baseStart_3151543 : Nat := 118140960795 + 3151543 * 2 ^ 59
def prefixEnd_3151543 : Nat := 4983230072969 + 3 ^ 40 * 3151543 * 2
def baseEnd_3151543 : Nat := 1078837574875112204812549

theorem tailTrace_3151543 : CollatzResearch.WordTrace tailWord_3151543 prefixEnd_3151543 1078837574875112204812549 := by
  unfold tailWord_3151543
  simp only [CollatzResearch.WordTrace]
  refine ⟨114946216421505426537979283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76630810947670284358652855 114946216421505426537979283)
  ·
    refine ⟨172419324632258139806968925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114946216421505426537979283 172419324632258139806968925)
    ·
      refine ⟨64657246737096802427613347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172419324632258139806968925 64657246737096802427613347)
      ·
        refine ⟨96985870105645203641420021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64657246737096802427613347 96985870105645203641420021)
        ·
          refine ⟨9092425322404237841383127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96985870105645203641420021 9092425322404237841383127)
          ·
            refine ⟨13638637983606356762074691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9092425322404237841383127 13638637983606356762074691)
            ·
              refine ⟨20457956975409535143112037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13638637983606356762074691 20457956975409535143112037)
              ·
                refine ⟨3835866932889287839333507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20457956975409535143112037 3835866932889287839333507)
                ·
                  refine ⟨5753800399333931759000261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3835866932889287839333507 5753800399333931759000261)
                  ·
                    refine ⟨1078837574875112204812549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5753800399333931759000261 1078837574875112204812549)
                    ·
                      rfl

theorem cell22_3151543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_3151543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151543 prefixEnd_3151543 := by exact prefixLift 3151543
  have htrace : WordTrace (prefixWord ++ tailWord_3151543) baseStart_3151543 baseEnd_3151543 := by
    simpa [prefixWord, tailWord_3151543, baseEnd_3151543] using wordTrace_append hprefix tailTrace_3151543
  have hstable : (prefixWord ++ tailWord_3151543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151543).length < 2 ^ (prefixWord ++ tailWord_3151543).sum := by decide
  have hdescent : baseEnd_3151543 < baseStart_3151543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151575 : List Nat := [1, 1, 3, 2, 1, 3, 5, 2, 4]
def baseStart_3151575 : Nat := 118140960795 + 3151575 * 2 ^ 59
def prefixEnd_3151575 : Nat := 4983230072969 + 3 ^ 40 * 3151575 * 2
def baseEnd_3151575 : Nat := 359616176376358262670817

theorem tailTrace_3151575 : CollatzResearch.WordTrace tailWord_3151575 prefixEnd_3151575 359616176376358262670817 := by
  unfold tailWord_3151575
  simp only [CollatzResearch.WordTrace]
  refine ⟨114947383557389496003144179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76631589038259664002096119 114947383557389496003144179)
  ·
    refine ⟨172421075336084244004716269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114947383557389496003144179 172421075336084244004716269)
    ·
      refine ⟨64657903251031591501768601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172421075336084244004716269 64657903251031591501768601)
      ·
        refine ⟨48493427438273693626326451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64657903251031591501768601 48493427438273693626326451)
        ·
          refine ⟨72740141157410540439489677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48493427438273693626326451 72740141157410540439489677)
          ·
            refine ⟨27277552934028952664808629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72740141157410540439489677 27277552934028952664808629)
            ·
              refine ⟨2557270587565214312325809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27277552934028952664808629 2557270587565214312325809)
              ·
                refine ⟨1917952940673910734244357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2557270587565214312325809 1917952940673910734244357)
                ·
                  refine ⟨359616176376358262670817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1917952940673910734244357 359616176376358262670817)
                  ·
                    rfl

theorem cell22_3151575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 4].length) (baseStart_3151575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151575 prefixEnd_3151575 := by exact prefixLift 3151575
  have htrace : WordTrace (prefixWord ++ tailWord_3151575) baseStart_3151575 baseEnd_3151575 := by
    simpa [prefixWord, tailWord_3151575, baseEnd_3151575] using wordTrace_append hprefix tailTrace_3151575
  have hstable : (prefixWord ++ tailWord_3151575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151575).length < 2 ^ (prefixWord ++ tailWord_3151575).sum := by decide
  have hdescent : baseEnd_3151575 < baseStart_3151575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151648 : List Nat := [2, 1, 1, 5, 1, 1, 1, 5, 5]
def baseStart_3151648 : Nat := 118140960795 + 3151648 * 2 ^ 59
def prefixEnd_3151648 : Nat := 4983230072969 + 3 ^ 40 * 3151648 * 2
def baseEnd_3151648 : Nat := 359624506173642310312409

theorem tailTrace_3151648 : CollatzResearch.WordTrace tailWord_3151648 prefixEnd_3151648 359624506173642310312409 := by
  unfold tailWord_3151648
  simp only [CollatzResearch.WordTrace]
  refine ⟨57475023043062514735275799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76633364057416686313701065 57475023043062514735275799)
  ·
    refine ⟨86212534564593772102913699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57475023043062514735275799 86212534564593772102913699)
    ·
      refine ⟨129318801846890658154370549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86212534564593772102913699 129318801846890658154370549)
      ·
        refine ⟨12123637673145999201972239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129318801846890658154370549 12123637673145999201972239)
        ·
          refine ⟨18185456509718998802958359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12123637673145999201972239 18185456509718998802958359)
          ·
            refine ⟨27278184764578498204437539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18185456509718998802958359 27278184764578498204437539)
            ·
              refine ⟨40917277146867747306656309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27278184764578498204437539 40917277146867747306656309)
              ·
                refine ⟨3835994732518851309999029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40917277146867747306656309 3835994732518851309999029)
                ·
                  refine ⟨359624506173642310312409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3835994732518851309999029 359624506173642310312409)
                  ·
                    rfl

theorem cell22_3151648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 5].length) (baseStart_3151648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151648 prefixEnd_3151648 := by exact prefixLift 3151648
  have htrace : WordTrace (prefixWord ++ tailWord_3151648) baseStart_3151648 baseEnd_3151648 := by
    simpa [prefixWord, tailWord_3151648, baseEnd_3151648] using wordTrace_append hprefix tailTrace_3151648
  have hstable : (prefixWord ++ tailWord_3151648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151648).length < 2 ^ (prefixWord ++ tailWord_3151648).sum := by decide
  have hdescent : baseEnd_3151648 < baseStart_3151648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151669 : List Nat := [1, 3, 3, 1, 4, 1, 2, 3, 1, 3]
def baseStart_3151669 : Nat := 118140960795 + 3151669 * 2 ^ 59
def prefixEnd_3151669 : Nat := 4983230072969 + 3 ^ 40 * 3151669 * 2
def baseEnd_3151669 : Nat := 1078880707250089876162163

theorem tailTrace_3151669 : CollatzResearch.WordTrace tailWord_3151669 prefixEnd_3151669 1078880707250089876162163 := by
  unfold tailWord_3151669
  simp only [CollatzResearch.WordTrace]
  refine ⟨114950812019048950057066061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76633874679365966704710707 114950812019048950057066061)
  ·
    refine ⟨43106554507143356271399773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114950812019048950057066061 43106554507143356271399773)
    ·
      refine ⟨16164957940178758601774915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43106554507143356271399773 16164957940178758601774915)
      ·
        refine ⟨24247436910268137902662373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16164957940178758601774915 24247436910268137902662373)
        ·
          refine ⟨4546394420675275856749195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24247436910268137902662373 4546394420675275856749195)
          ·
            refine ⟨6819591631012913785123793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4546394420675275856749195 6819591631012913785123793)
            ·
              refine ⟨5114693723259685338842845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6819591631012913785123793 5114693723259685338842845)
              ·
                refine ⟨1918010146222382002066067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5114693723259685338842845 1918010146222382002066067)
                ·
                  refine ⟨2877015219333573003099101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918010146222382002066067 2877015219333573003099101)
                  ·
                    refine ⟨1078880707250089876162163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2877015219333573003099101 1078880707250089876162163)
                    ·
                      rfl

theorem cell22_3151669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_3151669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151669 prefixEnd_3151669 := by exact prefixLift 3151669
  have htrace : WordTrace (prefixWord ++ tailWord_3151669) baseStart_3151669 baseEnd_3151669 := by
    simpa [prefixWord, tailWord_3151669, baseEnd_3151669] using wordTrace_append hprefix tailTrace_3151669
  have hstable : (prefixWord ++ tailWord_3151669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151669).length < 2 ^ (prefixWord ++ tailWord_3151669).sum := by decide
  have hdescent : baseEnd_3151669 < baseStart_3151669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151686 : List Nat := [6, 1, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_3151686 : Nat := 118140960795 + 3151686 * 2 ^ 59
def prefixEnd_3151686 : Nat := 4983230072969 + 3 ^ 40 * 3151686 * 2
def baseEnd_3151686 : Nat := 1078886526697507498487111

theorem tailTrace_3151686 : CollatzResearch.WordTrace tailWord_3151686 prefixEnd_3151686 1078886526697507498487111 := by
  unfold tailWord_3151686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3592232251874605061263591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76634288039991574640289941 3592232251874605061263591)
  ·
    refine ⟨5388348377811907591895387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3592232251874605061263591 5388348377811907591895387)
    ·
      refine ⟨8082522566717861387843081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5388348377811907591895387 8082522566717861387843081)
      ·
        refine ⟨6061891925038396040882311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8082522566717861387843081 6061891925038396040882311)
        ·
          refine ⟨9092837887557594061323467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6061891925038396040882311 9092837887557594061323467)
          ·
            refine ⟨13639256831336391091985201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9092837887557594061323467 13639256831336391091985201)
            ·
              refine ⟨10229442623502293318988901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13639256831336391091985201 10229442623502293318988901)
              ·
                refine ⟨1918020491906679997310419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10229442623502293318988901 1918020491906679997310419)
                ·
                  refine ⟨2877030737860019995965629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918020491906679997310419 2877030737860019995965629)
                  ·
                    refine ⟨1078886526697507498487111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2877030737860019995965629 1078886526697507498487111)
                    ·
                      rfl

theorem cell22_3151686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_3151686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151686 prefixEnd_3151686 := by exact prefixLift 3151686
  have htrace : WordTrace (prefixWord ++ tailWord_3151686) baseStart_3151686 baseEnd_3151686 := by
    simpa [prefixWord, tailWord_3151686, baseEnd_3151686] using wordTrace_append hprefix tailTrace_3151686
  have hstable : (prefixWord ++ tailWord_3151686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151686).length < 2 ^ (prefixWord ++ tailWord_3151686).sum := by decide
  have hdescent : baseEnd_3151686 < baseStart_3151686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151691 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 1, 11]
def baseStart_3151691 : Nat := 118140960795 + 3151691 * 2 ^ 59
def prefixEnd_3151691 : Nat := 4983230072969 + 3 ^ 40 * 3151691 * 2
def baseEnd_3151691 : Nat := 1078888238299689152112095

theorem tailTrace_3151691 : CollatzResearch.WordTrace tailWord_3151691 prefixEnd_3151691 1078888238299689152112095 := by
  unfold tailWord_3151691
  simp only [CollatzResearch.WordTrace]
  refine ⟨114951614424969247814366927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76634409616646165209577951 114951614424969247814366927)
  ·
    refine ⟨172427421637453871721550391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114951614424969247814366927 172427421637453871721550391)
    ·
      refine ⟨258641132456180807582325587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172427421637453871721550391 258641132456180807582325587)
      ·
        refine ⟨387961698684271211373488381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258641132456180807582325587 387961698684271211373488381)
        ·
          refine ⟨145485637006601704265058143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387961698684271211373488381 145485637006601704265058143)
          ·
            refine ⟨218228455509902556397587215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145485637006601704265058143 218228455509902556397587215)
            ·
              refine ⟨327342683264853834596380823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218228455509902556397587215 327342683264853834596380823)
              ·
                refine ⟨491014024897280751894571235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327342683264853834596380823 491014024897280751894571235)
                ·
                  refine ⟨736521037345921127841856853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491014024897280751894571235 736521037345921127841856853)
                  ·
                    refine ⟨1078888238299689152112095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 736521037345921127841856853 1078888238299689152112095)
                    ·
                      rfl

theorem cell22_3151691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_3151691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151691 prefixEnd_3151691 := by exact prefixLift 3151691
  have htrace : WordTrace (prefixWord ++ tailWord_3151691) baseStart_3151691 baseEnd_3151691 := by
    simpa [prefixWord, tailWord_3151691, baseEnd_3151691] using wordTrace_append hprefix tailTrace_3151691
  have hstable : (prefixWord ++ tailWord_3151691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151691).length < 2 ^ (prefixWord ++ tailWord_3151691).sum := by decide
  have hdescent : baseEnd_3151691 < baseStart_3151691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151723 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 2, 4]
def baseStart_3151723 : Nat := 118140960795 + 3151723 * 2 ^ 59
def prefixEnd_3151723 : Nat := 4983230072969 + 3 ^ 40 * 3151723 * 2
def baseEnd_3151723 : Nat := 1078899192553651735311997

theorem tailTrace_3151723 : CollatzResearch.WordTrace tailWord_3151723 prefixEnd_3151723 1078899192553651735311997 := by
  unfold tailWord_3151723
  simp only [CollatzResearch.WordTrace]
  refine ⟨114952781560853317279531823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76635187707235544853021215 114952781560853317279531823)
  ·
    refine ⟨172429172341279975919297735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114952781560853317279531823 172429172341279975919297735)
    ·
      refine ⟨258643758511919963878946603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172429172341279975919297735 258643758511919963878946603)
      ·
        refine ⟨387965637767879945818419905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258643758511919963878946603 387965637767879945818419905)
        ·
          refine ⟨290974228325909959363814929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387965637767879945818419905 290974228325909959363814929)
          ·
            refine ⟨218230671244432469522861197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290974228325909959363814929 218230671244432469522861197)
            ·
              refine ⟨81836501716662176071072949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218230671244432469522861197 81836501716662176071072949)
              ·
                refine ⟨7672172035937079006663089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81836501716662176071072949 7672172035937079006663089)
                ·
                  refine ⟨5754129026952809254997317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7672172035937079006663089 5754129026952809254997317)
                  ·
                    refine ⟨1078899192553651735311997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5754129026952809254997317 1078899192553651735311997)
                    ·
                      rfl

theorem cell22_3151723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 4].length) (baseStart_3151723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151723 prefixEnd_3151723 := by exact prefixLift 3151723
  have htrace : WordTrace (prefixWord ++ tailWord_3151723) baseStart_3151723 baseEnd_3151723 := by
    simpa [prefixWord, tailWord_3151723, baseEnd_3151723] using wordTrace_append hprefix tailTrace_3151723
  have hstable : (prefixWord ++ tailWord_3151723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151723).length < 2 ^ (prefixWord ++ tailWord_3151723).sum := by decide
  have hdescent : baseEnd_3151723 < baseStart_3151723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151725 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_3151725 : Nat := 118140960795 + 3151725 * 2 ^ 59
def prefixEnd_3151725 : Nat := 4983230072969 + 3 ^ 40 * 3151725 * 2
def baseEnd_3151725 : Nat := 1078899877194524396761991

theorem tailTrace_3151725 : CollatzResearch.WordTrace tailWord_3151725 prefixEnd_3151725 1078899877194524396761991 := by
  unfold tailWord_3151725
  simp only [CollatzResearch.WordTrace]
  refine ⟨114952854506846071621104629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76635236337897381080736419 114952854506846071621104629)
  ·
    refine ⟨10776830110016819214478559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114952854506846071621104629 10776830110016819214478559)
    ·
      refine ⟨16165245165025228821717839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10776830110016819214478559 16165245165025228821717839)
      ·
        refine ⟨24247867747537843232576759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16165245165025228821717839 24247867747537843232576759)
        ·
          refine ⟨36371801621306764848865139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24247867747537843232576759 36371801621306764848865139)
          ·
            refine ⟨54557702431960147273297709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36371801621306764848865139 54557702431960147273297709)
            ·
              refine ⟨20459138411985055227486641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54557702431960147273297709 20459138411985055227486641)
              ·
                refine ⟨15344353808988791420614981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20459138411985055227486641 15344353808988791420614981)
                ·
                  refine ⟨2877066339185398391365309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15344353808988791420614981 2877066339185398391365309)
                  ·
                    refine ⟨1078899877194524396761991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2877066339185398391365309 1078899877194524396761991)
                    ·
                      rfl

theorem cell22_3151725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_3151725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151725 prefixEnd_3151725 := by exact prefixLift 3151725
  have htrace : WordTrace (prefixWord ++ tailWord_3151725) baseStart_3151725 baseEnd_3151725 := by
    simpa [prefixWord, tailWord_3151725, baseEnd_3151725] using wordTrace_append hprefix tailTrace_3151725
  have hstable : (prefixWord ++ tailWord_3151725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151725).length < 2 ^ (prefixWord ++ tailWord_3151725).sum := by decide
  have hdescent : baseEnd_3151725 < baseStart_3151725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151800 : List Nat := [2, 1, 2, 1, 2, 3, 4, 2, 5]
def baseStart_3151800 : Nat := 118140960795 + 3151800 * 2 ^ 59
def prefixEnd_3151800 : Nat := 4983230072969 + 3 ^ 40 * 3151800 * 2
def baseEnd_3151800 : Nat := 359641850409083067045587

theorem tailTrace_3151800 : CollatzResearch.WordTrace tailWord_3151800 prefixEnd_3151800 359641850409083067045587 := by
  unfold tailWord_3151800
  simp only [CollatzResearch.WordTrace]
  refine ⟨57477794990787179715042427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76637059987716239620056569 57477794990787179715042427)
  ·
    refine ⟨86216692486180769572563641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57477794990787179715042427 86216692486180769572563641)
    ·
      refine ⟨64662519364635577179422731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86216692486180769572563641 64662519364635577179422731)
      ·
        refine ⟨96993779046953365769134097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64662519364635577179422731 96993779046953365769134097)
        ·
          refine ⟨72745334285215024326850573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96993779046953365769134097 72745334285215024326850573)
          ·
            refine ⟨27279500356955634122568965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72745334285215024326850573 27279500356955634122568965)
            ·
              refine ⟨5114906316929181397981681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27279500356955634122568965 5114906316929181397981681)
              ·
                refine ⟨3836179737696886048486261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5114906316929181397981681 3836179737696886048486261)
                ·
                  refine ⟨359641850409083067045587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3836179737696886048486261 359641850409083067045587)
                  ·
                    rfl

theorem cell22_3151800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 2, 5].length) (baseStart_3151800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151800 prefixEnd_3151800 := by exact prefixLift 3151800
  have htrace : WordTrace (prefixWord ++ tailWord_3151800) baseStart_3151800 baseEnd_3151800 := by
    simpa [prefixWord, tailWord_3151800, baseEnd_3151800] using wordTrace_append hprefix tailTrace_3151800
  have hstable : (prefixWord ++ tailWord_3151800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151800).length < 2 ^ (prefixWord ++ tailWord_3151800).sum := by decide
  have hdescent : baseEnd_3151800 < baseStart_3151800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151877 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 1, 5]
def baseStart_3151877 : Nat := 118140960795 + 3151877 * 2 ^ 59
def prefixEnd_3151877 : Nat := 4983230072969 + 3 ^ 40 * 3151877 * 2
def baseEnd_3151877 : Nat := 1078951909900846666961525

theorem tailTrace_3151877 : CollatzResearch.WordTrace tailWord_3151877 prefixEnd_3151877 1078951909900846666961525 := by
  unfold tailWord_3151877
  simp only [CollatzResearch.WordTrace]
  refine ⟨114958398402295401580637885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76638932268196934387091923 114958398402295401580637885)
  ·
    refine ⟨43109399400860775592739207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114958398402295401580637885 43109399400860775592739207)
    ·
      refine ⟨64664099101291163389108811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43109399400860775592739207 64664099101291163389108811)
      ·
        refine ⟨96996148651936745083663217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64664099101291163389108811 96996148651936745083663217)
        ·
          refine ⟨72747111488952558812747413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96996148651936745083663217 72747111488952558812747413)
          ·
            refine ⟨3410020851044651194347535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72747111488952558812747413 3410020851044651194347535)
            ·
              refine ⟨5115031276566976791521303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410020851044651194347535 5115031276566976791521303)
              ·
                refine ⟨7672546914850465187281955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5115031276566976791521303 7672546914850465187281955)
                ·
                  refine ⟨11508820372275697780922933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7672546914850465187281955 11508820372275697780922933)
                  ·
                    refine ⟨1078951909900846666961525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11508820372275697780922933 1078951909900846666961525)
                    ·
                      rfl

theorem cell22_3151877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_3151877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151877 prefixEnd_3151877 := by exact prefixLift 3151877
  have htrace : WordTrace (prefixWord ++ tailWord_3151877) baseStart_3151877 baseEnd_3151877 := by
    simpa [prefixWord, tailWord_3151877, baseEnd_3151877] using wordTrace_append hprefix tailTrace_3151877
  have hstable : (prefixWord ++ tailWord_3151877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151877).length < 2 ^ (prefixWord ++ tailWord_3151877).sum := by decide
  have hdescent : baseEnd_3151877 < baseStart_3151877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151924 : List Nat := [2, 5, 1, 2, 2, 1, 2, 7]
def baseStart_3151924 : Nat := 118140960795 + 3151924 * 2 ^ 59
def prefixEnd_3151924 : Nat := 4983230072969 + 3 ^ 40 * 3151924 * 2
def baseEnd_3151924 : Nat := 119885333217928245670709

theorem tailTrace_3151924 : CollatzResearch.WordTrace tailWord_3151924 prefixEnd_3151924 119885333217928245670709 := by
  unfold tailWord_3151924
  simp only [CollatzResearch.WordTrace]
  refine ⟨57480056316562564303799413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76640075088750085738399217 57480056316562564303799413)
  ·
    refine ⟨5388755279677740403481195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57480056316562564303799413 5388755279677740403481195)
    ·
      refine ⟨8083132919516610605221793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5388755279677740403481195 8083132919516610605221793)
      ·
        refine ⟨6062349689637457953916345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8083132919516610605221793 6062349689637457953916345)
        ·
          refine ⟨4546762267228093465437259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6062349689637457953916345 4546762267228093465437259)
          ·
            refine ⟨6820143400842140198155889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4546762267228093465437259 6820143400842140198155889)
            ·
              refine ⟨5115107550631605148616917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6820143400842140198155889 5115107550631605148616917)
              ·
                refine ⟨119885333217928245670709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5115107550631605148616917 119885333217928245670709)
                ·
                  rfl

theorem cell22_3151924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 7].length) (baseStart_3151924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151924 prefixEnd_3151924 := by exact prefixLift 3151924
  have htrace : WordTrace (prefixWord ++ tailWord_3151924) baseStart_3151924 baseEnd_3151924 := by
    simpa [prefixWord, tailWord_3151924, baseEnd_3151924] using wordTrace_append hprefix tailTrace_3151924
  have hstable : (prefixWord ++ tailWord_3151924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151924).length < 2 ^ (prefixWord ++ tailWord_3151924).sum := by decide
  have hdescent : baseEnd_3151924 < baseStart_3151924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151928 : List Nat := [2, 1, 2, 1, 7, 1, 2, 1, 2, 3]
def baseStart_3151928 : Nat := 118140960795 + 3151928 * 2 ^ 59
def prefixEnd_3151928 : Nat := 4983230072969 + 3 ^ 40 * 3151928 * 2
def baseEnd_3151928 : Nat := 1078969368243099533936369

theorem tailTrace_3151928 : CollatzResearch.WordTrace tailWord_3151928 prefixEnd_3151928 1078969368243099533936369 := by
  unfold tailWord_3151928
  simp only [CollatzResearch.WordTrace]
  refine ⟨57480129262555318645372219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76640172350073758193829625 57480129262555318645372219)
  ·
    refine ⟨86220193893832977968058329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57480129262555318645372219 86220193893832977968058329)
    ·
      refine ⟨64665145420374733476043747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86220193893832977968058329 64665145420374733476043747)
      ·
        refine ⟨96997718130562100214065621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64665145420374733476043747 96997718130562100214065621)
        ·
          refine ⟨2273384018685049223767163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 96997718130562100214065621 2273384018685049223767163)
          ·
            refine ⟨3410076028027573835650745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273384018685049223767163 3410076028027573835650745)
            ·
              refine ⟨2557557021020680376738059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3410076028027573835650745 2557557021020680376738059)
              ·
                refine ⟨3836335531531020565107089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2557557021020680376738059 3836335531531020565107089)
                ·
                  refine ⟨2877251648648265423830317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3836335531531020565107089 2877251648648265423830317)
                  ·
                    refine ⟨1078969368243099533936369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2877251648648265423830317 1078969368243099533936369)
                    ·
                      rfl

theorem cell22_3151928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_3151928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151928 prefixEnd_3151928 := by exact prefixLift 3151928
  have htrace : WordTrace (prefixWord ++ tailWord_3151928) baseStart_3151928 baseEnd_3151928 := by
    simpa [prefixWord, tailWord_3151928, baseEnd_3151928] using wordTrace_append hprefix tailTrace_3151928
  have hstable : (prefixWord ++ tailWord_3151928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151928).length < 2 ^ (prefixWord ++ tailWord_3151928).sum := by decide
  have hdescent : baseEnd_3151928 < baseStart_3151928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151973 : List Nat := [1, 3, 1, 3, 2, 4, 2, 2, 1, 3]
def baseStart_3151973 : Nat := 118140960795 + 3151973 * 2 ^ 59
def prefixEnd_3151973 : Nat := 4983230072969 + 3 ^ 40 * 3151973 * 2
def baseEnd_3151973 : Nat := 1078984772662734416561231

theorem tailTrace_3151973 : CollatzResearch.WordTrace tailWord_3151973 prefixEnd_3151973 1078984772662734416561231 := by
  unfold tailWord_3151973
  simp only [CollatzResearch.WordTrace]
  refine ⟨114961899809947609976132573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76641266539965073317421715 114961899809947609976132573)
  ·
    refine ⟨43110712428730353741049715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114961899809947609976132573 43110712428730353741049715)
    ·
      refine ⟨64666068643095530611574573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43110712428730353741049715 64666068643095530611574573)
      ·
        refine ⟨24249775741160823979340465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64666068643095530611574573 24249775741160823979340465)
        ·
          refine ⟨18187331805870617984505349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24249775741160823979340465 18187331805870617984505349)
          ·
            refine ⟨3410124713600740872094753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18187331805870617984505349 3410124713600740872094753)
            ·
              refine ⟨2557593535200555654071065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3410124713600740872094753 2557593535200555654071065)
              ·
                refine ⟨1918195151400416740553299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2557593535200555654071065 1918195151400416740553299)
                ·
                  refine ⟨2877292727100625110829949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918195151400416740553299 2877292727100625110829949)
                  ·
                    refine ⟨1078984772662734416561231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2877292727100625110829949 1078984772662734416561231)
                    ·
                      rfl

theorem cell22_3151973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_3151973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151973 prefixEnd_3151973 := by exact prefixLift 3151973
  have htrace : WordTrace (prefixWord ++ tailWord_3151973) baseStart_3151973 baseEnd_3151973 := by
    simpa [prefixWord, tailWord_3151973, baseEnd_3151973] using wordTrace_append hprefix tailTrace_3151973
  have hstable : (prefixWord ++ tailWord_3151973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151973).length < 2 ^ (prefixWord ++ tailWord_3151973).sum := by decide
  have hdescent : baseEnd_3151973 < baseStart_3151973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151982 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_3151982 : Nat := 118140960795 + 3151982 * 2 ^ 59
def prefixEnd_3151982 : Nat := 4983230072969 + 3 ^ 40 * 3151982 * 2
def baseEnd_3151982 : Nat := 1078987853546661393086203

theorem tailTrace_3151982 : CollatzResearch.WordTrace tailWord_3151982 prefixEnd_3151982 1078987853546661393086203 := by
  unfold tailWord_3151982
  simp only [CollatzResearch.WordTrace]
  refine ⟨14370278508364375564151275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76641485377943336342140133 14370278508364375564151275)
  ·
    refine ⟨21555417762546563346226913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14370278508364375564151275 21555417762546563346226913)
    ·
      refine ⟨16166563321909922509670185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21555417762546563346226913 16166563321909922509670185)
      ·
        refine ⟨12124922491432441882252639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16166563321909922509670185 12124922491432441882252639)
        ·
          refine ⟨18187383737148662823378959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12124922491432441882252639 18187383737148662823378959)
          ·
            refine ⟨27281075605722994235068439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18187383737148662823378959 27281075605722994235068439)
            ·
              refine ⟨40921613408584491352602659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27281075605722994235068439 40921613408584491352602659)
              ·
                refine ⟨61382420112876737028903989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40921613408584491352602659 61382420112876737028903989)
                ·
                  refine ⟨5754601885582194096459749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61382420112876737028903989 5754601885582194096459749)
                  ·
                    refine ⟨1078987853546661393086203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5754601885582194096459749 1078987853546661393086203)
                    ·
                      rfl

theorem cell22_3151982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_3151982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151982 prefixEnd_3151982 := by exact prefixLift 3151982
  have htrace : WordTrace (prefixWord ++ tailWord_3151982) baseStart_3151982 baseEnd_3151982 := by
    simpa [prefixWord, tailWord_3151982, baseEnd_3151982] using wordTrace_append hprefix tailTrace_3151982
  have hstable : (prefixWord ++ tailWord_3151982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151982).length < 2 ^ (prefixWord ++ tailWord_3151982).sum := by decide
  have hdescent : baseEnd_3151982 < baseStart_3151982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3151997 : List Nat := [1, 4, 1, 1, 3, 3, 1, 2, 6]
def baseStart_3151997 : Nat := 118140960795 + 3151997 * 2 ^ 59
def prefixEnd_3151997 : Nat := 4983230072969 + 3 ^ 40 * 3151997 * 2
def baseEnd_3151997 : Nat := 359664329451068784653719

theorem tailTrace_3151997 : CollatzResearch.WordTrace tailWord_3151997 prefixEnd_3151997 359664329451068784653719 := by
  unfold tailWord_3151997
  simp only [CollatzResearch.WordTrace]
  refine ⟨114962775161860662075006245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76641850107907108050004163 114962775161860662075006245)
  ·
    refine ⟨21555520342848874139063671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114962775161860662075006245 21555520342848874139063671)
    ·
      refine ⟨32333280514273311208595507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21555520342848874139063671 32333280514273311208595507)
      ·
        refine ⟨48499920771409966812893261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32333280514273311208595507 48499920771409966812893261)
        ·
          refine ⟨18187470289278737554834973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48499920771409966812893261 18187470289278737554834973)
          ·
            refine ⟨6820301358479526583063115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18187470289278737554834973 6820301358479526583063115)
            ·
              refine ⟨10230452037719289874594673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6820301358479526583063115 10230452037719289874594673)
              ·
                refine ⟨7672839028289467405946005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10230452037719289874594673 7672839028289467405946005)
                ·
                  refine ⟨359664329451068784653719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7672839028289467405946005 359664329451068784653719)
                  ·
                    rfl

theorem cell22_3151997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_3151997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3151997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3151997 prefixEnd_3151997 := by exact prefixLift 3151997
  have htrace : WordTrace (prefixWord ++ tailWord_3151997) baseStart_3151997 baseEnd_3151997 := by
    simpa [prefixWord, tailWord_3151997, baseEnd_3151997] using wordTrace_append hprefix tailTrace_3151997
  have hstable : (prefixWord ++ tailWord_3151997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3151997).length < 2 ^ (prefixWord ++ tailWord_3151997).sum := by decide
  have hdescent : baseEnd_3151997 < baseStart_3151997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3151997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152029 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_3152029 : Nat := 118140960795 + 3152029 * 2 ^ 59
def prefixEnd_3152029 : Nat := 4983230072969 + 3 ^ 40 * 3152029 * 2
def baseEnd_3152029 : Nat := 1079003942607168937161059

theorem tailTrace_3152029 : CollatzResearch.WordTrace tailWord_3152029 prefixEnd_3152029 1079003942607168937161059 := by
  unfold tailWord_3152029
  simp only [CollatzResearch.WordTrace]
  refine ⟨114963942297744731540171141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76642628198496487693447427 114963942297744731540171141)
  ·
    refine ⟨21555739180827137163782089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114963942297744731540171141 21555739180827137163782089)
    ·
      refine ⟨16166804385620352872836567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21555739180827137163782089 16166804385620352872836567)
      ·
        refine ⟨24250206578430529309254851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16166804385620352872836567 24250206578430529309254851)
        ·
          refine ⟨36375309867645793963882277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24250206578430529309254851 36375309867645793963882277)
          ·
            refine ⟨6820370600183586368227927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36375309867645793963882277 6820370600183586368227927)
            ·
              refine ⟨10230555900275379552341891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6820370600183586368227927 10230555900275379552341891)
              ·
                refine ⟨15345833850413069328512837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10230555900275379552341891 15345833850413069328512837)
                ·
                  refine ⟨2877343846952450499096157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15345833850413069328512837 2877343846952450499096157)
                  ·
                    refine ⟨1079003942607168937161059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2877343846952450499096157 1079003942607168937161059)
                    ·
                      rfl

theorem cell22_3152029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_3152029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152029 prefixEnd_3152029 := by exact prefixLift 3152029
  have htrace : WordTrace (prefixWord ++ tailWord_3152029) baseStart_3152029 baseEnd_3152029 := by
    simpa [prefixWord, tailWord_3152029, baseEnd_3152029] using wordTrace_append hprefix tailTrace_3152029
  have hstable : (prefixWord ++ tailWord_3152029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152029).length < 2 ^ (prefixWord ++ tailWord_3152029).sum := by decide
  have hdescent : baseEnd_3152029 < baseStart_3152029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152065 : List Nat := [1, 2, 6, 1, 3, 1, 1, 3, 4]
def baseStart_3152065 : Nat := 118140960795 + 3152065 * 2 ^ 59
def prefixEnd_3152065 : Nat := 4983230072969 + 3 ^ 40 * 3152065 * 2
def baseEnd_3152065 : Nat := 359672088714292281086983

theorem tailTrace_3152065 : CollatzResearch.WordTrace tailWord_3152065 prefixEnd_3152065 359672088714292281086983 := by
  unfold tailWord_3152065
  simp only [CollatzResearch.WordTrace]
  refine ⟨114965255325614309688481649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76643503550409539792321099 114965255325614309688481649)
  ·
    refine ⟨86223941494210732266361237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114965255325614309688481649 86223941494210732266361237)
    ·
      refine ⟨4041747257541128074985683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86223941494210732266361237 4041747257541128074985683)
      ·
        refine ⟨6062620886311692112478525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4041747257541128074985683 6062620886311692112478525)
        ·
          refine ⟨2273482832366884542179447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6062620886311692112478525 2273482832366884542179447)
          ·
            refine ⟨3410224248550326813269171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273482832366884542179447 3410224248550326813269171)
            ·
              refine ⟨5115336372825490219903757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410224248550326813269171 5115336372825490219903757)
              ·
                refine ⟨1918251139809558832463909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5115336372825490219903757 1918251139809558832463909)
                ·
                  refine ⟨359672088714292281086983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1918251139809558832463909 359672088714292281086983)
                  ·
                    rfl

theorem cell22_3152065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3, 4].length) (baseStart_3152065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152065 prefixEnd_3152065 := by exact prefixLift 3152065
  have htrace : WordTrace (prefixWord ++ tailWord_3152065) baseStart_3152065 baseEnd_3152065 := by
    simpa [prefixWord, tailWord_3152065, baseEnd_3152065] using wordTrace_append hprefix tailTrace_3152065
  have hstable : (prefixWord ++ tailWord_3152065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152065).length < 2 ^ (prefixWord ++ tailWord_3152065).sum := by decide
  have hdescent : baseEnd_3152065 < baseStart_3152065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152076 : List Nat := [2, 2, 1, 6, 2, 1, 8]
def baseStart_3152076 : Nat := 118140960795 + 3152076 * 2 ^ 59
def prefixEnd_3152076 : Nat := 4983230072969 + 3 ^ 40 * 3152076 * 2
def baseEnd_3152076 : Nat := 39963704876580610416145

theorem tailTrace_3152076 : CollatzResearch.WordTrace tailWord_3152076 prefixEnd_3152076 39963704876580610416145 := by
  unfold tailWord_3152076
  simp only [CollatzResearch.WordTrace]
  refine ⟨57482828264287229283566041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76643771019049639044754721 57482828264287229283566041)
  ·
    refine ⟨43112121198215421962674531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57482828264287229283566041 43112121198215421962674531)
    ·
      refine ⟨64668181797323132944011797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43112121198215421962674531 64668181797323132944011797)
      ·
        refine ⟨3031321021749521856750553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64668181797323132944011797 3031321021749521856750553)
        ·
          refine ⟨2273490766312141392562915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3031321021749521856750553 2273490766312141392562915)
          ·
            refine ⟨3410236149468212088844373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273490766312141392562915 3410236149468212088844373)
            ·
              refine ⟨39963704876580610416145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3410236149468212088844373 39963704876580610416145)
              ·
                rfl

theorem cell22_3152076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 8].length) (baseStart_3152076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152076 prefixEnd_3152076 := by exact prefixLift 3152076
  have htrace : WordTrace (prefixWord ++ tailWord_3152076) baseStart_3152076 baseEnd_3152076 := by
    simpa [prefixWord, tailWord_3152076, baseEnd_3152076] using wordTrace_append hprefix tailTrace_3152076
  have hstable : (prefixWord ++ tailWord_3152076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152076).length < 2 ^ (prefixWord ++ tailWord_3152076).sum := by decide
  have hdescent : baseEnd_3152076 < baseStart_3152076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152087 : List Nat := [1, 1, 3, 2, 1, 2, 1, 6, 5]
def baseStart_3152087 : Nat := 118140960795 + 3152087 * 2 ^ 59
def prefixEnd_3152087 : Nat := 4983230072969 + 3 ^ 40 * 3152087 * 2
def baseEnd_3152087 : Nat := 359674599064158706403627

theorem tailTrace_3152087 : CollatzResearch.WordTrace tailWord_3152087 prefixEnd_3152087 359674599064158706403627 := by
  unfold tailWord_3152087
  simp only [CollatzResearch.WordTrace]
  refine ⟨114966057731534607445782515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76644038487689738297188343 114966057731534607445782515)
  ·
    refine ⟨172449086597301911168673773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114966057731534607445782515 172449086597301911168673773)
    ·
      refine ⟨64668407473988216688252665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172449086597301911168673773 64668407473988216688252665)
      ·
        refine ⟨48501305605491162516189499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64668407473988216688252665 48501305605491162516189499)
        ·
          refine ⟨72751958408236743774284249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48501305605491162516189499 72751958408236743774284249)
          ·
            refine ⟨54563968806177557830713187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72751958408236743774284249 54563968806177557830713187)
            ·
              refine ⟨81845953209266336746069781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54563968806177557830713187 81845953209266336746069781)
              ·
                refine ⟨3836529056684359534972021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81845953209266336746069781 3836529056684359534972021)
                ·
                  refine ⟨359674599064158706403627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3836529056684359534972021 359674599064158706403627)
                  ·
                    rfl

theorem cell22_3152087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 5].length) (baseStart_3152087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152087 prefixEnd_3152087 := by exact prefixLift 3152087
  have htrace : WordTrace (prefixWord ++ tailWord_3152087) baseStart_3152087 baseEnd_3152087 := by
    simpa [prefixWord, tailWord_3152087, baseEnd_3152087] using wordTrace_append hprefix tailTrace_3152087
  have hstable : (prefixWord ++ tailWord_3152087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152087).length < 2 ^ (prefixWord ++ tailWord_3152087).sum := by decide
  have hdescent : baseEnd_3152087 < baseStart_3152087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152104 : List Nat := [2, 1, 4, 1, 2, 3, 1, 3, 5]
def baseStart_3152104 : Nat := 118140960795 + 3152104 * 2 ^ 59
def prefixEnd_3152104 : Nat := 4983230072969 + 3 ^ 40 * 3152104 * 2
def baseEnd_3152104 : Nat := 359676538879964580511943

theorem tailTrace_3152104 : CollatzResearch.WordTrace tailWord_3152104 prefixEnd_3152104 359676538879964580511943 := by
  unfold tailWord_3152104
  simp only [CollatzResearch.WordTrace]
  refine ⟨57483338886236509674575683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76644451848315346232767577 57483338886236509674575683)
  ·
    refine ⟨86225008329354764511863525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57483338886236509674575683 86225008329354764511863525)
    ·
      refine ⟨16167189061754018345974411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86225008329354764511863525 16167189061754018345974411)
      ·
        refine ⟨24250783592631027518961617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16167189061754018345974411 24250783592631027518961617)
        ·
          refine ⟨18188087694473270639221213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24250783592631027518961617 18188087694473270639221213)
          ·
            refine ⟨6820532885427476489707955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18188087694473270639221213 6820532885427476489707955)
            ·
              refine ⟨10230799328141214734561933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6820532885427476489707955 10230799328141214734561933)
              ·
                refine ⟨3836549748052955525460725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10230799328141214734561933 3836549748052955525460725)
                ·
                  refine ⟨359676538879964580511943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3836549748052955525460725 359676538879964580511943)
                  ·
                    rfl

theorem cell22_3152104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 3, 5].length) (baseStart_3152104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152104 prefixEnd_3152104 := by exact prefixLift 3152104
  have htrace : WordTrace (prefixWord ++ tailWord_3152104) baseStart_3152104 baseEnd_3152104 := by
    simpa [prefixWord, tailWord_3152104, baseEnd_3152104] using wordTrace_append hprefix tailTrace_3152104
  have hstable : (prefixWord ++ tailWord_3152104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152104).length < 2 ^ (prefixWord ++ tailWord_3152104).sum := by decide
  have hdescent : baseEnd_3152104 < baseStart_3152104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152164 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_3152164 : Nat := 118140960795 + 3152164 * 2 ^ 59
def prefixEnd_3152164 : Nat := 4983230072969 + 3 ^ 40 * 3152164 * 2
def baseEnd_3152164 : Nat := 1079050155866073585035645

theorem tailTrace_3152164 : CollatzResearch.WordTrace tailWord_3152164 prefixEnd_3152164 1079050155866073585035645 := by
  unfold tailWord_3152164
  simp only [CollatzResearch.WordTrace]
  refine ⟨57484433076127824798167773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76645910768170433064223697 57484433076127824798167773)
  ·
    refine ⟨21556662403547934299312915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57484433076127824798167773 21556662403547934299312915)
    ·
      refine ⟨32334993605321901448969373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21556662403547934299312915 32334993605321901448969373)
      ·
        refine ⟨12125622601995713043363515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32334993605321901448969373 12125622601995713043363515)
        ·
          refine ⟨18188433902993569565045273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12125622601995713043363515 18188433902993569565045273)
          ·
            refine ⟨13641325427245177173783955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18188433902993569565045273 13641325427245177173783955)
            ·
              refine ⟨20461988140867765760675933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13641325427245177173783955 20461988140867765760675933)
              ·
                refine ⟨7673245552825412160253475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20461988140867765760675933 7673245552825412160253475)
                ·
                  refine ⟨11509868329238118240380213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7673245552825412160253475 11509868329238118240380213)
                  ·
                    refine ⟨1079050155866073585035645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11509868329238118240380213 1079050155866073585035645)
                    ·
                      rfl

theorem cell22_3152164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_3152164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152164 prefixEnd_3152164 := by exact prefixLift 3152164
  have htrace : WordTrace (prefixWord ++ tailWord_3152164) baseStart_3152164 baseEnd_3152164 := by
    simpa [prefixWord, tailWord_3152164, baseEnd_3152164] using wordTrace_append hprefix tailTrace_3152164
  have hstable : (prefixWord ++ tailWord_3152164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152164).length < 2 ^ (prefixWord ++ tailWord_3152164).sum := by decide
  have hdescent : baseEnd_3152164 < baseStart_3152164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152207 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 2, 6]
def baseStart_3152207 : Nat := 118140960795 + 3152207 * 2 ^ 59
def prefixEnd_3152207 : Nat := 4983230072969 + 3 ^ 40 * 3152207 * 2
def baseEnd_3152207 : Nat := 1079064875644835806210513

theorem tailTrace_3152207 : CollatzResearch.WordTrace tailWord_3152207 prefixEnd_3152207 1079064875644835806210513 := by
  unfold tailWord_3152207
  simp only [CollatzResearch.WordTrace]
  refine ⟨114970434491099867940150875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76646956327399911960100583 114970434491099867940150875)
  ·
    refine ⟨172455651736649801910226313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114970434491099867940150875 172455651736649801910226313)
    ·
      refine ⟨129341738802487351432669735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172455651736649801910226313 129341738802487351432669735)
      ·
        refine ⟨194012608203731027149004603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129341738802487351432669735 194012608203731027149004603)
        ·
          refine ⟨291018912305596540723506905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194012608203731027149004603 291018912305596540723506905)
          ·
            refine ⟨218264184229197405542630179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291018912305596540723506905 218264184229197405542630179)
            ·
              refine ⟨327396276343796108313945269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218264184229197405542630179 327396276343796108313945269)
              ·
                refine ⟨30693400907230885154432369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 327396276343796108313945269 30693400907230885154432369)
                ·
                  refine ⟨23020050680423163865824277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30693400907230885154432369 23020050680423163865824277)
                  ·
                    refine ⟨1079064875644835806210513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23020050680423163865824277 1079064875644835806210513)
                    ·
                      rfl

theorem cell22_3152207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_3152207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152207 prefixEnd_3152207 := by exact prefixLift 3152207
  have htrace : WordTrace (prefixWord ++ tailWord_3152207) baseStart_3152207 baseEnd_3152207 := by
    simpa [prefixWord, tailWord_3152207, baseEnd_3152207] using wordTrace_append hprefix tailTrace_3152207
  have hstable : (prefixWord ++ tailWord_3152207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152207).length < 2 ^ (prefixWord ++ tailWord_3152207).sum := by decide
  have hdescent : baseEnd_3152207 < baseStart_3152207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152260 : List Nat := [2, 3, 2, 1, 1, 2, 5, 2, 1, 3]
def baseStart_3152260 : Nat := 118140960795 + 3152260 * 2 ^ 59
def prefixEnd_3152260 : Nat := 4983230072969 + 3 ^ 40 * 3152260 * 2
def baseEnd_3152260 : Nat := 1079083018627961334635351

theorem tailTrace_3152260 : CollatzResearch.WordTrace tailWord_3152260 prefixEnd_3152260 1079083018627961334635351 := by
  unfold tailWord_3152260
  simp only [CollatzResearch.WordTrace]
  refine ⟨57486183779953928995915117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76648245039938571994553489 57486183779953928995915117)
  ·
    refine ⟨21557318917482723373468169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57486183779953928995915117 21557318917482723373468169)
    ·
      refine ⟨16167989188112042530101127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21557318917482723373468169 16167989188112042530101127)
      ·
        refine ⟨24251983782168063795151691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16167989188112042530101127 24251983782168063795151691)
        ·
          refine ⟨36377975673252095692727537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24251983782168063795151691 36377975673252095692727537)
          ·
            refine ⟨27283481754939071769545653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36377975673252095692727537 27283481754939071769545653)
            ·
              refine ⟨2557826414525537978394905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27283481754939071769545653 2557826414525537978394905)
              ·
                refine ⟨1918369810894153483796179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2557826414525537978394905 1918369810894153483796179)
                ·
                  refine ⟨2877554716341230225694269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918369810894153483796179 2877554716341230225694269)
                  ·
                    refine ⟨1079083018627961334635351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2877554716341230225694269 1079083018627961334635351)
                    ·
                      rfl

theorem cell22_3152260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_3152260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152260 prefixEnd_3152260 := by exact prefixLift 3152260
  have htrace : WordTrace (prefixWord ++ tailWord_3152260) baseStart_3152260 baseEnd_3152260 := by
    simpa [prefixWord, tailWord_3152260, baseEnd_3152260] using wordTrace_append hprefix tailTrace_3152260
  have hstable : (prefixWord ++ tailWord_3152260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152260).length < 2 ^ (prefixWord ++ tailWord_3152260).sum := by decide
  have hdescent : baseEnd_3152260 < baseStart_3152260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152329 : List Nat := [1, 2, 1, 1, 2, 1, 7, 7]
def baseStart_3152329 : Nat := 118140960795 + 3152329 * 2 ^ 59
def prefixEnd_3152329 : Nat := 4983230072969 + 3 ^ 40 * 3152329 * 2
def baseEnd_3152329 : Nat := 119900737637563128295571

theorem tailTrace_3152329 : CollatzResearch.WordTrace tailWord_3152329 prefixEnd_3152329 119900737637563128295571 := by
  unfold tailWord_3152329
  simp only [CollatzResearch.WordTrace]
  refine ⟨114974884196657882776092041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76649922797771921850728027 114974884196657882776092041)
  ·
    refine ⟨86231163147493412082069031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114974884196657882776092041 86231163147493412082069031)
    ·
      refine ⟨129346744721240118123103547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86231163147493412082069031 129346744721240118123103547)
      ·
        refine ⟨194020117081860177184655321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129346744721240118123103547 194020117081860177184655321)
        ·
          refine ⟨145515087811395132888491491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194020117081860177184655321 145515087811395132888491491)
          ·
            refine ⟨218272631717092699332737237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145515087811395132888491491 218272631717092699332737237)
            ·
              refine ⟨5115764805869360140611029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 218272631717092699332737237 5115764805869360140611029)
              ·
                refine ⟨119900737637563128295571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5115764805869360140611029 119900737637563128295571)
                ·
                  rfl

theorem cell22_3152329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 7].length) (baseStart_3152329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152329 prefixEnd_3152329 := by exact prefixLift 3152329
  have htrace : WordTrace (prefixWord ++ tailWord_3152329) baseStart_3152329 baseEnd_3152329 := by
    simpa [prefixWord, tailWord_3152329, baseEnd_3152329] using wordTrace_append hprefix tailTrace_3152329
  have hstable : (prefixWord ++ tailWord_3152329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152329).length < 2 ^ (prefixWord ++ tailWord_3152329).sum := by decide
  have hdescent : baseEnd_3152329 < baseStart_3152329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152346 : List Nat := [3, 1, 1, 2, 3, 1, 5, 6]
def baseStart_3152346 : Nat := 118140960795 + 3152346 * 2 ^ 59
def prefixEnd_3152346 : Nat := 4983230072969 + 3 ^ 40 * 3152346 * 2
def baseEnd_3152346 : Nat := 119901384242831752998343

theorem tailTrace_3152346 : CollatzResearch.WordTrace tailWord_3152346 prefixEnd_3152346 119901384242831752998343 := by
  unfold tailWord_3152346
  simp only [CollatzResearch.WordTrace]
  refine ⟨28743876059399073669865223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76650336158397529786307261 28743876059399073669865223)
  ·
    refine ⟨43115814089098610504797835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28743876059399073669865223 43115814089098610504797835)
    ·
      refine ⟨64673721133647915757196753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43115814089098610504797835 64673721133647915757196753)
      ·
        refine ⟨48505290850235936817897565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64673721133647915757196753 48505290850235936817897565)
        ·
          refine ⟨18189484068838476306711587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48505290850235936817897565 18189484068838476306711587)
          ·
            refine ⟨27284226103257714460067381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18189484068838476306711587 27284226103257714460067381)
            ·
              refine ⟨2557896197180410730631317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27284226103257714460067381 2557896197180410730631317)
              ·
                refine ⟨119901384242831752998343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2557896197180410730631317 119901384242831752998343)
                ·
                  rfl

theorem cell22_3152346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 6].length) (baseStart_3152346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152346 prefixEnd_3152346 := by exact prefixLift 3152346
  have htrace : WordTrace (prefixWord ++ tailWord_3152346) baseStart_3152346 baseEnd_3152346 := by
    simpa [prefixWord, tailWord_3152346, baseEnd_3152346] using wordTrace_append hprefix tailTrace_3152346
  have hstable : (prefixWord ++ tailWord_3152346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152346).length < 2 ^ (prefixWord ++ tailWord_3152346).sum := by decide
  have hdescent : baseEnd_3152346 < baseStart_3152346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152354 : List Nat := [3, 3, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3152354 : Nat := 118140960795 + 3152354 * 2 ^ 59
def prefixEnd_3152354 : Nat := 4983230072969 + 3 ^ 40 * 3152354 * 2
def baseEnd_3152354 : Nat := 1079115196748976422785063

theorem tailTrace_3152354 : CollatzResearch.WordTrace tailWord_3152354 prefixEnd_3152354 1079115196748976422785063 := by
  unfold tailWord_3152354
  simp only [CollatzResearch.WordTrace]
  refine ⟨28743949005391828011438029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76650530681044874697168077 28743949005391828011438029)
  ·
    refine ⟨10778980877021935504289261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28743949005391828011438029 10778980877021935504289261)
    ·
      refine ⟨4042117828883225814108473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10778980877021935504289261 4042117828883225814108473)
      ·
        refine ⟨3031588371662419360581355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4042117828883225814108473 3031588371662419360581355)
        ·
          refine ⟨4547382557493629040872033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3031588371662419360581355 4547382557493629040872033)
          ·
            refine ⟨3410536918120221780654025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4547382557493629040872033 3410536918120221780654025)
            ·
              refine ⟨2557902688590166335490519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3410536918120221780654025 2557902688590166335490519)
              ·
                refine ⟨3836854032885249503235779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2557902688590166335490519 3836854032885249503235779)
                ·
                  refine ⟨5755281049327874254853669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836854032885249503235779 5755281049327874254853669)
                  ·
                    refine ⟨1079115196748976422785063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5755281049327874254853669 1079115196748976422785063)
                    ·
                      rfl

theorem cell22_3152354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3152354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152354 prefixEnd_3152354 := by exact prefixLift 3152354
  have htrace : WordTrace (prefixWord ++ tailWord_3152354) baseStart_3152354 baseEnd_3152354 := by
    simpa [prefixWord, tailWord_3152354, baseEnd_3152354] using wordTrace_append hprefix tailTrace_3152354
  have hstable : (prefixWord ++ tailWord_3152354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152354).length < 2 ^ (prefixWord ++ tailWord_3152354).sum := by decide
  have hdescent : baseEnd_3152354 < baseStart_3152354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152397 : List Nat := [1, 7, 1, 1, 1, 3, 2, 6]
def baseStart_3152397 : Nat := 118140960795 + 3152397 * 2 ^ 59
def prefixEnd_3152397 : Nat := 4983230072969 + 3 ^ 40 * 3152397 * 2
def baseEnd_3152397 : Nat := 119903324058637627106659

theorem tailTrace_3152397 : CollatzResearch.WordTrace tailWord_3152397 prefixEnd_3152397 119903324058637627106659 := by
  unfold tailWord_3152397
  simp only [CollatzResearch.WordTrace]
  refine ⟨114977364360411530389567445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76651576240274353593044963 114977364360411530389567445)
  ·
    refine ⟨2694781977197145243505487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 114977364360411530389567445 2694781977197145243505487)
    ·
      refine ⟨4042172965795717865258231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2694781977197145243505487 4042172965795717865258231)
      ·
        refine ⟨6063259448693576797887347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4042172965795717865258231 6063259448693576797887347)
        ·
          refine ⟨9094889173040365196831021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6063259448693576797887347 9094889173040365196831021)
          ·
            refine ⟨3410583439890136948811633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9094889173040365196831021 3410583439890136948811633)
            ·
              refine ⟨2557937579917602711608725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3410583439890136948811633 2557937579917602711608725)
              ·
                refine ⟨119903324058637627106659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2557937579917602711608725 119903324058637627106659)
                ·
                  rfl

theorem cell22_3152397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 6].length) (baseStart_3152397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152397 prefixEnd_3152397 := by exact prefixLift 3152397
  have htrace : WordTrace (prefixWord ++ tailWord_3152397) baseStart_3152397 baseEnd_3152397 := by
    simpa [prefixWord, tailWord_3152397, baseEnd_3152397] using wordTrace_append hprefix tailTrace_3152397
  have hstable : (prefixWord ++ tailWord_3152397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152397).length < 2 ^ (prefixWord ++ tailWord_3152397).sum := by decide
  have hdescent : baseEnd_3152397 < baseStart_3152397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152412 : List Nat := [2, 2, 3, 1, 2, 4, 1, 3, 1, 3]
def baseStart_3152412 : Nat := 118140960795 + 3152412 * 2 ^ 59
def prefixEnd_3152412 : Nat := 4983230072969 + 3 ^ 40 * 3152412 * 2
def baseEnd_3152412 : Nat := 1079135051334283604834885

theorem tailTrace_3152412 : CollatzResearch.WordTrace tailWord_3152412 prefixEnd_3152412 1079135051334283604834885 := by
  unfold tailWord_3152412
  simp only [CollatzResearch.WordTrace]
  refine ⟨57488955727678593975681745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76651940970238125300908993 57488955727678593975681745)
  ·
    refine ⟨43116716795758945481761309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57488955727678593975681745 43116716795758945481761309)
    ·
      refine ⟨16168768798409604555660491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43116716795758945481761309 16168768798409604555660491)
      ·
        refine ⟨24253153197614406833490737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16168768798409604555660491 24253153197614406833490737)
        ·
          refine ⟨18189864898210805125118053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24253153197614406833490737 18189864898210805125118053)
          ·
            refine ⟨3410599668414525960959635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18189864898210805125118053 3410599668414525960959635)
            ·
              refine ⟨5115899502621788941439453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410599668414525960959635 5115899502621788941439453)
              ·
                refine ⟨1918462313483170853039795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5115899502621788941439453 1918462313483170853039795)
                ·
                  refine ⟨2877693470224756279559693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918462313483170853039795 2877693470224756279559693)
                  ·
                    refine ⟨1079135051334283604834885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2877693470224756279559693 1079135051334283604834885)
                    ·
                      rfl

theorem cell22_3152412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_3152412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152412 prefixEnd_3152412 := by exact prefixLift 3152412
  have htrace : WordTrace (prefixWord ++ tailWord_3152412) baseStart_3152412 baseEnd_3152412 := by
    simpa [prefixWord, tailWord_3152412, baseEnd_3152412] using wordTrace_append hprefix tailTrace_3152412
  have hstable : (prefixWord ++ tailWord_3152412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152412).length < 2 ^ (prefixWord ++ tailWord_3152412).sum := by decide
  have hdescent : baseEnd_3152412 < baseStart_3152412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152455 : List Nat := [1, 1, 4, 1, 4, 3, 1, 2, 1, 4]
def baseStart_3152455 : Nat := 118140960795 + 3152455 * 2 ^ 59
def prefixEnd_3152455 : Nat := 4983230072969 + 3 ^ 40 * 3152455 * 2
def baseEnd_3152455 : Nat := 1079149771113045826009753

theorem tailTrace_3152455 : CollatzResearch.WordTrace tailWord_3152455 prefixEnd_3152455 1079149771113045826009753 := by
  unfold tailWord_3152455
  simp only [CollatzResearch.WordTrace]
  refine ⟨114979479794201406295178819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76652986529467604196785879 114979479794201406295178819)
  ·
    refine ⟨172469219691302109442768229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114979479794201406295178819 172469219691302109442768229)
    ·
      refine ⟨32337978692119145520519043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172469219691302109442768229 32337978692119145520519043)
      ·
        refine ⟨48506968038178718280778565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32337978692119145520519043 48506968038178718280778565)
        ·
          refine ⟨9095056507158509677645981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48506968038178718280778565 9095056507158509677645981)
          ·
            refine ⟨3410646190184441129117243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9095056507158509677645981 3410646190184441129117243)
            ·
              refine ⟨5115969285276661693675865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410646190184441129117243 5115969285276661693675865)
              ·
                refine ⟨3836976963957496270256899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5115969285276661693675865 3836976963957496270256899)
                ·
                  refine ⟨5755465445936244405385349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836976963957496270256899 5755465445936244405385349)
                  ·
                    refine ⟨1079149771113045826009753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5755465445936244405385349 1079149771113045826009753)
                    ·
                      rfl

theorem cell22_3152455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_3152455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152455 prefixEnd_3152455 := by exact prefixLift 3152455
  have htrace : WordTrace (prefixWord ++ tailWord_3152455) baseStart_3152455 baseEnd_3152455 := by
    simpa [prefixWord, tailWord_3152455, baseEnd_3152455] using wordTrace_append hprefix tailTrace_3152455
  have hstable : (prefixWord ++ tailWord_3152455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152455).length < 2 ^ (prefixWord ++ tailWord_3152455).sum := by decide
  have hdescent : baseEnd_3152455 < baseStart_3152455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152468 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3152468 : Nat := 118140960795 + 3152468 * 2 ^ 59
def prefixEnd_3152468 : Nat := 4983230072969 + 3 ^ 40 * 3152468 * 2
def baseEnd_3152468 : Nat := 1079154221278718125434713

theorem tailTrace_3152468 : CollatzResearch.WordTrace tailWord_3152468 prefixEnd_3152468 1079154221278718125434713 := by
  unfold tailWord_3152468
  simp only [CollatzResearch.WordTrace]
  refine ⟨57489976971577154757701029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76653302628769539676934705 57489976971577154757701029)
  ·
    refine ⟨10779370682170716517068943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57489976971577154757701029 10779370682170716517068943)
    ·
      refine ⟨16169056023256074775603415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10779370682170716517068943 16169056023256074775603415)
      ·
        refine ⟨24253584034884112163405123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16169056023256074775603415 24253584034884112163405123)
        ·
          refine ⟨36380376052326168245107685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24253584034884112163405123 36380376052326168245107685)
          ·
            refine ⟨6821320509811156545957691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36380376052326168245107685 6821320509811156545957691)
            ·
              refine ⟨10231980764716734818936537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6821320509811156545957691 10231980764716734818936537)
              ·
                refine ⟨7673985573537551114202403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10231980764716734818936537 7673985573537551114202403)
                ·
                  refine ⟨11510978360306326671303605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7673985573537551114202403 11510978360306326671303605)
                  ·
                    refine ⟨1079154221278718125434713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11510978360306326671303605 1079154221278718125434713)
                    ·
                      rfl

theorem cell22_3152468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3152468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152468 prefixEnd_3152468 := by exact prefixLift 3152468
  have htrace : WordTrace (prefixWord ++ tailWord_3152468) baseStart_3152468 baseEnd_3152468 := by
    simpa [prefixWord, tailWord_3152468, baseEnd_3152468] using wordTrace_append hprefix tailTrace_3152468
  have hstable : (prefixWord ++ tailWord_3152468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152468).length < 2 ^ (prefixWord ++ tailWord_3152468).sum := by decide
  have hdescent : baseEnd_3152468 < baseStart_3152468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152590 : List Nat := [4, 1, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_3152590 : Nat := 118140960795 + 3152590 * 2 ^ 59
def prefixEnd_3152590 : Nat := 4983230072969 + 3 ^ 40 * 3152590 * 2
def baseEnd_3152590 : Nat := 1079195984371950473884339

theorem tailTrace_3152590 : CollatzResearch.WordTrace tailWord_3152590 prefixEnd_3152590 1079195984371950473884339 := by
  unfold tailWord_3152590
  simp only [CollatzResearch.WordTrace]
  refine ⟨14373050456089040543917903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76656269099141549567562149 14373050456089040543917903)
  ·
    refine ⟨21559575684133560815876855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14373050456089040543917903 21559575684133560815876855)
    ·
      refine ⟨32339363526200341223815283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21559575684133560815876855 32339363526200341223815283)
      ·
        refine ⟨48509045289300511835722925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32339363526200341223815283 48509045289300511835722925)
        ·
          refine ⟨18190891983487691938396097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48509045289300511835722925 18190891983487691938396097)
          ·
            refine ⟨13643168987615768953797073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18190891983487691938396097 13643168987615768953797073)
            ·
              refine ⟨10232376740711826715347805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13643168987615768953797073 10232376740711826715347805)
              ·
                refine ⟨3837141277766935018255427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10232376740711826715347805 3837141277766935018255427)
                ·
                  refine ⟨5755711916650402527383141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837141277766935018255427 5755711916650402527383141)
                  ·
                    refine ⟨1079195984371950473884339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5755711916650402527383141 1079195984371950473884339)
                    ·
                      rfl

theorem cell22_3152590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_3152590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152590 prefixEnd_3152590 := by exact prefixLift 3152590
  have htrace : WordTrace (prefixWord ++ tailWord_3152590) baseStart_3152590 baseEnd_3152590 := by
    simpa [prefixWord, tailWord_3152590, baseEnd_3152590] using wordTrace_append hprefix tailTrace_3152590
  have hstable : (prefixWord ++ tailWord_3152590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152590).length < 2 ^ (prefixWord ++ tailWord_3152590).sum := by decide
  have hdescent : baseEnd_3152590 < baseStart_3152590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152618 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_3152618 : Nat := 118140960795 + 3152618 * 2 ^ 59
def prefixEnd_3152618 : Nat := 4983230072969 + 3 ^ 40 * 3152618 * 2
def baseEnd_3152618 : Nat := 1079205569344167734184253

theorem tailTrace_3152618 : CollatzResearch.WordTrace tailWord_3152618 prefixEnd_3152618 1079205569344167734184253 := by
  unfold tailWord_3152618
  simp only [CollatzResearch.WordTrace]
  refine ⟨28746356223152721283340627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76656949928407256755575005 28746356223152721283340627)
  ·
    refine ⟨43119534334729081925010941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28746356223152721283340627 43119534334729081925010941)
    ·
      refine ⟨16169825375523405721879103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43119534334729081925010941 16169825375523405721879103)
      ·
        refine ⟨24254738063285108582818655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16169825375523405721879103 24254738063285108582818655)
        ·
          refine ⟨36382107094927662874227983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24254738063285108582818655 36382107094927662874227983)
          ·
            refine ⟨54573160642391494311341975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36382107094927662874227983 54573160642391494311341975)
            ·
              refine ⟨81859740963587241467012963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54573160642391494311341975 81859740963587241467012963)
              ·
                refine ⟨122789611445380862200519445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81859740963587241467012963 122789611445380862200519445)
                ·
                  refine ⟨5755763036502227915649349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122789611445380862200519445 5755763036502227915649349)
                  ·
                    refine ⟨1079205569344167734184253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5755763036502227915649349 1079205569344167734184253)
                    ·
                      rfl

theorem cell22_3152618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_3152618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152618 prefixEnd_3152618 := by exact prefixLift 3152618
  have htrace : WordTrace (prefixWord ++ tailWord_3152618) baseStart_3152618 baseEnd_3152618 := by
    simpa [prefixWord, tailWord_3152618, baseEnd_3152618] using wordTrace_append hprefix tailTrace_3152618
  have hstable : (prefixWord ++ tailWord_3152618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152618).length < 2 ^ (prefixWord ++ tailWord_3152618).sum := by decide
  have hdescent : baseEnd_3152618 < baseStart_3152618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152740 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 6]
def baseStart_3152740 : Nat := 118140960795 + 3152740 * 2 ^ 59
def prefixEnd_3152740 : Nat := 4983230072969 + 3 ^ 40 * 3152740 * 2
def baseEnd_3152740 : Nat := 359749110812466694211293

theorem tailTrace_3152740 : CollatzResearch.WordTrace tailWord_3152740 prefixEnd_3152740 359749110812466694211293 := by
  unfold tailWord_3152740
  simp only [CollatzResearch.WordTrace]
  refine ⟨57494937299084449984651837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76659916398779266646202449 57494937299084449984651837)
  ·
    refine ⟨21560601487156668744244439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57494937299084449984651837 21560601487156668744244439)
    ·
      refine ⟨32340902230735003116366659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21560601487156668744244439 32340902230735003116366659)
      ·
        refine ⟨48511353346102504674549989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32340902230735003116366659 48511353346102504674549989)
        ·
          refine ⟨9095878752394219626478123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48511353346102504674549989 9095878752394219626478123)
          ·
            refine ⟨13643818128591329439717185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9095878752394219626478123 13643818128591329439717185)
            ·
              refine ⟨10232863596443497079787889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13643818128591329439717185 10232863596443497079787889)
              ·
                refine ⟨7674647697332622809840917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10232863596443497079787889 7674647697332622809840917)
                ·
                  refine ⟨359749110812466694211293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7674647697332622809840917 359749110812466694211293)
                  ·
                    rfl

theorem cell22_3152740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_3152740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152740 prefixEnd_3152740 := by exact prefixLift 3152740
  have htrace : WordTrace (prefixWord ++ tailWord_3152740) baseStart_3152740 baseEnd_3152740 := by
    simpa [prefixWord, tailWord_3152740, baseEnd_3152740] using wordTrace_append hprefix tailTrace_3152740
  have hstable : (prefixWord ++ tailWord_3152740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152740).length < 2 ^ (prefixWord ++ tailWord_3152740).sum := by decide
  have hdescent : baseEnd_3152740 < baseStart_3152740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152755 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 4, 3]
def baseStart_3152755 : Nat := 118140960795 + 3152755 * 2 ^ 59
def prefixEnd_3152755 : Nat := 4983230072969 + 3 ^ 40 * 3152755 * 2
def baseEnd_3152755 : Nat := 1079252467243945043508833

theorem tailTrace_3152755 : CollatzResearch.WordTrace tailWord_3152755 prefixEnd_3152755 1079252467243945043508833 := by
  unfold tailWord_3152755
  simp only [CollatzResearch.WordTrace]
  refine ⟨114990421693114557531099719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76660281128743038354066479 114990421693114557531099719)
  ·
    refine ⟨172485632539671836296649579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114990421693114557531099719 172485632539671836296649579)
    ·
      refine ⟨258728448809507754444974369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172485632539671836296649579 258728448809507754444974369)
      ·
        refine ⟨194046336607130815833730777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258728448809507754444974369 194046336607130815833730777)
        ·
          refine ⟨145534752455348111875298083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194046336607130815833730777 145534752455348111875298083)
          ·
            refine ⟨218302128683022167812947125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145534752455348111875298083 218302128683022167812947125)
            ·
              refine ⟨20465824564033328232463793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 218302128683022167812947125 20465824564033328232463793)
              ·
                refine ⟨15349368423024996174347845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20465824564033328232463793 15349368423024996174347845)
                ·
                  refine ⟨2878006579317186782690221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15349368423024996174347845 2878006579317186782690221)
                  ·
                    refine ⟨1079252467243945043508833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2878006579317186782690221 1079252467243945043508833)
                    ·
                      rfl

theorem cell22_3152755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 3].length) (baseStart_3152755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152755 prefixEnd_3152755 := by exact prefixLift 3152755
  have htrace : WordTrace (prefixWord ++ tailWord_3152755) baseStart_3152755 baseEnd_3152755 := by
    simpa [prefixWord, tailWord_3152755, baseEnd_3152755] using wordTrace_append hprefix tailTrace_3152755
  have hstable : (prefixWord ++ tailWord_3152755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152755).length < 2 ^ (prefixWord ++ tailWord_3152755).sum := by decide
  have hdescent : baseEnd_3152755 < baseStart_3152755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152772 : List Nat := [2, 3, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_3152772 : Nat := 118140960795 + 3152772 * 2 ^ 59
def prefixEnd_3152772 : Nat := 4983230072969 + 3 ^ 40 * 3152772 * 2
def baseEnd_3152772 : Nat := 1079258286691362665833781

theorem tailTrace_3152772 : CollatzResearch.WordTrace tailWord_3152772 prefixEnd_3152772 1079258286691362665833781 := by
  unfold tailWord_3152772
  simp only [CollatzResearch.WordTrace]
  refine ⟨57495520867026484717234285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76660694489368646289645713 57495520867026484717234285)
  ·
    refine ⟨21560820325134931768962857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57495520867026484717234285 21560820325134931768962857)
    ·
      refine ⟨16170615243851198826722143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21560820325134931768962857 16170615243851198826722143)
      ·
        refine ⟨24255922865776798240083215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16170615243851198826722143 24255922865776798240083215)
        ·
          refine ⟨36383884298665197360124823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24255922865776798240083215 36383884298665197360124823)
          ·
            refine ⟨54575826447997796040187235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36383884298665197360124823 54575826447997796040187235)
            ·
              refine ⟨81863739671996694060280853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54575826447997796040187235 81863739671996694060280853)
              ·
                refine ⟨3837362797124845034075665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81863739671996694060280853 3837362797124845034075665)
                ·
                  refine ⟨2878022097843633775556749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3837362797124845034075665 2878022097843633775556749)
                  ·
                    refine ⟨1079258286691362665833781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2878022097843633775556749 1079258286691362665833781)
                    ·
                      rfl

theorem cell22_3152772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_3152772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152772 prefixEnd_3152772 := by exact prefixLift 3152772
  have htrace : WordTrace (prefixWord ++ tailWord_3152772) baseStart_3152772 baseEnd_3152772 := by
    simpa [prefixWord, tailWord_3152772, baseEnd_3152772] using wordTrace_append hprefix tailTrace_3152772
  have hstable : (prefixWord ++ tailWord_3152772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152772).length < 2 ^ (prefixWord ++ tailWord_3152772).sum := by decide
  have hdescent : baseEnd_3152772 < baseStart_3152772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152789 : List Nat := [1, 3, 2, 1, 1, 4, 4, 1, 2, 3]
def baseStart_3152789 : Nat := 118140960795 + 3152789 * 2 ^ 59
def prefixEnd_3152789 : Nat := 4983230072969 + 3 ^ 40 * 3152789 * 2
def baseEnd_3152789 : Nat := 1079264106138780288158729

theorem tailTrace_3152789 : CollatzResearch.WordTrace tailWord_3152789 prefixEnd_3152789 1079264106138780288158729 := by
  unfold tailWord_3152789
  simp only [CollatzResearch.WordTrace]
  refine ⟨114991661774991381337837421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76661107849994254225224947 114991661774991381337837421)
  ·
    refine ⟨43121873165621768001689033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114991661774991381337837421 43121873165621768001689033)
    ·
      refine ⟨32341404874216326001266775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43121873165621768001689033 32341404874216326001266775)
      ·
        refine ⟨48512107311324489001900163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32341404874216326001266775 48512107311324489001900163)
        ·
          refine ⟨72768160966986733502850245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48512107311324489001900163 72768160966986733502850245)
          ·
            refine ⟨13644030181310012531784421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72768160966986733502850245 13644030181310012531784421)
            ·
              refine ⟨2558255658995627349709579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13644030181310012531784421 2558255658995627349709579)
              ·
                refine ⟨3837383488493441024564369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558255658995627349709579 3837383488493441024564369)
                ·
                  refine ⟨2878037616370080768423277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3837383488493441024564369 2878037616370080768423277)
                  ·
                    refine ⟨1079264106138780288158729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2878037616370080768423277 1079264106138780288158729)
                    ·
                      rfl

theorem cell22_3152789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_3152789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152789 prefixEnd_3152789 := by exact prefixLift 3152789
  have htrace : WordTrace (prefixWord ++ tailWord_3152789) baseStart_3152789 baseEnd_3152789 := by
    simpa [prefixWord, tailWord_3152789, baseEnd_3152789] using wordTrace_append hprefix tailTrace_3152789
  have hstable : (prefixWord ++ tailWord_3152789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152789).length < 2 ^ (prefixWord ++ tailWord_3152789).sum := by decide
  have hdescent : baseEnd_3152789 < baseStart_3152789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152836 : List Nat := [2, 3, 3, 3, 2, 1, 1, 7]
def baseStart_3152836 : Nat := 118140960795 + 3152836 * 2 ^ 59
def prefixEnd_3152836 : Nat := 4983230072969 + 3 ^ 40 * 3152836 * 2
def baseEnd_3152836 : Nat := 119920021688809759137065

theorem tailTrace_3152836 : CollatzResearch.WordTrace tailWord_3152836 prefixEnd_3152836 119920021688809759137065 := by
  unfold tailWord_3152836
  simp only [CollatzResearch.WordTrace]
  refine ⟨57496688002910554182399181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76662250670547405576532241 57496688002910554182399181)
  ·
    refine ⟨21561258001091457818399693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57496688002910554182399181 21561258001091457818399693)
    ·
      refine ⟨8085471750409296681899885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21561258001091457818399693 8085471750409296681899885)
      ·
        refine ⟨3032051906403486255712457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8085471750409296681899885 3032051906403486255712457)
        ·
          refine ⟨2274038929802614691784343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3032051906403486255712457 2274038929802614691784343)
          ·
            refine ⟨3411058394703922037676515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2274038929802614691784343 3411058394703922037676515)
            ·
              refine ⟨5116587592055883056514773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411058394703922037676515 5116587592055883056514773)
              ·
                refine ⟨119920021688809759137065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5116587592055883056514773 119920021688809759137065)
                ·
                  rfl

theorem cell22_3152836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 7].length) (baseStart_3152836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152836 prefixEnd_3152836 := by exact prefixLift 3152836
  have htrace : WordTrace (prefixWord ++ tailWord_3152836) baseStart_3152836 baseEnd_3152836 := by
    simpa [prefixWord, tailWord_3152836, baseEnd_3152836] using wordTrace_append hprefix tailTrace_3152836
  have hstable : (prefixWord ++ tailWord_3152836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152836).length < 2 ^ (prefixWord ++ tailWord_3152836).sum := by decide
  have hdescent : baseEnd_3152836 < baseStart_3152836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152890 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_3152890 : Nat := 118140960795 + 3152890 * 2 ^ 59
def prefixEnd_3152890 : Nat := 4983230072969 + 3 ^ 40 * 3152890 * 2
def baseEnd_3152890 : Nat := 1079298680502849691383419

theorem tailTrace_3152890 : CollatzResearch.WordTrace tailWord_3152890 prefixEnd_3152890 1079298680502849691383419 := by
  unfold tailWord_3152890
  simp only [CollatzResearch.WordTrace]
  refine ⟨28748836386906368896816031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76663563698416983724842749 28748836386906368896816031)
  ·
    refine ⟨43123254580359553345224047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28748836386906368896816031 43123254580359553345224047)
    ·
      refine ⟨64684881870539330017836071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43123254580359553345224047 64684881870539330017836071)
      ·
        refine ⟨97027322805808995026754107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64684881870539330017836071 97027322805808995026754107)
        ·
          refine ⟨145540984208713492540131161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97027322805808995026754107 145540984208713492540131161)
          ·
            refine ⟨109155738156535119405098371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145540984208713492540131161 109155738156535119405098371)
            ·
              refine ⟨163733607234802679107647557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109155738156535119405098371 163733607234802679107647557)
              ·
                refine ⟨30700051356525502332683917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163733607234802679107647557 30700051356525502332683917)
                ·
                  refine ⟨11512519258697063374756469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30700051356525502332683917 11512519258697063374756469)
                  ·
                    refine ⟨1079298680502849691383419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11512519258697063374756469 1079298680502849691383419)
                    ·
                      rfl

theorem cell22_3152890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_3152890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152890 prefixEnd_3152890 := by exact prefixLift 3152890
  have htrace : WordTrace (prefixWord ++ tailWord_3152890) baseStart_3152890 baseEnd_3152890 := by
    simpa [prefixWord, tailWord_3152890, baseEnd_3152890] using wordTrace_append hprefix tailTrace_3152890
  have hstable : (prefixWord ++ tailWord_3152890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152890).length < 2 ^ (prefixWord ++ tailWord_3152890).sum := by decide
  have hdescent : baseEnd_3152890 < baseStart_3152890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152892 : List Nat := [2, 2, 2, 1, 2, 4, 2, 1, 6]
def baseStart_3152892 : Nat := 118140960795 + 3152892 * 2 ^ 59
def prefixEnd_3152892 : Nat := 4983230072969 + 3 ^ 40 * 3152892 * 2
def baseEnd_3152892 : Nat := 359766455047907450944471

theorem tailTrace_3152892 : CollatzResearch.WordTrace tailWord_3152892 prefixEnd_3152892 359766455047907450944471 := by
  unfold tailWord_3152892
  simp only [CollatzResearch.WordTrace]
  refine ⟨57497709246809114964418465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76663612329078819952557953 57497709246809114964418465)
  ·
    refine ⟨43123281935106836223313849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57497709246809114964418465 43123281935106836223313849)
    ·
      refine ⟨32342461451330127167485387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43123281935106836223313849 32342461451330127167485387)
      ·
        refine ⟨48513692176995190751228081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32342461451330127167485387 48513692176995190751228081)
        ·
          refine ⟨36385269132746393063421061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48513692176995190751228081 36385269132746393063421061)
          ·
            refine ⟨6822237962389948699391449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36385269132746393063421061 6822237962389948699391449)
            ·
              refine ⟨5116678471792461524543587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6822237962389948699391449 5116678471792461524543587)
              ·
                refine ⟨7675017707688692286815381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116678471792461524543587 7675017707688692286815381)
                ·
                  refine ⟨359766455047907450944471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7675017707688692286815381 359766455047907450944471)
                  ·
                    rfl

theorem cell22_3152892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_3152892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152892 prefixEnd_3152892 := by exact prefixLift 3152892
  have htrace : WordTrace (prefixWord ++ tailWord_3152892) baseStart_3152892 baseEnd_3152892 := by
    simpa [prefixWord, tailWord_3152892, baseEnd_3152892] using wordTrace_append hprefix tailTrace_3152892
  have hstable : (prefixWord ++ tailWord_3152892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152892).length < 2 ^ (prefixWord ++ tailWord_3152892).sum := by decide
  have hdescent : baseEnd_3152892 < baseStart_3152892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152898 : List Nat := [3, 4, 1, 3, 1, 1, 3, 1, 5]
def baseStart_3152898 : Nat := 118140960795 + 3152898 * 2 ^ 59
def prefixEnd_3152898 : Nat := 4983230072969 + 3 ^ 40 * 3152898 * 2
def baseEnd_3152898 : Nat := 359767139688780112394465

theorem tailTrace_3152898 : CollatzResearch.WordTrace tailWord_3152898 prefixEnd_3152898 359767139688780112394465 := by
  unfold tailWord_3152898
  simp only [CollatzResearch.WordTrace]
  refine ⟨28748909332899123238388837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76663758221064328635703565 28748909332899123238388837)
  ·
    refine ⟨5390420499918585607197907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28748909332899123238388837 5390420499918585607197907)
    ·
      refine ⟨8085630749877878410796861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5390420499918585607197907 8085630749877878410796861)
      ·
        refine ⟨3032111531204204404048823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8085630749877878410796861 3032111531204204404048823)
        ·
          refine ⟨4548167296806306606073235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3032111531204204404048823 4548167296806306606073235)
          ·
            refine ⟨6822250945209459909109853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4548167296806306606073235 6822250945209459909109853)
            ·
              refine ⟨2558344104453547465916195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6822250945209459909109853 2558344104453547465916195)
              ·
                refine ⟨3837516156680321198874293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558344104453547465916195 3837516156680321198874293)
                ·
                  refine ⟨359767139688780112394465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3837516156680321198874293 359767139688780112394465)
                  ·
                    rfl

theorem cell22_3152898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_3152898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152898 prefixEnd_3152898 := by exact prefixLift 3152898
  have htrace : WordTrace (prefixWord ++ tailWord_3152898) baseStart_3152898 baseEnd_3152898 := by
    simpa [prefixWord, tailWord_3152898, baseEnd_3152898] using wordTrace_append hprefix tailTrace_3152898
  have hstable : (prefixWord ++ tailWord_3152898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152898).length < 2 ^ (prefixWord ++ tailWord_3152898).sum := by decide
  have hdescent : baseEnd_3152898 < baseStart_3152898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152907 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 1, 5]
def baseStart_3152907 : Nat := 118140960795 + 3152907 * 2 ^ 59
def prefixEnd_3152907 : Nat := 4983230072969 + 3 ^ 40 * 3152907 * 2
def baseEnd_3152907 : Nat := 1079304499950267313708367

theorem tailTrace_3152907 : CollatzResearch.WordTrace tailWord_3152907 prefixEnd_3152907 1079304499950267313708367 := by
  unfold tailWord_3152907
  simp only [CollatzResearch.WordTrace]
  refine ⟨114995965588563887490632975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76663977059042591660421983 114995965588563887490632975)
  ·
    refine ⟨172493948382845831235949463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114995965588563887490632975 172493948382845831235949463)
    ·
      refine ⟨258740922574268746853924195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172493948382845831235949463 258740922574268746853924195)
      ·
        refine ⟨388111383861403120280886293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258740922574268746853924195 388111383861403120280886293)
        ·
          refine ⟨18192721118503271263166545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 388111383861403120280886293 18192721118503271263166545)
          ·
            refine ⟨13644540838877453447374909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18192721118503271263166545 13644540838877453447374909)
            ·
              refine ⟨5116702814579045042765591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13644540838877453447374909 5116702814579045042765591)
              ·
                refine ⟨7675054221868567564148387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116702814579045042765591 7675054221868567564148387)
                ·
                  refine ⟨11512581332802851346222581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7675054221868567564148387 11512581332802851346222581)
                  ·
                    refine ⟨1079304499950267313708367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11512581332802851346222581 1079304499950267313708367)
                    ·
                      rfl

theorem cell22_3152907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 5].length) (baseStart_3152907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152907 prefixEnd_3152907 := by exact prefixLift 3152907
  have htrace : WordTrace (prefixWord ++ tailWord_3152907) baseStart_3152907 baseEnd_3152907 := by
    simpa [prefixWord, tailWord_3152907, baseEnd_3152907] using wordTrace_append hprefix tailTrace_3152907
  have hstable : (prefixWord ++ tailWord_3152907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152907).length < 2 ^ (prefixWord ++ tailWord_3152907).sum := by decide
  have hdescent : baseEnd_3152907 < baseStart_3152907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152922 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_3152922 : Nat := 118140960795 + 3152922 * 2 ^ 59
def prefixEnd_3152922 : Nat := 4983230072969 + 3 ^ 40 * 3152922 * 2
def baseEnd_3152922 : Nat := 1079309634756812274583321

theorem tailTrace_3152922 : CollatzResearch.WordTrace tailWord_3152922 prefixEnd_3152922 1079309634756812274583321 := by
  unfold tailWord_3152922
  simp only [CollatzResearch.WordTrace]
  refine ⟨28749128170877386263107255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76664341789006363368286013 28749128170877386263107255)
  ·
    refine ⟨43123692256316079394660883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28749128170877386263107255 43123692256316079394660883)
    ·
      refine ⟨64685538384474119091991325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43123692256316079394660883 64685538384474119091991325)
      ·
        refine ⟨24257076894177794659496747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64685538384474119091991325 24257076894177794659496747)
        ·
          refine ⟨36385615341266691989245121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24257076894177794659496747 36385615341266691989245121)
          ·
            refine ⟨27289211505950018991933841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36385615341266691989245121 27289211505950018991933841)
            ·
              refine ⟨20466908629462514243950381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27289211505950018991933841 20466908629462514243950381)
              ·
                refine ⟨7675090736048442841481393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20466908629462514243950381 7675090736048442841481393)
                ·
                  refine ⟨5756318052036332131111045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7675090736048442841481393 5756318052036332131111045)
                  ·
                    refine ⟨1079309634756812274583321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5756318052036332131111045 1079309634756812274583321)
                    ·
                      rfl

theorem cell22_3152922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_3152922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152922 prefixEnd_3152922 := by exact prefixLift 3152922
  have htrace : WordTrace (prefixWord ++ tailWord_3152922) baseStart_3152922 baseEnd_3152922 := by
    simpa [prefixWord, tailWord_3152922, baseEnd_3152922] using wordTrace_append hprefix tailTrace_3152922
  have hstable : (prefixWord ++ tailWord_3152922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152922).length < 2 ^ (prefixWord ++ tailWord_3152922).sum := by decide
  have hdescent : baseEnd_3152922 < baseStart_3152922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152958 : List Nat := [4, 2, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_3152958 : Nat := 118140960795 + 3152958 * 2 ^ 59
def prefixEnd_3152958 : Nat := 4983230072969 + 3 ^ 40 * 3152958 * 2
def baseEnd_3152958 : Nat := 1079321958292520180683211

theorem tailTrace_3152958 : CollatzResearch.WordTrace tailWord_3152958 prefixEnd_3152958 1079321958292520180683211 := by
  unfold tailWord_3152958
  simp only [CollatzResearch.WordTrace]
  refine ⟨14374728213922390400092441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76665217140919415467159685 14374728213922390400092441)
  ·
    refine ⟨10781046160441792800069331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14374728213922390400092441 10781046160441792800069331)
    ·
      refine ⟨16171569240662689200103997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10781046160441792800069331 16171569240662689200103997)
      ·
        refine ⟨6064338465248508450038999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16171569240662689200103997 6064338465248508450038999)
        ·
          refine ⟨9096507697872762675058499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6064338465248508450038999 9096507697872762675058499)
          ·
            refine ⟨13644761546809144012587749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9096507697872762675058499 13644761546809144012587749)
            ·
              refine ⟨2558392790026714502360203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13644761546809144012587749 2558392790026714502360203)
              ·
                refine ⟨3837589185040071753540305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558392790026714502360203 3837589185040071753540305)
                ·
                  refine ⟨2878191888780053815155229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3837589185040071753540305 2878191888780053815155229)
                  ·
                    refine ⟨1079321958292520180683211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2878191888780053815155229 1079321958292520180683211)
                    ·
                      rfl

theorem cell22_3152958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_3152958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152958 prefixEnd_3152958 := by exact prefixLift 3152958
  have htrace : WordTrace (prefixWord ++ tailWord_3152958) baseStart_3152958 baseEnd_3152958 := by
    simpa [prefixWord, tailWord_3152958, baseEnd_3152958] using wordTrace_append hprefix tailTrace_3152958
  have hstable : (prefixWord ++ tailWord_3152958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152958).length < 2 ^ (prefixWord ++ tailWord_3152958).sum := by decide
  have hdescent : baseEnd_3152958 < baseStart_3152958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152997 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_3152997 : Nat := 118140960795 + 3152997 * 2 ^ 59
def prefixEnd_3152997 : Nat := 4983230072969 + 3 ^ 40 * 3152997 * 2
def baseEnd_3152997 : Nat := 1079335308789537078958091

theorem tailTrace_3152997 : CollatzResearch.WordTrace tailWord_3152997 prefixEnd_3152997 1079335308789537078958091 := by
  unfold tailWord_3152997
  simp only [CollatzResearch.WordTrace]
  refine ⟨114999248158237832861409245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76666165438825221907606163 114999248158237832861409245)
  ·
    refine ⟨43124718059339187323028467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114999248158237832861409245 43124718059339187323028467)
    ·
      refine ⟨64687077089008780984542701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43124718059339187323028467 64687077089008780984542701)
      ·
        refine ⟨24257653908378292869203513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64687077089008780984542701 24257653908378292869203513)
        ·
          refine ⟨18193240431283719651902635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24257653908378292869203513 18193240431283719651902635)
          ·
            refine ⟨27289860646925579477853953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18193240431283719651902635 27289860646925579477853953)
            ·
              refine ⟨20467395485194184608390465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27289860646925579477853953 20467395485194184608390465)
              ·
                refine ⟨15350546613895638456292849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20467395485194184608390465 15350546613895638456292849)
                ·
                  refine ⟨11512909960421728842219637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15350546613895638456292849 11512909960421728842219637)
                  ·
                    refine ⟨1079335308789537078958091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11512909960421728842219637 1079335308789537078958091)
                    ·
                      rfl

theorem cell22_3152997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_3152997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152997 prefixEnd_3152997 := by exact prefixLift 3152997
  have htrace : WordTrace (prefixWord ++ tailWord_3152997) baseStart_3152997 baseEnd_3152997 := by
    simpa [prefixWord, tailWord_3152997, baseEnd_3152997] using wordTrace_append hprefix tailTrace_3152997
  have hstable : (prefixWord ++ tailWord_3152997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152997).length < 2 ^ (prefixWord ++ tailWord_3152997).sum := by decide
  have hdescent : baseEnd_3152997 < baseStart_3152997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3152999 : List Nat := [1, 1, 5, 1, 1, 4, 2, 2, 5]
def baseStart_3152999 : Nat := 118140960795 + 3152999 * 2 ^ 59
def prefixEnd_3152999 : Nat := 4983230072969 + 3 ^ 40 * 3152999 * 2
def baseEnd_3152999 : Nat := 359778664476803246802695

theorem tailTrace_3152999 : CollatzResearch.WordTrace tailWord_3152999 prefixEnd_3152999 359778664476803246802695 := by
  unfold tailWord_3152999
  simp only [CollatzResearch.WordTrace]
  refine ⟨114999321104230587202982051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76666214069487058135321367 114999321104230587202982051)
  ·
    refine ⟨172498981656345880804473077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114999321104230587202982051 172498981656345880804473077)
    ·
      refine ⟨16171779530282426325419351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172498981656345880804473077 16171779530282426325419351)
      ·
        refine ⟨24257669295423639488129027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16171779530282426325419351 24257669295423639488129027)
        ·
          refine ⟨36386503943135459232193541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24257669295423639488129027 36386503943135459232193541)
          ·
            refine ⟨6822469489337898606036289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36386503943135459232193541 6822469489337898606036289)
            ·
              refine ⟨5116852117003423954527217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6822469489337898606036289 5116852117003423954527217)
              ·
                refine ⟨3837639087752567965895413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5116852117003423954527217 3837639087752567965895413)
                ·
                  refine ⟨359778664476803246802695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3837639087752567965895413 359778664476803246802695)
                  ·
                    rfl

theorem cell22_3152999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 2, 5].length) (baseStart_3152999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3152999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3152999 prefixEnd_3152999 := by exact prefixLift 3152999
  have htrace : WordTrace (prefixWord ++ tailWord_3152999) baseStart_3152999 baseEnd_3152999 := by
    simpa [prefixWord, tailWord_3152999, baseEnd_3152999] using wordTrace_append hprefix tailTrace_3152999
  have hstable : (prefixWord ++ tailWord_3152999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3152999).length < 2 ^ (prefixWord ++ tailWord_3152999).sum := by decide
  have hdescent : baseEnd_3152999 < baseStart_3152999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3152999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153014 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_3153014 : Nat := 118140960795 + 3153014 * 2 ^ 59
def prefixEnd_3153014 : Nat := 4983230072969 + 3 ^ 40 * 3153014 * 2
def baseEnd_3153014 : Nat := 1079341128236954701283039

theorem tailTrace_3153014 : CollatzResearch.WordTrace tailWord_3153014 prefixEnd_3153014 1079341128236954701283039 := by
  unfold tailWord_3153014
  simp only [CollatzResearch.WordTrace]
  refine ⟨7187491762448515297798631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76666578799450829843185397 7187491762448515297798631)
  ·
    refine ⟨10781237643672772946697947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7187491762448515297798631 10781237643672772946697947)
    ·
      refine ⟨16171856465509159420046921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10781237643672772946697947 16171856465509159420046921)
      ·
        refine ⟨12128892349131869565035191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16171856465509159420046921 12128892349131869565035191)
        ·
          refine ⟨18193338523697804347552787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12128892349131869565035191 18193338523697804347552787)
          ·
            refine ⟨27290007785546706521329181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18193338523697804347552787 27290007785546706521329181)
            ·
              refine ⟨10233752919580014945498443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27290007785546706521329181 10233752919580014945498443)
              ·
                refine ⟨15350629379370022418247665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10233752919580014945498443 15350629379370022418247665)
                ·
                  refine ⟨11512972034527516813685749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15350629379370022418247665 11512972034527516813685749)
                  ·
                    refine ⟨1079341128236954701283039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11512972034527516813685749 1079341128236954701283039)
                    ·
                      rfl

theorem cell22_3153014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_3153014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153014 prefixEnd_3153014 := by exact prefixLift 3153014
  have htrace : WordTrace (prefixWord ++ tailWord_3153014) baseStart_3153014 baseEnd_3153014 := by
    simpa [prefixWord, tailWord_3153014, baseEnd_3153014] using wordTrace_append hprefix tailTrace_3153014
  have hstable : (prefixWord ++ tailWord_3153014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153014).length < 2 ^ (prefixWord ++ tailWord_3153014).sum := by decide
  have hdescent : baseEnd_3153014 < baseStart_3153014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153027 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 6]
def baseStart_3153027 : Nat := 118140960795 + 3153027 * 2 ^ 59
def prefixEnd_3153027 : Nat := 4983230072969 + 3 ^ 40 * 3153027 * 2
def baseEnd_3153027 : Nat := 359781859467542333569333

theorem tailTrace_3153027 : CollatzResearch.WordTrace tailWord_3153027 prefixEnd_3153027 359781859467542333569333 := by
  unfold tailWord_3153027
  simp only [CollatzResearch.WordTrace]
  refine ⟨115000342348129147985001335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76666894898752765323334223 115000342348129147985001335)
  ·
    refine ⟨172500513522193721977502003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115000342348129147985001335 172500513522193721977502003)
    ·
      refine ⟨258750770283290582966253005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172500513522193721977502003 258750770283290582966253005)
      ·
        refine ⟨97031538856233968612344877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258750770283290582966253005 97031538856233968612344877)
        ·
          refine ⟨36386827071087738229629329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97031538856233968612344877 36386827071087738229629329)
          ·
            refine ⟨27290120303315803672221997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36386827071087738229629329 27290120303315803672221997)
            ·
              refine ⟨10233795113743426377083249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27290120303315803672221997 10233795113743426377083249)
              ·
                refine ⟨7675346335307569782812437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10233795113743426377083249 7675346335307569782812437)
                ·
                  refine ⟨359781859467542333569333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7675346335307569782812437 359781859467542333569333)
                  ·
                    rfl

theorem cell22_3153027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 6].length) (baseStart_3153027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153027 prefixEnd_3153027 := by exact prefixLift 3153027
  have htrace : WordTrace (prefixWord ++ tailWord_3153027) baseStart_3153027 baseEnd_3153027 := by
    simpa [prefixWord, tailWord_3153027, baseEnd_3153027] using wordTrace_append hprefix tailTrace_3153027
  have hstable : (prefixWord ++ tailWord_3153027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153027).length < 2 ^ (prefixWord ++ tailWord_3153027).sum := by decide
  have hdescent : baseEnd_3153027 < baseStart_3153027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153108 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_3153108 : Nat := 118140960795 + 3153108 * 2 ^ 59
def prefixEnd_3153108 : Nat := 4983230072969 + 3 ^ 40 * 3153108 * 2
def baseEnd_3153108 : Nat := 1079373306357969789432751

theorem tailTrace_3153108 : CollatzResearch.WordTrace tailWord_3153108 prefixEnd_3153108 1079373306357969789432751 := by
  unfold tailWord_3153108
  simp only [CollatzResearch.WordTrace]
  refine ⟨57501648330417849409349989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76668864440557132545799985 57501648330417849409349989)
  ·
    refine ⟨10781559061953346764253123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57501648330417849409349989 10781559061953346764253123)
    ·
      refine ⟨16172338592930020146379685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10781559061953346764253123 16172338592930020146379685)
      ·
        refine ⟨3032313486174378777446191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16172338592930020146379685 3032313486174378777446191)
        ·
          refine ⟨4548470229261568166169287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3032313486174378777446191 4548470229261568166169287)
          ·
            refine ⟨6822705343892352249253931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4548470229261568166169287 6822705343892352249253931)
            ·
              refine ⟨10234058015838528373880897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6822705343892352249253931 10234058015838528373880897)
              ·
                refine ⟨7675543511878896280410673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10234058015838528373880897 7675543511878896280410673)
                ·
                  refine ⟨5756657633909172210308005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7675543511878896280410673 5756657633909172210308005)
                  ·
                    refine ⟨1079373306357969789432751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5756657633909172210308005 1079373306357969789432751)
                    ·
                      rfl

theorem cell22_3153108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_3153108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153108 prefixEnd_3153108 := by exact prefixLift 3153108
  have htrace : WordTrace (prefixWord ++ tailWord_3153108) baseStart_3153108 baseEnd_3153108 := by
    simpa [prefixWord, tailWord_3153108, baseEnd_3153108] using wordTrace_append hprefix tailTrace_3153108
  have hstable : (prefixWord ++ tailWord_3153108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153108).length < 2 ^ (prefixWord ++ tailWord_3153108).sum := by decide
  have hdescent : baseEnd_3153108 < baseStart_3153108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153121 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 3, 3]
def baseStart_3153121 : Nat := 118140960795 + 3153121 * 2 ^ 59
def prefixEnd_3153121 : Nat := 4983230072969 + 3 ^ 40 * 3153121 * 2
def baseEnd_3153121 : Nat := 1079377756523642088857711

theorem tailTrace_3153121 : CollatzResearch.WordTrace tailWord_3153121 prefixEnd_3153121 1079377756523642088857711 := by
  unfold tailWord_3153121
  simp only [CollatzResearch.WordTrace]
  refine ⟨115003770809788602038923217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76669180539859068025948811 115003770809788602038923217)
  ·
    refine ⟨86252828107341451529192413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115003770809788602038923217 86252828107341451529192413)
    ·
      refine ⟨32344810540253044323447155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86252828107341451529192413 32344810540253044323447155)
      ·
        refine ⟨48517215810379566485170733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32344810540253044323447155 48517215810379566485170733)
        ·
          refine ⟨18193955928892337431939025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48517215810379566485170733 18193955928892337431939025)
          ·
            refine ⟨13645466946669253073954269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18193955928892337431939025 13645466946669253073954269)
            ·
              refine ⟨5117050105000969902732851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13645466946669253073954269 5117050105000969902732851)
              ·
                refine ⟨7675575157501454854099277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5117050105000969902732851 7675575157501454854099277)
                ·
                  refine ⟨2878340684063045570287229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7675575157501454854099277 2878340684063045570287229)
                  ·
                    refine ⟨1079377756523642088857711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2878340684063045570287229 1079377756523642088857711)
                    ·
                      rfl

theorem cell22_3153121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_3153121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153121 prefixEnd_3153121 := by exact prefixLift 3153121
  have htrace : WordTrace (prefixWord ++ tailWord_3153121) baseStart_3153121 baseEnd_3153121 := by
    simpa [prefixWord, tailWord_3153121, baseEnd_3153121] using wordTrace_append hprefix tailTrace_3153121
  have hstable : (prefixWord ++ tailWord_3153121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153121).length < 2 ^ (prefixWord ++ tailWord_3153121).sum := by decide
  have hdescent : baseEnd_3153121 < baseStart_3153121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153127 : List Nat := [1, 1, 5, 3, 3, 1, 2, 1, 2, 3]
def baseStart_3153127 : Nat := 118140960795 + 3153127 * 2 ^ 59
def prefixEnd_3153127 : Nat := 4983230072969 + 3 ^ 40 * 3153127 * 2
def baseEnd_3153127 : Nat := 1079379810446260073207693

theorem tailTrace_3153127 : CollatzResearch.WordTrace tailWord_3153127 prefixEnd_3153127 1079379810446260073207693 := by
  unfold tailWord_3153127
  simp only [CollatzResearch.WordTrace]
  refine ⟨115003989647766865063641635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76669326431844576709094423 115003989647766865063641635)
  ·
    refine ⟨172505984471650297595462453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115003989647766865063641635 172505984471650297595462453)
    ·
      refine ⟨16172436044217215399574605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172505984471650297595462453 16172436044217215399574605)
      ·
        refine ⟨6064663516581455774840477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16172436044217215399574605 6064663516581455774840477)
        ·
          refine ⟨2274248818718045915565179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6064663516581455774840477 2274248818718045915565179)
          ·
            refine ⟨3411373228077068873347769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2274248818718045915565179 3411373228077068873347769)
            ·
              refine ⟨2558529921057801655010827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3411373228077068873347769 2558529921057801655010827)
              ·
                refine ⟨3837794881586702482516241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558529921057801655010827 3837794881586702482516241)
                ·
                  refine ⟨2878346161190026861887181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3837794881586702482516241 2878346161190026861887181)
                  ·
                    refine ⟨1079379810446260073207693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2878346161190026861887181 1079379810446260073207693)
                    ·
                      rfl

theorem cell22_3153127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_3153127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153127 prefixEnd_3153127 := by exact prefixLift 3153127
  have htrace : WordTrace (prefixWord ++ tailWord_3153127) baseStart_3153127 baseEnd_3153127 := by
    simpa [prefixWord, tailWord_3153127, baseEnd_3153127] using wordTrace_append hprefix tailTrace_3153127
  have hstable : (prefixWord ++ tailWord_3153127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153127).length < 2 ^ (prefixWord ++ tailWord_3153127).sum := by decide
  have hdescent : baseEnd_3153127 < baseStart_3153127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153181 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_3153181 : Nat := 118140960795 + 3153181 * 2 ^ 59
def prefixEnd_3153181 : Nat := 4983230072969 + 3 ^ 40 * 3153181 * 2
def baseEnd_3153181 : Nat := 1079398295749821932357527

theorem tailTrace_3153181 : CollatzResearch.WordTrace tailWord_3153181 prefixEnd_3153181 1079398295749821932357527 := by
  unfold tailWord_3153181
  simp only [CollatzResearch.WordTrace]
  refine ⟨115005959189571232286107397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76670639459714154857404931 115005959189571232286107397)
  ·
    refine ⟨21563617348044606053645137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115005959189571232286107397 21563617348044606053645137)
    ·
      refine ⟨16172713011033454540233853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21563617348044606053645137 16172713011033454540233853)
      ·
        refine ⟨6064767379137545452587695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16172713011033454540233853 6064767379137545452587695)
        ·
          refine ⟨9097151068706318178881543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6064767379137545452587695 9097151068706318178881543)
          ·
            refine ⟨13645726603059477268322315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9097151068706318178881543 13645726603059477268322315)
            ·
              refine ⟨20468589904589215902483473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13645726603059477268322315 20468589904589215902483473)
              ·
                refine ⟨15351442428441911926862605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20468589904589215902483473 15351442428441911926862605)
                ·
                  refine ⟨5756790910665716972573477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15351442428441911926862605 5756790910665716972573477)
                  ·
                    refine ⟨1079398295749821932357527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5756790910665716972573477 1079398295749821932357527)
                    ·
                      rfl

theorem cell22_3153181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_3153181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153181 prefixEnd_3153181 := by exact prefixLift 3153181
  have htrace : WordTrace (prefixWord ++ tailWord_3153181) baseStart_3153181 baseEnd_3153181 := by
    simpa [prefixWord, tailWord_3153181, baseEnd_3153181] using wordTrace_append hprefix tailTrace_3153181
  have hstable : (prefixWord ++ tailWord_3153181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153181).length < 2 ^ (prefixWord ++ tailWord_3153181).sum := by decide
  have hdescent : baseEnd_3153181 < baseStart_3153181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153228 : List Nat := [2, 2, 1, 3, 2, 2, 3, 2, 2, 3]
def baseStart_3153228 : Nat := 118140960795 + 3153228 * 2 ^ 59
def prefixEnd_3153228 : Nat := 4983230072969 + 3 ^ 40 * 3153228 * 2
def baseEnd_3153228 : Nat := 1079414384810329476432383

theorem tailTrace_3153228 : CollatzResearch.WordTrace tailWord_3153228 prefixEnd_3153228 1079414384810329476432383 := by
  unfold tailWord_3153228
  simp only [CollatzResearch.WordTrace]
  refine ⟨57503836710200479656534169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76671782280267306208712225 57503836710200479656534169)
  ·
    refine ⟨43127877532650359742400627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57503836710200479656534169 43127877532650359742400627)
    ·
      refine ⟨64691816298975539613600941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43127877532650359742400627 64691816298975539613600941)
      ·
        refine ⟨24259431112115827355100353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64691816298975539613600941 24259431112115827355100353)
        ·
          refine ⟨18194573334086870516325265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24259431112115827355100353 18194573334086870516325265)
          ·
            refine ⟨13645930000565152887243949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18194573334086870516325265 13645930000565152887243949)
            ·
              refine ⟨5117223750211932332716481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13645930000565152887243949 5117223750211932332716481)
              ·
                refine ⟨3837917812658949249537361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5117223750211932332716481 3837917812658949249537361)
                ·
                  refine ⟨2878438359494211937153021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3837917812658949249537361 2878438359494211937153021)
                  ·
                    refine ⟨1079414384810329476432383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2878438359494211937153021 1079414384810329476432383)
                    ·
                      rfl

theorem cell22_3153228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_3153228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153228 prefixEnd_3153228 := by exact prefixLift 3153228
  have htrace : WordTrace (prefixWord ++ tailWord_3153228) baseStart_3153228 baseEnd_3153228 := by
    simpa [prefixWord, tailWord_3153228, baseEnd_3153228] using wordTrace_append hprefix tailTrace_3153228
  have hstable : (prefixWord ++ tailWord_3153228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153228).length < 2 ^ (prefixWord ++ tailWord_3153228).sum := by decide
  have hdescent : baseEnd_3153228 < baseStart_3153228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153397 : List Nat := [1, 3, 5, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3153397 : Nat := 118140960795 + 3153397 * 2 ^ 59
def prefixEnd_3153397 : Nat := 4983230072969 + 3 ^ 40 * 3153397 * 2
def baseEnd_3153397 : Nat := 1079472236964069368956865

theorem tailTrace_3153397 : CollatzResearch.WordTrace tailWord_3153397 prefixEnd_3153397 1079472236964069368956865 := by
  unfold tailWord_3153397
  simp only [CollatzResearch.WordTrace]
  refine ⟨115013837356788701175970445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76675891571192467450646963 115013837356788701175970445)
  ·
    refine ⟨43130189008795762940988917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115013837356788701175970445 43130189008795762940988917)
    ·
      refine ⟨4043455219574602775717711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43130189008795762940988917 4043455219574602775717711)
      ·
        refine ⟨6065182829361904163576567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4043455219574602775717711 6065182829361904163576567)
        ·
          refine ⟨9097774244042856245364851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6065182829361904163576567 9097774244042856245364851)
          ·
            refine ⟨13646661366064284368047277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9097774244042856245364851 13646661366064284368047277)
            ·
              refine ⟨5117498012274106638017729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13646661366064284368047277 5117498012274106638017729)
              ·
                refine ⟨3838123509205579978513297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5117498012274106638017729 3838123509205579978513297)
                ·
                  refine ⟨2878592631904184983884973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3838123509205579978513297 2878592631904184983884973)
                  ·
                    refine ⟨1079472236964069368956865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2878592631904184983884973 1079472236964069368956865)
                    ·
                      rfl

theorem cell22_3153397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3153397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153397 prefixEnd_3153397 := by exact prefixLift 3153397
  have htrace : WordTrace (prefixWord ++ tailWord_3153397) baseStart_3153397 baseEnd_3153397 := by
    simpa [prefixWord, tailWord_3153397, baseEnd_3153397] using wordTrace_append hprefix tailTrace_3153397
  have hstable : (prefixWord ++ tailWord_3153397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153397).length < 2 ^ (prefixWord ++ tailWord_3153397).sum := by decide
  have hdescent : baseEnd_3153397 < baseStart_3153397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153442 : List Nat := [3, 3, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_3153442 : Nat := 118140960795 + 3153442 * 2 ^ 59
def prefixEnd_3153442 : Nat := 4983230072969 + 3 ^ 40 * 3153442 * 2
def baseEnd_3153442 : Nat := 1079487641383704251581727

theorem tailTrace_3153442 : CollatzResearch.WordTrace tailWord_3153442 prefixEnd_3153442 1079487641383704251581727 := by
  unfold tailWord_3153442
  simp only [CollatzResearch.WordTrace]
  refine ⟨28753869660406418465339645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76676985761083782574239053 28753869660406418465339645)
  ·
    refine ⟨10782701122652406924502367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28753869660406418465339645 10782701122652406924502367)
    ·
      refine ⟨16174051683978610386753551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10782701122652406924502367 16174051683978610386753551)
      ·
        refine ⟨24261077525967915580130327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16174051683978610386753551 24261077525967915580130327)
        ·
          refine ⟨36391616288951873370195491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24261077525967915580130327 36391616288951873370195491)
          ·
            refine ⟨54587424433427810055293237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36391616288951873370195491 54587424433427810055293237)
            ·
              refine ⟨5117571040633857192683741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54587424433427810055293237 5117571040633857192683741)
              ·
                refine ⟨1919089140237696447256403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5117571040633857192683741 1919089140237696447256403)
                ·
                  refine ⟨2878633710356544670884605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919089140237696447256403 2878633710356544670884605)
                  ·
                    refine ⟨1079487641383704251581727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2878633710356544670884605 1079487641383704251581727)
                    ·
                      rfl

theorem cell22_3153442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_3153442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153442 prefixEnd_3153442 := by exact prefixLift 3153442
  have htrace : WordTrace (prefixWord ++ tailWord_3153442) baseStart_3153442 baseEnd_3153442 := by
    simpa [prefixWord, tailWord_3153442, baseEnd_3153442] using wordTrace_append hprefix tailTrace_3153442
  have hstable : (prefixWord ++ tailWord_3153442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153442).length < 2 ^ (prefixWord ++ tailWord_3153442).sum := by decide
  have hdescent : baseEnd_3153442 < baseStart_3153442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153451 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 7, 4]
def baseStart_3153451 : Nat := 118140960795 + 3153451 * 2 ^ 59
def prefixEnd_3153451 : Nat := 4983230072969 + 3 ^ 40 * 3153451 * 2
def baseEnd_3153451 : Nat := 1079490722267631228106699

theorem tailTrace_3153451 : CollatzResearch.WordTrace tailWord_3153451 prefixEnd_3153451 1079490722267631228106699 := by
  unfold tailWord_3153451
  simp only [CollatzResearch.WordTrace]
  refine ⟨115015806898593068398436207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76677204599062045598957471 115015806898593068398436207)
  ·
    refine ⟨172523710347889602597654311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115015806898593068398436207 172523710347889602597654311)
    ·
      refine ⟨258785565521834403896481467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172523710347889602597654311 258785565521834403896481467)
      ·
        refine ⟨388178348282751605844722201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258785565521834403896481467 388178348282751605844722201)
        ·
          refine ⟨291133761212063704383541651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388178348282751605844722201 291133761212063704383541651)
          ·
            refine ⟨436700641818095556575312477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291133761212063704383541651 436700641818095556575312477)
            ·
              refine ⟨163762740681785833715742179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 436700641818095556575312477 163762740681785833715742179)
              ·
                refine ⟨245644111022678750573613269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163762740681785833715742179 245644111022678750573613269)
                ·
                  refine ⟨5757283852094033216569061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 245644111022678750573613269 5757283852094033216569061)
                  ·
                    refine ⟨1079490722267631228106699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5757283852094033216569061 1079490722267631228106699)
                    ·
                      rfl

theorem cell22_3153451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 4].length) (baseStart_3153451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153451 prefixEnd_3153451 := by exact prefixLift 3153451
  have htrace : WordTrace (prefixWord ++ tailWord_3153451) baseStart_3153451 baseEnd_3153451 := by
    simpa [prefixWord, tailWord_3153451, baseEnd_3153451] using wordTrace_append hprefix tailTrace_3153451
  have hstable : (prefixWord ++ tailWord_3153451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153451).length < 2 ^ (prefixWord ++ tailWord_3153451).sum := by decide
  have hdescent : baseEnd_3153451 < baseStart_3153451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153481 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 5, 5]
def baseStart_3153481 : Nat := 118140960795 + 3153481 * 2 ^ 59
def prefixEnd_3153481 : Nat := 4983230072969 + 3 ^ 40 * 3153481 * 2
def baseEnd_3153481 : Nat := 1079500991880721149856607

theorem tailTrace_3153481 : CollatzResearch.WordTrace tailWord_3153481 prefixEnd_3153481 1079500991880721149856607 := by
  unfold tailWord_3153481
  simp only [CollatzResearch.WordTrace]
  refine ⟨115016901088484383522028297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76677934058989589014685531 115016901088484383522028297)
  ·
    refine ⟨86262675816363287641521223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115016901088484383522028297 86262675816363287641521223)
    ·
      refine ⟨129394013724544931462281835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86262675816363287641521223 129394013724544931462281835)
      ·
        refine ⟨194091020586817397193422753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129394013724544931462281835 194091020586817397193422753)
        ·
          refine ⟨145568265440113047895067065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194091020586817397193422753 145568265440113047895067065)
          ·
            refine ⟨109176199080084785921300299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145568265440113047895067065 109176199080084785921300299)
            ·
              refine ⟨163764298620127178881950449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109176199080084785921300299 163764298620127178881950449)
              ·
                refine ⟨122823223965095384161462837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163764298620127178881950449 122823223965095384161462837)
                ·
                  refine ⟨11514677246727692265137141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122823223965095384161462837 11514677246727692265137141)
                  ·
                    refine ⟨1079500991880721149856607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11514677246727692265137141 1079500991880721149856607)
                    ·
                      rfl

theorem cell22_3153481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_3153481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153481 prefixEnd_3153481 := by exact prefixLift 3153481
  have htrace : WordTrace (prefixWord ++ tailWord_3153481) baseStart_3153481 baseEnd_3153481 := by
    simpa [prefixWord, tailWord_3153481, baseEnd_3153481] using wordTrace_append hprefix tailTrace_3153481
  have hstable : (prefixWord ++ tailWord_3153481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153481).length < 2 ^ (prefixWord ++ tailWord_3153481).sum := by decide
  have hdescent : baseEnd_3153481 < baseStart_3153481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153498 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 6, 3]
def baseStart_3153498 : Nat := 118140960795 + 3153498 * 2 ^ 59
def prefixEnd_3153498 : Nat := 4983230072969 + 3 ^ 40 * 3153498 * 2
def baseEnd_3153498 : Nat := 1079506811328138772181555

theorem tailTrace_3153498 : CollatzResearch.WordTrace tailWord_3153498 prefixEnd_3153498 1079506811328138772181555 := by
  unfold tailWord_3153498
  simp only [CollatzResearch.WordTrace]
  refine ⟨28754380282355698856349287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76678347419615196950264765 28754380282355698856349287)
  ·
    refine ⟨43131570423533548284523931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28754380282355698856349287 43131570423533548284523931)
    ·
      refine ⟨64697355635300322426785897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43131570423533548284523931 64697355635300322426785897)
      ·
        refine ⟨48523016726475241820089423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64697355635300322426785897 48523016726475241820089423)
        ·
          refine ⟨72784525089712862730134135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48523016726475241820089423 72784525089712862730134135)
          ·
            refine ⟨109176787634569294095201203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72784525089712862730134135 109176787634569294095201203)
            ·
              refine ⟨163765181451853941142801805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109176787634569294095201203 163765181451853941142801805)
              ·
                refine ⟨61411943044445227928550677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163765181451853941142801805 61411943044445227928550677)
                ·
                  refine ⟨2878684830208370059150813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61411943044445227928550677 2878684830208370059150813)
                  ·
                    refine ⟨1079506811328138772181555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2878684830208370059150813 1079506811328138772181555)
                    ·
                      rfl

theorem cell22_3153498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_3153498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153498 prefixEnd_3153498 := by exact prefixLift 3153498
  have htrace : WordTrace (prefixWord ++ tailWord_3153498) baseStart_3153498 baseEnd_3153498 := by
    simpa [prefixWord, tailWord_3153498, baseEnd_3153498] using wordTrace_append hprefix tailTrace_3153498
  have hstable : (prefixWord ++ tailWord_3153498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153498).length < 2 ^ (prefixWord ++ tailWord_3153498).sum := by decide
  have hdescent : baseEnd_3153498 < baseStart_3153498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153513 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 2, 4]
def baseStart_3153513 : Nat := 118140960795 + 3153513 * 2 ^ 59
def prefixEnd_3153513 : Nat := 4983230072969 + 3 ^ 40 * 3153513 * 2
def baseEnd_3153513 : Nat := 1079511946134683733056509

theorem tailTrace_3153513 : CollatzResearch.WordTrace tailWord_3153513 prefixEnd_3153513 1079511946134683733056509 := by
  unfold tailWord_3153513
  simp only [CollatzResearch.WordTrace]
  refine ⟨115018068224368452987193193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76678712149578968658128795 115018068224368452987193193)
  ·
    refine ⟨86263551168276339740394895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115018068224368452987193193 86263551168276339740394895)
    ·
      refine ⟨129395326752414509610592343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86263551168276339740394895 129395326752414509610592343)
      ·
        refine ⟨194092990128621764415888515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129395326752414509610592343 194092990128621764415888515)
        ·
          refine ⟨291139485192932646623832773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194092990128621764415888515 291139485192932646623832773)
          ·
            refine ⟨54588653473674871241968645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291139485192932646623832773 54588653473674871241968645)
            ·
              refine ⟨10235372526314038357869121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54588653473674871241968645 10235372526314038357869121)
              ·
                refine ⟨7676529394735528768401841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10235372526314038357869121 7676529394735528768401841)
                ·
                  refine ⟨5757397046051646576301381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7676529394735528768401841 5757397046051646576301381)
                  ·
                    refine ⟨1079511946134683733056509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5757397046051646576301381 1079511946134683733056509)
                    ·
                      rfl

theorem cell22_3153513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_3153513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153513 prefixEnd_3153513 := by exact prefixLift 3153513
  have htrace : WordTrace (prefixWord ++ tailWord_3153513) baseStart_3153513 baseEnd_3153513 := by
    simpa [prefixWord, tailWord_3153513, baseEnd_3153513] using wordTrace_append hprefix tailTrace_3153513
  have hstable : (prefixWord ++ tailWord_3153513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153513).length < 2 ^ (prefixWord ++ tailWord_3153513).sum := by decide
  have hdescent : baseEnd_3153513 < baseStart_3153513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153517 : List Nat := [1, 5, 1, 1, 4, 1, 1, 4, 4]
def baseStart_3153517 : Nat := 118140960795 + 3153517 * 2 ^ 59
def prefixEnd_3153517 : Nat := 4983230072969 + 3 ^ 40 * 3153517 * 2
def baseEnd_3153517 : Nat := 359837771805476351985499

theorem tailTrace_3153517 : CollatzResearch.WordTrace tailWord_3153517 prefixEnd_3153517 359837771805476351985499 := by
  unfold tailWord_3153517
  simp only [CollatzResearch.WordTrace]
  refine ⟨115018214116353961670338805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76678809410902641113559203 115018214116353961670338805)
  ·
    refine ⟨10782957573408183906594263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115018214116353961670338805 10782957573408183906594263)
    ·
      refine ⟨16174436360112275859891395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10782957573408183906594263 16174436360112275859891395)
      ·
        refine ⟨24261654540168413789837093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16174436360112275859891395 24261654540168413789837093)
        ·
          refine ⟨4549060226281577585594455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24261654540168413789837093 4549060226281577585594455)
          ·
            refine ⟨6823590339422366378391683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4549060226281577585594455 6823590339422366378391683)
            ·
              refine ⟨10235385509133549567587525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6823590339422366378391683 10235385509133549567587525)
              ·
                refine ⟨1919134782962540543922661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10235385509133549567587525 1919134782962540543922661)
                ·
                  refine ⟨359837771805476351985499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1919134782962540543922661 359837771805476351985499)
                  ·
                    rfl

theorem cell22_3153517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_3153517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153517 prefixEnd_3153517 := by exact prefixLift 3153517
  have htrace : WordTrace (prefixWord ++ tailWord_3153517) baseStart_3153517 baseEnd_3153517 := by
    simpa [prefixWord, tailWord_3153517, baseEnd_3153517] using wordTrace_append hprefix tailTrace_3153517
  have hstable : (prefixWord ++ tailWord_3153517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153517).length < 2 ^ (prefixWord ++ tailWord_3153517).sum := by decide
  have hdescent : baseEnd_3153517 < baseStart_3153517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153628 : List Nat := [2, 2, 5, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3153628 : Nat := 118140960795 + 3153628 * 2 ^ 59
def prefixEnd_3153628 : Nat := 4983230072969 + 3 ^ 40 * 3153628 * 2
def baseEnd_3153628 : Nat := 1079551312984861766431157

theorem tailTrace_3153628 : CollatzResearch.WordTrace tailWord_3153628 prefixEnd_3153628 1079551312984861766431157 := by
  unfold tailWord_3153628
  simp only [CollatzResearch.WordTrace]
  refine ⟨57511131309475913813814769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76681508412634551751753025 57511131309475913813814769)
  ·
    refine ⟨43133348482106935360361077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57511131309475913813814769 43133348482106935360361077)
    ·
      refine ⟨4043751420197525190033851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43133348482106935360361077 4043751420197525190033851)
      ·
        refine ⟨6065627130296287785050777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4043751420197525190033851 6065627130296287785050777)
        ·
          refine ⟨4549220347722215838788083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6065627130296287785050777 4549220347722215838788083)
          ·
            refine ⟨6823830521583323758182125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4549220347722215838788083 6823830521583323758182125)
            ·
              refine ⟨2558936445593746409318297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6823830521583323758182125 2558936445593746409318297)
              ·
                refine ⟨1919202334195309806988723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2558936445593746409318297 1919202334195309806988723)
                ·
                  refine ⟨2878803501292964710483085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919202334195309806988723 2878803501292964710483085)
                  ·
                    refine ⟨1079551312984861766431157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2878803501292964710483085 1079551312984861766431157)
                    ·
                      rfl

theorem cell22_3153628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3153628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153628 prefixEnd_3153628 := by exact prefixLift 3153628
  have htrace : WordTrace (prefixWord ++ tailWord_3153628) baseStart_3153628 baseEnd_3153628 := by
    simpa [prefixWord, tailWord_3153628, baseEnd_3153628] using wordTrace_append hprefix tailTrace_3153628
  have hstable : (prefixWord ++ tailWord_3153628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153628).length < 2 ^ (prefixWord ++ tailWord_3153628).sum := by decide
  have hdescent : baseEnd_3153628 < baseStart_3153628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153648 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 1, 6]
def baseStart_3153648 : Nat := 118140960795 + 3153648 * 2 ^ 59
def prefixEnd_3153648 : Nat := 4983230072969 + 3 ^ 40 * 3153648 * 2
def baseEnd_3153648 : Nat := 1079558159393588380931095

theorem tailTrace_3153648 : CollatzResearch.WordTrace tailWord_3153648 prefixEnd_3153648 1079558159393588380931095 := by
  unfold tailWord_3153648
  simp only [CollatzResearch.WordTrace]
  refine ⟨57511496039439685521678799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76681994719252914028905065 57511496039439685521678799)
  ·
    refine ⟨86267244059159528282518199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57511496039439685521678799 86267244059159528282518199)
    ·
      refine ⟨129400866088739292423777299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86267244059159528282518199 129400866088739292423777299)
      ·
        refine ⟨194101299133108938635665949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129400866088739292423777299 194101299133108938635665949)
        ·
          refine ⟨72787987174915851988374731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194101299133108938635665949 72787987174915851988374731)
          ·
            refine ⟨109181980762373777982562097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72787987174915851988374731 109181980762373777982562097)
            ·
              refine ⟨81886485571780333486921573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109181980762373777982562097 81886485571780333486921573)
              ·
                refine ⟨15353716044708812528797795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81886485571780333486921573 15353716044708812528797795)
                ·
                  refine ⟨23030574067063218793196693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15353716044708812528797795 23030574067063218793196693)
                  ·
                    refine ⟨1079558159393588380931095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23030574067063218793196693 1079558159393588380931095)
                    ·
                      rfl

theorem cell22_3153648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_3153648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153648 prefixEnd_3153648 := by exact prefixLift 3153648
  have htrace : WordTrace (prefixWord ++ tailWord_3153648) baseStart_3153648 baseEnd_3153648 := by
    simpa [prefixWord, tailWord_3153648, baseEnd_3153648] using wordTrace_append hprefix tailTrace_3153648
  have hstable : (prefixWord ++ tailWord_3153648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153648).length < 2 ^ (prefixWord ++ tailWord_3153648).sum := by decide
  have hdescent : baseEnd_3153648 < baseStart_3153648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153650 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_3153650 : Nat := 118140960795 + 3153650 * 2 ^ 59
def prefixEnd_3153650 : Nat := 4983230072969 + 3 ^ 40 * 3153650 * 2
def baseEnd_3153650 : Nat := 1079558844034461042381089

theorem tailTrace_3153650 : CollatzResearch.WordTrace tailWord_3153650 prefixEnd_3153650 1079558844034461042381089 := by
  unfold tailWord_3153650
  simp only [CollatzResearch.WordTrace]
  refine ⟨28755766256218031346232601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76682043349914750256620269 28755766256218031346232601)
  ·
    refine ⟨21566824692163523509674451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28755766256218031346232601 21566824692163523509674451)
    ·
      refine ⟨32350237038245285264511677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21566824692163523509674451 32350237038245285264511677)
      ·
        refine ⟨12131338889341981974191879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32350237038245285264511677 12131338889341981974191879)
        ·
          refine ⟨18197008334012972961287819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12131338889341981974191879 18197008334012972961287819)
          ·
            refine ⟨27295512501019459441931729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18197008334012972961287819 27295512501019459441931729)
            ·
              refine ⟨20471634375764594581448797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27295512501019459441931729 20471634375764594581448797)
              ·
                refine ⟨7676862890911722968043299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20471634375764594581448797 7676862890911722968043299)
                ·
                  refine ⟨11515294336367584452064949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7676862890911722968043299 11515294336367584452064949)
                  ·
                    refine ⟨1079558844034461042381089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11515294336367584452064949 1079558844034461042381089)
                    ·
                      rfl

theorem cell22_3153650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_3153650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153650 prefixEnd_3153650 := by exact prefixLift 3153650
  have htrace : WordTrace (prefixWord ++ tailWord_3153650) baseStart_3153650 baseEnd_3153650 := by
    simpa [prefixWord, tailWord_3153650, baseEnd_3153650] using wordTrace_append hprefix tailTrace_3153650
  have hstable : (prefixWord ++ tailWord_3153650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153650).length < 2 ^ (prefixWord ++ tailWord_3153650).sum := by decide
  have hdescent : baseEnd_3153650 < baseStart_3153650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153654 : List Nat := [5, 1, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_3153654 : Nat := 118140960795 + 3153654 * 2 ^ 59
def prefixEnd_3153654 : Nat := 4983230072969 + 3 ^ 40 * 3153654 * 2
def baseEnd_3153654 : Nat := 1079560213316206365281077

theorem tailTrace_3153654 : CollatzResearch.WordTrace tailWord_3153654 prefixEnd_3153654 1079560213316206365281077 := by
  unfold tailWord_3153654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7188950682303602129254751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76682140611238422712050677 7188950682303602129254751)
  ·
    refine ⟨10783426023455403193882127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7188950682303602129254751 10783426023455403193882127)
    ·
      refine ⟨16175139035183104790823191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10783426023455403193882127 16175139035183104790823191)
      ·
        refine ⟨24262708552774657186234787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16175139035183104790823191 24262708552774657186234787)
        ·
          refine ⟨36394062829161985779352181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24262708552774657186234787 36394062829161985779352181)
          ·
            refine ⟨3411943390233936166814267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36394062829161985779352181 3411943390233936166814267)
            ·
              refine ⟨5117915085350904250221401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411943390233936166814267 5117915085350904250221401)
              ·
                refine ⟨3838436314013178187666051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5117915085350904250221401 3838436314013178187666051)
                ·
                  refine ⟨5757654471019767281499077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838436314013178187666051 5757654471019767281499077)
                  ·
                    refine ⟨1079560213316206365281077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5757654471019767281499077 1079560213316206365281077)
                    ·
                      rfl

theorem cell22_3153654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_3153654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153654 prefixEnd_3153654 := by exact prefixLift 3153654
  have htrace : WordTrace (prefixWord ++ tailWord_3153654) baseStart_3153654 baseEnd_3153654 := by
    simpa [prefixWord, tailWord_3153654, baseEnd_3153654] using wordTrace_append hprefix tailTrace_3153654
  have hstable : (prefixWord ++ tailWord_3153654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153654).length < 2 ^ (prefixWord ++ tailWord_3153654).sum := by decide
  have hdescent : baseEnd_3153654 < baseStart_3153654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153663 : List Nat := [1, 1, 2, 2, 1, 3, 4, 8]
def baseStart_3153663 : Nat := 118140960795 + 3153663 * 2 ^ 59
def prefixEnd_3153663 : Nat := 4983230072969 + 3 ^ 40 * 3153663 * 2
def baseEnd_3153663 : Nat := 119951477133348149089561

theorem tailTrace_3153663 : CollatzResearch.WordTrace tailWord_3153663 prefixEnd_3153663 119951477133348149089561 := by
  unfold tailWord_3153663
  simp only [CollatzResearch.WordTrace]
  refine ⟨115023539173825028605153643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76682359449216685736769095 115023539173825028605153643)
  ·
    refine ⟨172535308760737542907730465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115023539173825028605153643 172535308760737542907730465)
    ·
      refine ⟨129401481570553157180797849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172535308760737542907730465 129401481570553157180797849)
      ·
        refine ⟨97051111177914867885598387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129401481570553157180797849 97051111177914867885598387)
        ·
          refine ⟨145576666766872301828397581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97051111177914867885598387 145576666766872301828397581)
          ·
            refine ⟨54591250037577113185649093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145576666766872301828397581 54591250037577113185649093)
            ·
              refine ⟨10235859382045708722309205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54591250037577113185649093 10235859382045708722309205)
              ·
                refine ⟨119951477133348149089561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10235859382045708722309205 119951477133348149089561)
                ·
                  rfl

theorem cell22_3153663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 8].length) (baseStart_3153663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153663 prefixEnd_3153663 := by exact prefixLift 3153663
  have htrace : WordTrace (prefixWord ++ tailWord_3153663) baseStart_3153663 baseEnd_3153663 := by
    simpa [prefixWord, tailWord_3153663, baseEnd_3153663] using wordTrace_append hprefix tailTrace_3153663
  have hstable : (prefixWord ++ tailWord_3153663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153663).length < 2 ^ (prefixWord ++ tailWord_3153663).sum := by decide
  have hdescent : baseEnd_3153663 < baseStart_3153663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153665 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3153665 : Nat := 118140960795 + 3153665 * 2 ^ 59
def prefixEnd_3153665 : Nat := 4983230072969 + 3 ^ 40 * 3153665 * 2
def baseEnd_3153665 : Nat := 1079563978841006003256043

theorem tailTrace_3153665 : CollatzResearch.WordTrace tailWord_3153665 prefixEnd_3153665 1079563978841006003256043 := by
  unfold tailWord_3153665
  simp only [CollatzResearch.WordTrace]
  refine ⟨115023612119817782946726449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76682408079878521964484299 115023612119817782946726449)
  ·
    refine ⟨86267709089863337210044837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115023612119817782946726449 86267709089863337210044837)
    ·
      refine ⟨16175195454349375726883407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86267709089863337210044837 16175195454349375726883407)
      ·
        refine ⟨24262793181524063590325111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16175195454349375726883407 24262793181524063590325111)
        ·
          refine ⟨36394189772286095385487667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24262793181524063590325111 36394189772286095385487667)
          ·
            refine ⟨54591284658429143078231501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36394189772286095385487667 54591284658429143078231501)
            ·
              refine ⟨20471731746910928654336813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54591284658429143078231501 20471731746910928654336813)
              ·
                refine ⟨7676899405091598245376305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20471731746910928654336813 7676899405091598245376305)
                ·
                  refine ⟨5757674553818698684032229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7676899405091598245376305 5757674553818698684032229)
                  ·
                    refine ⟨1079563978841006003256043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5757674553818698684032229 1079563978841006003256043)
                    ·
                      rfl

theorem cell22_3153665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3153665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153665 prefixEnd_3153665 := by exact prefixLift 3153665
  have htrace : WordTrace (prefixWord ++ tailWord_3153665) baseStart_3153665 baseEnd_3153665 := by
    simpa [prefixWord, tailWord_3153665, baseEnd_3153665] using wordTrace_append hprefix tailTrace_3153665
  have hstable : (prefixWord ++ tailWord_3153665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153665).length < 2 ^ (prefixWord ++ tailWord_3153665).sum := by decide
  have hdescent : baseEnd_3153665 < baseStart_3153665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153772 : List Nat := [2, 2, 1, 1, 4, 2, 1, 4, 1, 4]
def baseStart_3153772 : Nat := 118140960795 + 3153772 * 2 ^ 59
def prefixEnd_3153772 : Nat := 4983230072969 + 3 ^ 40 * 3153772 * 2
def baseEnd_3153772 : Nat := 1079600607127693390830715

theorem tailTrace_3153772 : CollatzResearch.WordTrace tailWord_3153772 prefixEnd_3153772 1079600607127693390830715 := by
  unfold tailWord_3153772
  simp only [CollatzResearch.WordTrace]
  refine ⟨57513757365215070110435785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76685009820286760147247713 57513757365215070110435785)
  ·
    refine ⟨43135318023911302582826839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57513757365215070110435785 43135318023911302582826839)
    ·
      refine ⟨64702977035866953874240259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43135318023911302582826839 64702977035866953874240259)
      ·
        refine ⟨97054465553800430811360389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64702977035866953874240259 97054465553800430811360389)
        ·
          refine ⟨18197712291337580777130073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97054465553800430811360389 18197712291337580777130073)
          ·
            refine ⟨13648284218503185582847555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18197712291337580777130073 13648284218503185582847555)
            ·
              refine ⟨20472426327754778374271333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13648284218503185582847555 20472426327754778374271333)
              ·
                refine ⟨3838579936454020945175875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20472426327754778374271333 3838579936454020945175875)
                ·
                  refine ⟨5757869904681031417763813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838579936454020945175875 5757869904681031417763813)
                  ·
                    refine ⟨1079600607127693390830715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5757869904681031417763813 1079600607127693390830715)
                    ·
                      rfl

theorem cell22_3153772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_3153772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153772 prefixEnd_3153772 := by exact prefixLift 3153772
  have htrace : WordTrace (prefixWord ++ tailWord_3153772) baseStart_3153772 baseEnd_3153772 := by
    simpa [prefixWord, tailWord_3153772, baseEnd_3153772] using wordTrace_append hprefix tailTrace_3153772
  have hstable : (prefixWord ++ tailWord_3153772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153772).length < 2 ^ (prefixWord ++ tailWord_3153772).sum := by decide
  have hdescent : baseEnd_3153772 < baseStart_3153772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153785 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 3, 5]
def baseStart_3153785 : Nat := 118140960795 + 3153785 * 2 ^ 59
def prefixEnd_3153785 : Nat := 4983230072969 + 3 ^ 40 * 3153785 * 2
def baseEnd_3153785 : Nat := 1079605057293365690255675

theorem tailTrace_3153785 : CollatzResearch.WordTrace tailWord_3153785 prefixEnd_3153785 1079605057293365690255675 := by
  unfold tailWord_3153785
  simp only [CollatzResearch.WordTrace]
  refine ⟨115027988879383043441094809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76685325919588695627396539 115027988879383043441094809)
  ·
    refine ⟨86270991659537282580821107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115027988879383043441094809 86270991659537282580821107)
    ·
      refine ⟨129406487489305923871231661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86270991659537282580821107 129406487489305923871231661)
      ·
        refine ⟨48527432808489721451711873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129406487489305923871231661 48527432808489721451711873)
        ·
          refine ⟨36395574606367291088783905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48527432808489721451711873 36395574606367291088783905)
          ·
            refine ⟨27296680954775468316587929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36395574606367291088783905 27296680954775468316587929)
            ·
              refine ⟨20472510716081601237440947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27296680954775468316587929 20472510716081601237440947)
              ·
                refine ⟨30708766074122401856161421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20472510716081601237440947 30708766074122401856161421)
                ·
                  refine ⟨11515787277795900696060533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30708766074122401856161421 11515787277795900696060533)
                  ·
                    refine ⟨1079605057293365690255675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11515787277795900696060533 1079605057293365690255675)
                    ·
                      rfl

theorem cell22_3153785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_3153785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153785 prefixEnd_3153785 := by exact prefixLift 3153785
  have htrace : WordTrace (prefixWord ++ tailWord_3153785) baseStart_3153785 baseEnd_3153785 := by
    simpa [prefixWord, tailWord_3153785, baseEnd_3153785] using wordTrace_append hprefix tailTrace_3153785
  have hstable : (prefixWord ++ tailWord_3153785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153785).length < 2 ^ (prefixWord ++ tailWord_3153785).sum := by decide
  have hdescent : baseEnd_3153785 < baseStart_3153785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153815 : List Nat := [1, 1, 3, 3, 1, 3, 1, 9]
def baseStart_3153815 : Nat := 118140960795 + 3153815 * 2 ^ 59
def prefixEnd_3153815 : Nat := 4983230072969 + 3 ^ 40 * 3153815 * 2
def baseEnd_3153815 : Nat := 119957258545161734667287

theorem tailTrace_3153815 : CollatzResearch.WordTrace tailWord_3153815 prefixEnd_3153815 119957258545161734667287 := by
  unfold tailWord_3153815
  simp only [CollatzResearch.WordTrace]
  refine ⟨115029083069274358564686899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76686055379516239043124599 115029083069274358564686899)
  ·
    refine ⟨172543624603911537847030349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115029083069274358564686899 172543624603911537847030349)
    ·
      refine ⟨64703859226466826692636381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172543624603911537847030349 64703859226466826692636381)
      ·
        refine ⟨24263947209925060009738643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64703859226466826692636381 24263947209925060009738643)
        ·
          refine ⟨36395920814887590014607965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24263947209925060009738643 36395920814887590014607965)
          ·
            refine ⟨13648470305582846255477987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36395920814887590014607965 13648470305582846255477987)
            ·
              refine ⟨20472705458374269383216981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13648470305582846255477987 20472705458374269383216981)
              ·
                refine ⟨119957258545161734667287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20472705458374269383216981 119957258545161734667287)
                ·
                  rfl

theorem cell22_3153815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 9].length) (baseStart_3153815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153815 prefixEnd_3153815 := by exact prefixLift 3153815
  have htrace : WordTrace (prefixWord ++ tailWord_3153815) baseStart_3153815 baseEnd_3153815 := by
    simpa [prefixWord, tailWord_3153815, baseEnd_3153815] using wordTrace_append hprefix tailTrace_3153815
  have hstable : (prefixWord ++ tailWord_3153815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153815).length < 2 ^ (prefixWord ++ tailWord_3153815).sum := by decide
  have hdescent : baseEnd_3153815 < baseStart_3153815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153941 : List Nat := [1, 3, 2, 1, 5, 1, 2, 2, 1, 4]
def baseStart_3153941 : Nat := 118140960795 + 3153941 * 2 ^ 59
def prefixEnd_3153941 : Nat := 4983230072969 + 3 ^ 40 * 3153941 * 2
def baseEnd_3153941 : Nat := 1079658459281433283355197

theorem tailTrace_3153941 : CollatzResearch.WordTrace tailWord_3153941 prefixEnd_3153941 1079658459281433283355197 := by
  unfold tailWord_3153941
  simp only [CollatzResearch.WordTrace]
  refine ⟨115033678666817882083773677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76689119111211921389182451 115033678666817882083773677)
  ·
    refine ⟨43137629500056705781415129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115033678666817882083773677 43137629500056705781415129)
    ·
      refine ⟨32353222125042529336061347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43137629500056705781415129 32353222125042529336061347)
      ·
        refine ⟨48529833187563794004092021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32353222125042529336061347 48529833187563794004092021)
        ·
          refine ⟨4549671861334105687883627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48529833187563794004092021 4549671861334105687883627)
          ·
            refine ⟨6824507792001158531825441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4549671861334105687883627 6824507792001158531825441)
            ·
              refine ⟨5118380844000868898869081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6824507792001158531825441 5118380844000868898869081)
              ·
                refine ⟨3838785633000651674151811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5118380844000868898869081 3838785633000651674151811)
                ·
                  refine ⟨5758178449500977511227717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838785633000651674151811 5758178449500977511227717)
                  ·
                    refine ⟨1079658459281433283355197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5758178449500977511227717 1079658459281433283355197)
                    ·
                      rfl

theorem cell22_3153941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_3153941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153941 prefixEnd_3153941 := by exact prefixLift 3153941
  have htrace : WordTrace (prefixWord ++ tailWord_3153941) baseStart_3153941 baseEnd_3153941 := by
    simpa [prefixWord, tailWord_3153941, baseEnd_3153941] using wordTrace_append hprefix tailTrace_3153941
  have hstable : (prefixWord ++ tailWord_3153941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153941).length < 2 ^ (prefixWord ++ tailWord_3153941).sum := by decide
  have hdescent : baseEnd_3153941 < baseStart_3153941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153954 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_3153954 : Nat := 118140960795 + 3153954 * 2 ^ 59
def prefixEnd_3153954 : Nat := 4983230072969 + 3 ^ 40 * 3153954 * 2
def baseEnd_3153954 : Nat := 1079662909447105582780157

theorem tailTrace_3153954 : CollatzResearch.WordTrace tailWord_3153954 prefixEnd_3153954 1079662909447105582780157 := by
  unfold tailWord_3153954
  simp only [CollatzResearch.WordTrace]
  refine ⟨28758538203942696325999229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76689435210513856869331277 28758538203942696325999229)
  ·
    refine ⟨10784451826478511122249711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28758538203942696325999229 10784451826478511122249711)
    ·
      refine ⟨16176677739717766683374567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10784451826478511122249711 16176677739717766683374567)
      ·
        refine ⟨24265016609576650025061851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16176677739717766683374567 24265016609576650025061851)
        ·
          refine ⟨36397524914364975037592777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24265016609576650025061851 36397524914364975037592777)
          ·
            refine ⟨27298143685773731278194583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36397524914364975037592777 27298143685773731278194583)
            ·
              refine ⟨40947215528660596917291875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27298143685773731278194583 40947215528660596917291875)
              ·
                refine ⟨61420823292990895375937813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40947215528660596917291875 61420823292990895375937813)
                ·
                  refine ⟨2879101091858948220747085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61420823292990895375937813 2879101091858948220747085)
                  ·
                    refine ⟨1079662909447105582780157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2879101091858948220747085 1079662909447105582780157)
                    ·
                      rfl

theorem cell22_3153954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_3153954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153954 prefixEnd_3153954 := by exact prefixLift 3153954
  have htrace : WordTrace (prefixWord ++ tailWord_3153954) baseStart_3153954 baseEnd_3153954 := by
    simpa [prefixWord, tailWord_3153954, baseEnd_3153954] using wordTrace_append hprefix tailTrace_3153954
  have hstable : (prefixWord ++ tailWord_3153954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153954).length < 2 ^ (prefixWord ++ tailWord_3153954).sum := by decide
  have hdescent : baseEnd_3153954 < baseStart_3153954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3153969 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 2, 4]
def baseStart_3153969 : Nat := 118140960795 + 3153969 * 2 ^ 59
def prefixEnd_3153969 : Nat := 4983230072969 + 3 ^ 40 * 3153969 * 2
def baseEnd_3153969 : Nat := 1079668044253650543655111

theorem tailTrace_3153969 : CollatzResearch.WordTrace tailWord_3153969 prefixEnd_3153969 1079668044253650543655111 := by
  unfold tailWord_3153969
  simp only [CollatzResearch.WordTrace]
  refine ⟨115034699910716442865792961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76689799940477628577195307 115034699910716442865792961)
  ·
    refine ⟨86276024933037332149344721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115034699910716442865792961 86276024933037332149344721)
    ·
      refine ⟨64707018699777999112008541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86276024933037332149344721 64707018699777999112008541)
      ·
        refine ⟨24265132012416749667003203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64707018699777999112008541 24265132012416749667003203)
        ·
          refine ⟨36397698018625124500504805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24265132012416749667003203 36397698018625124500504805)
          ·
            refine ⟨6824568378492210843844651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36397698018625124500504805 6824568378492210843844651)
            ·
              refine ⟨10236852567738316265766977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6824568378492210843844651 10236852567738316265766977)
              ·
                refine ⟨7677639425803737199325233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10236852567738316265766977 7677639425803737199325233)
                ·
                  refine ⟨5758229569352802899493925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7677639425803737199325233 5758229569352802899493925)
                  ·
                    refine ⟨1079668044253650543655111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5758229569352802899493925 1079668044253650543655111)
                    ·
                      rfl

theorem cell22_3153969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_3153969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3153969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3153969 prefixEnd_3153969 := by exact prefixLift 3153969
  have htrace : WordTrace (prefixWord ++ tailWord_3153969) baseStart_3153969 baseEnd_3153969 := by
    simpa [prefixWord, tailWord_3153969, baseEnd_3153969] using wordTrace_append hprefix tailTrace_3153969
  have hstable : (prefixWord ++ tailWord_3153969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3153969).length < 2 ^ (prefixWord ++ tailWord_3153969).sum := by decide
  have hdescent : baseEnd_3153969 < baseStart_3153969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3153969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154044 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_3154044 : Nat := 118140960795 + 3154044 * 2 ^ 59
def prefixEnd_3154044 : Nat := 4983230072969 + 3 ^ 40 * 3154044 * 2
def baseEnd_3154044 : Nat := 1079693718286375348029881

theorem tailTrace_3154044 : CollatzResearch.WordTrace tailWord_3154044 prefixEnd_3154044 1079693718286375348029881 := by
  unfold tailWord_3154044
  simp only [CollatzResearch.WordTrace]
  refine ⟨57518717692722365337386593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76691623590296487116515457 57518717692722365337386593)
  ·
    refine ⟨43139038269541774003039945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57518717692722365337386593 43139038269541774003039945)
    ·
      refine ⟨32354278702156330502279959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43139038269541774003039945 32354278702156330502279959)
      ·
        refine ⟨48531418053234495753419939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32354278702156330502279959 48531418053234495753419939)
        ·
          refine ⟨72797127079851743630129909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48531418053234495753419939 72797127079851743630129909)
          ·
            refine ⟨6824730663736100965324679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72797127079851743630129909 6824730663736100965324679)
            ·
              refine ⟨10237095995604151447987019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6824730663736100965324679 10237095995604151447987019)
              ·
                refine ⟨15355643993406227171980529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10237095995604151447987019 15355643993406227171980529)
                ·
                  refine ⟨11516732995054670378985397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15355643993406227171980529 11516732995054670378985397)
                  ·
                    refine ⟨1079693718286375348029881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11516732995054670378985397 1079693718286375348029881)
                    ·
                      rfl

theorem cell22_3154044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_3154044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154044 prefixEnd_3154044 := by exact prefixLift 3154044
  have htrace : WordTrace (prefixWord ++ tailWord_3154044) baseStart_3154044 baseEnd_3154044 := by
    simpa [prefixWord, tailWord_3154044, baseEnd_3154044] using wordTrace_append hprefix tailTrace_3154044
  have hstable : (prefixWord ++ tailWord_3154044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154044).length < 2 ^ (prefixWord ++ tailWord_3154044).sum := by decide
  have hdescent : baseEnd_3154044 < baseStart_3154044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154076 : List Nat := [2, 2, 3, 2, 1, 1, 3, 3, 1, 4]
def baseStart_3154076 : Nat := 118140960795 + 3154076 * 2 ^ 59
def prefixEnd_3154076 : Nat := 4983230072969 + 3 ^ 40 * 3154076 * 2
def baseEnd_3154076 : Nat := 1079704672540337931229783

theorem tailTrace_3154076 : CollatzResearch.WordTrace tailWord_3154076 prefixEnd_3154076 1079704672540337931229783 := by
  unfold tailWord_3154076
  simp only [CollatzResearch.WordTrace]
  refine ⟨57519301260664400069969041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76692401680885866759958721 57519301260664400069969041)
  ·
    refine ⟨43139475945498300052476781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57519301260664400069969041 43139475945498300052476781)
    ·
      refine ⟨16177303479561862519678793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43139475945498300052476781 16177303479561862519678793)
      ·
        refine ⟨12132977609671396889759095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16177303479561862519678793 12132977609671396889759095)
        ·
          refine ⟨18199466414507095334638643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12132977609671396889759095 18199466414507095334638643)
          ·
            refine ⟨27299199621760643001957965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18199466414507095334638643 27299199621760643001957965)
            ·
              refine ⟨10237199858160241125734237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27299199621760643001957965 10237199858160241125734237)
              ·
                refine ⟨3838949946810090422150339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10237199858160241125734237 3838949946810090422150339)
                ·
                  refine ⟨5758424920215135633225509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3838949946810090422150339 5758424920215135633225509)
                  ·
                    refine ⟨1079704672540337931229783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5758424920215135633225509 1079704672540337931229783)
                    ·
                      rfl

theorem cell22_3154076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_3154076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154076 prefixEnd_3154076 := by exact prefixLift 3154076
  have htrace : WordTrace (prefixWord ++ tailWord_3154076) baseStart_3154076 baseEnd_3154076 := by
    simpa [prefixWord, tailWord_3154076, baseEnd_3154076] using wordTrace_append hprefix tailTrace_3154076
  have hstable : (prefixWord ++ tailWord_3154076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154076).length < 2 ^ (prefixWord ++ tailWord_3154076).sum := by decide
  have hdescent : baseEnd_3154076 < baseStart_3154076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154106 : List Nat := [3, 1, 1, 1, 2, 2, 2, 5, 2, 3]
def baseStart_3154106 : Nat := 118140960795 + 3154106 * 2 ^ 59
def prefixEnd_3154106 : Nat := 4983230072969 + 3 ^ 40 * 3154106 * 2
def baseEnd_3154106 : Nat := 1079714942153427852979691

theorem tailTrace_3154106 : CollatzResearch.WordTrace tailWord_3154106 prefixEnd_3154106 1079714942153427852979691 := by
  unfold tailWord_3154106
  simp only [CollatzResearch.WordTrace]
  refine ⟨28759924177805028815882543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76693131140813410175686781 28759924177805028815882543)
  ·
    refine ⟨43139886266707543223823815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28759924177805028815882543 43139886266707543223823815)
    ·
      refine ⟨64709829400061314835735723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43139886266707543223823815 64709829400061314835735723)
      ·
        refine ⟨97064744100091972253603585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64709829400061314835735723 97064744100091972253603585)
        ·
          refine ⟨72798558075068979190202689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97064744100091972253603585 72798558075068979190202689)
          ·
            refine ⟨54598918556301734392652017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72798558075068979190202689 54598918556301734392652017)
            ·
              refine ⟨40949188917226300794489013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54598918556301734392652017 40949188917226300794489013)
              ·
                refine ⟨3838986460989965699483345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40949188917226300794489013 3838986460989965699483345)
                ·
                  refine ⟨2879239845742474274612509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3838986460989965699483345 2879239845742474274612509)
                  ·
                    refine ⟨1079714942153427852979691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2879239845742474274612509 1079714942153427852979691)
                    ·
                      rfl

theorem cell22_3154106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_3154106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154106 prefixEnd_3154106 := by exact prefixLift 3154106
  have htrace : WordTrace (prefixWord ++ tailWord_3154106) baseStart_3154106 baseEnd_3154106 := by
    simpa [prefixWord, tailWord_3154106, baseEnd_3154106] using wordTrace_append hprefix tailTrace_3154106
  have hstable : (prefixWord ++ tailWord_3154106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154106).length < 2 ^ (prefixWord ++ tailWord_3154106).sum := by decide
  have hdescent : baseEnd_3154106 < baseStart_3154106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154157 : List Nat := [1, 5, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_3154157 : Nat := 118140960795 + 3154157 * 2 ^ 59
def prefixEnd_3154157 : Nat := 4983230072969 + 3 ^ 40 * 3154157 * 2
def baseEnd_3154157 : Nat := 1079732400495680719954535

theorem tailTrace_3154157 : CollatzResearch.WordTrace tailWord_3154157 prefixEnd_3154157 1079732400495680719954535 := by
  unfold tailWord_3154157
  simp only [CollatzResearch.WordTrace]
  refine ⟨115041556834035350973636725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76694371222690233982424483 115041556834035350973636725)
  ·
    refine ⟨10785145953190814153778443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115041556834035350973636725 10785145953190814153778443)
    ·
      refine ⟨16177718929786221230667665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10785145953190814153778443 16177718929786221230667665)
      ·
        refine ⟨12133289197339665923000749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16177718929786221230667665 12133289197339665923000749)
        ·
          refine ⟨4549983449002374721125281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12133289197339665923000749 4549983449002374721125281)
          ·
            refine ⟨3412487586751781040843961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4549983449002374721125281 3412487586751781040843961)
            ·
              refine ⟨2559365690063835780632971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3412487586751781040843961 2559365690063835780632971)
              ·
                refine ⟨3839048535095753670949457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2559365690063835780632971 3839048535095753670949457)
                ·
                  refine ⟨2879286401321815253212093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3839048535095753670949457 2879286401321815253212093)
                  ·
                    refine ⟨1079732400495680719954535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2879286401321815253212093 1079732400495680719954535)
                    ·
                      rfl

theorem cell22_3154157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_3154157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154157 prefixEnd_3154157 := by exact prefixLift 3154157
  have htrace : WordTrace (prefixWord ++ tailWord_3154157) baseStart_3154157 baseEnd_3154157 := by
    simpa [prefixWord, tailWord_3154157, baseEnd_3154157] using wordTrace_append hprefix tailTrace_3154157
  have hstable : (prefixWord ++ tailWord_3154157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154157).length < 2 ^ (prefixWord ++ tailWord_3154157).sum := by decide
  have hdescent : baseEnd_3154157 < baseStart_3154157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154228 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3154228 : Nat := 118140960795 + 3154228 * 2 ^ 59
def prefixEnd_3154228 : Nat := 4983230072969 + 3 ^ 40 * 3154228 * 2
def baseEnd_3154228 : Nat := 1079756705246660201429317

theorem tailTrace_3154228 : CollatzResearch.WordTrace tailWord_3154228 prefixEnd_3154228 1079756705246660201429317 := by
  unfold tailWord_3154228
  simp only [CollatzResearch.WordTrace]
  refine ⟨57522073208389065049735669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76696097611185420066314225 57522073208389065049735669)
  ·
    refine ⟨5392694363286474848412719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57522073208389065049735669 5392694363286474848412719)
    ·
      refine ⟨8089041544929712272619079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5392694363286474848412719 8089041544929712272619079)
      ·
        refine ⟨12133562317394568408928619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8089041544929712272619079 12133562317394568408928619)
        ·
          refine ⟨18200343476091852613392929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12133562317394568408928619 18200343476091852613392929)
          ·
            refine ⟨13650257607068889460044697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18200343476091852613392929 13650257607068889460044697)
            ·
              refine ⟨10237693205301667095033523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13650257607068889460044697 10237693205301667095033523)
              ·
                refine ⟨15356539807952500642550285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10237693205301667095033523 15356539807952500642550285)
                ·
                  refine ⟨5758702427982187740956357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15356539807952500642550285 5758702427982187740956357)
                  ·
                    refine ⟨1079756705246660201429317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5758702427982187740956357 1079756705246660201429317)
                    ·
                      rfl

theorem cell22_3154228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3154228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154228 prefixEnd_3154228 := by exact prefixLift 3154228
  have htrace : WordTrace (prefixWord ++ tailWord_3154228) baseStart_3154228 baseEnd_3154228 := by
    simpa [prefixWord, tailWord_3154228, baseEnd_3154228] using wordTrace_append hprefix tailTrace_3154228
  have hstable : (prefixWord ++ tailWord_3154228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154228).length < 2 ^ (prefixWord ++ tailWord_3154228).sum := by decide
  have hdescent : baseEnd_3154228 < baseStart_3154228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154275 : List Nat := [1, 1, 1, 5, 2, 1, 5, 1, 2, 3]
def baseStart_3154275 : Nat := 118140960795 + 3154275 * 2 ^ 59
def prefixEnd_3154275 : Nat := 4983230072969 + 3 ^ 40 * 3154275 * 2
def baseEnd_3154275 : Nat := 1079772794307167745504173

theorem tailTrace_3154275 : CollatzResearch.WordTrace tailWord_3154275 prefixEnd_3154275 1079772794307167745504173 := by
  unfold tailWord_3154275
  simp only [CollatzResearch.WordTrace]
  refine ⟨115045860647607857126432279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76697240431738571417621519 115045860647607857126432279)
  ·
    refine ⟨172568790971411785689648419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115045860647607857126432279 172568790971411785689648419)
    ·
      refine ⟨258853186457117678534472629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172568790971411785689648419 258853186457117678534472629)
      ·
        refine ⟨24267486230354782362606809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 258853186457117678534472629 24267486230354782362606809)
        ·
          refine ⟨18200614672766086771955107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24267486230354782362606809 18200614672766086771955107)
          ·
            refine ⟨27300922009149130157932661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18200614672766086771955107 27300922009149130157932661)
            ·
              refine ⟨2559461438357730952306187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27300922009149130157932661 2559461438357730952306187)
              ·
                refine ⟨3839192157536596428459281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2559461438357730952306187 3839192157536596428459281)
                ·
                  refine ⟨2879394118152447321344461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3839192157536596428459281 2879394118152447321344461)
                  ·
                    refine ⟨1079772794307167745504173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2879394118152447321344461 1079772794307167745504173)
                    ·
                      rfl

theorem cell22_3154275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 2, 3].length) (baseStart_3154275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154275 prefixEnd_3154275 := by exact prefixLift 3154275
  have htrace : WordTrace (prefixWord ++ tailWord_3154275) baseStart_3154275 baseEnd_3154275 := by
    simpa [prefixWord, tailWord_3154275, baseEnd_3154275] using wordTrace_append hprefix tailTrace_3154275
  have hstable : (prefixWord ++ tailWord_3154275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154275).length < 2 ^ (prefixWord ++ tailWord_3154275).sum := by decide
  have hdescent : baseEnd_3154275 < baseStart_3154275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154288 : List Nat := [2, 1, 1, 1, 4, 5, 2, 6]
def baseStart_3154288 : Nat := 118140960795 + 3154288 * 2 ^ 59
def prefixEnd_3154288 : Nat := 4983230072969 + 3 ^ 40 * 3154288 * 2
def baseEnd_3154288 : Nat := 119975249385871116103237

theorem tailTrace_3154288 : CollatzResearch.WordTrace tailWord_3154288 prefixEnd_3154288 119975249385871116103237 := by
  unfold tailWord_3154288
  simp only [CollatzResearch.WordTrace]
  refine ⟨57523167398280380173327759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76697556531040506897770345 57523167398280380173327759)
  ·
    refine ⟨86284751097420570259991639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57523167398280380173327759 86284751097420570259991639)
    ·
      refine ⟨129427126646130855389987459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86284751097420570259991639 129427126646130855389987459)
      ·
        refine ⟨194140689969196283084981189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129427126646130855389987459 194140689969196283084981189)
        ·
          refine ⟨36401379369224303078433973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194140689969196283084981189 36401379369224303078433973)
          ·
            refine ⟨3412629315864778413603185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36401379369224303078433973 3412629315864778413603185)
            ·
              refine ⟨2559471986898583810202389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3412629315864778413603185 2559471986898583810202389)
              ·
                refine ⟨119975249385871116103237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2559471986898583810202389 119975249385871116103237)
                ·
                  rfl

theorem cell22_3154288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 6].length) (baseStart_3154288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154288 prefixEnd_3154288 := by exact prefixLift 3154288
  have htrace : WordTrace (prefixWord ++ tailWord_3154288) baseStart_3154288 baseEnd_3154288 := by
    simpa [prefixWord, tailWord_3154288, baseEnd_3154288] using wordTrace_append hprefix tailTrace_3154288
  have hstable : (prefixWord ++ tailWord_3154288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154288).length < 2 ^ (prefixWord ++ tailWord_3154288).sum := by decide
  have hdescent : baseEnd_3154288 < baseStart_3154288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154294 : List Nat := [5, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_3154294 : Nat := 118140960795 + 3154294 * 2 ^ 59
def prefixEnd_3154294 : Nat := 4983230072969 + 3 ^ 40 * 3154294 * 2
def baseEnd_3154294 : Nat := 359926432798486009759705

theorem tailTrace_3154294 : CollatzResearch.WordTrace tailWord_3154294 prefixEnd_3154294 359926432798486009759705 := by
  unfold tailWord_3154294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7190409602158688960710871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76697702423026015580915957 7190409602158688960710871)
  ·
    refine ⟨10785614403238033441066307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7190409602158688960710871 10785614403238033441066307)
    ·
      refine ⟨16178421604857050161599461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10785614403238033441066307 16178421604857050161599461)
      ·
        refine ⟨3033454050910696905299899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16178421604857050161599461 3033454050910696905299899)
        ·
          refine ⟨4550181076366045357949849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3033454050910696905299899 4550181076366045357949849)
          ·
            refine ⟨3412635807274534018462387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4550181076366045357949849 3412635807274534018462387)
            ·
              refine ⟨5118953710911801027693581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412635807274534018462387 5118953710911801027693581)
              ·
                refine ⟨1919607641591925385385093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5118953710911801027693581 1919607641591925385385093)
                ·
                  refine ⟨359926432798486009759705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1919607641591925385385093 359926432798486009759705)
                  ·
                    rfl

theorem cell22_3154294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_3154294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154294 prefixEnd_3154294 := by exact prefixLift 3154294
  have htrace : WordTrace (prefixWord ++ tailWord_3154294) baseStart_3154294 baseEnd_3154294 := by
    simpa [prefixWord, tailWord_3154294, baseEnd_3154294] using wordTrace_append hprefix tailTrace_3154294
  have hstable : (prefixWord ++ tailWord_3154294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154294).length < 2 ^ (prefixWord ++ tailWord_3154294).sum := by decide
  have hdescent : baseEnd_3154294 < baseStart_3154294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154316 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 7]
def baseStart_3154316 : Nat := 118140960795 + 3154316 * 2 ^ 59
def prefixEnd_3154316 : Nat := 4983230072969 + 3 ^ 40 * 3154316 * 2
def baseEnd_3154316 : Nat := 359928943148352435076349

theorem tailTrace_3154316 : CollatzResearch.WordTrace tailWord_3154316 prefixEnd_3154316 359928943148352435076349 := by
  unfold tailWord_3154316
  simp only [CollatzResearch.WordTrace]
  refine ⟨57523678020229660564337401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76698237360306214085783201 57523678020229660564337401)
  ·
    refine ⟨43142758515172245423253051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57523678020229660564337401 43142758515172245423253051)
    ·
      refine ⟨64714137772758368134879577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43142758515172245423253051 64714137772758368134879577)
      ·
        refine ⟨48535603329568776101159683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64714137772758368134879577 48535603329568776101159683)
        ·
          refine ⟨72803404994353164151739525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48535603329568776101159683 72803404994353164151739525)
          ·
            refine ⟨13650638436441218278451161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72803404994353164151739525 13650638436441218278451161)
            ·
              refine ⟨10237978827330913708838371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13650638436441218278451161 10237978827330913708838371)
              ·
                refine ⟨15356968240996370563257557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10237978827330913708838371 15356968240996370563257557)
                ·
                  refine ⟨359928943148352435076349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15356968240996370563257557 359928943148352435076349)
                  ·
                    rfl

theorem cell22_3154316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_3154316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154316 prefixEnd_3154316 := by exact prefixLift 3154316
  have htrace : WordTrace (prefixWord ++ tailWord_3154316) baseStart_3154316 baseEnd_3154316 := by
    simpa [prefixWord, tailWord_3154316, baseEnd_3154316] using wordTrace_append hprefix tailTrace_3154316
  have hstable : (prefixWord ++ tailWord_3154316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154316).length < 2 ^ (prefixWord ++ tailWord_3154316).sum := by decide
  have hdescent : baseEnd_3154316 < baseStart_3154316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154326 : List Nat := [5, 3, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_3154326 : Nat := 118140960795 + 3154326 * 2 ^ 59
def prefixEnd_3154326 : Nat := 4983230072969 + 3 ^ 40 * 3154326 * 2
def baseEnd_3154326 : Nat := 1079790252649420612479017

theorem tailTrace_3154326 : CollatzResearch.WordTrace tailWord_3154326 prefixEnd_3154326 1079790252649420612479017 := by
  unfold tailWord_3154326
  simp only [CollatzResearch.WordTrace]
  refine ⟨7190482548151443302283677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76698480513615395224359221 7190482548151443302283677)
  ·
    refine ⟨2696430955556791238356379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7190482548151443302283677 2696430955556791238356379)
    ·
      refine ⟨4044646433335186857534569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2696430955556791238356379 4044646433335186857534569)
      ·
        refine ⟨3033484825001390143150927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4044646433335186857534569 3033484825001390143150927)
        ·
          refine ⟨4550227237502085214726391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3033484825001390143150927 4550227237502085214726391)
          ·
            refine ⟨6825340856253127822089587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4550227237502085214726391 6825340856253127822089587)
            ·
              refine ⟨10238011284379691733134381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6825340856253127822089587 10238011284379691733134381)
              ·
                refine ⟨3839254231642384399925393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10238011284379691733134381 3839254231642384399925393)
                ·
                  refine ⟨2879440673731788299944045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3839254231642384399925393 2879440673731788299944045)
                  ·
                    refine ⟨1079790252649420612479017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2879440673731788299944045 1079790252649420612479017)
                    ·
                      rfl

theorem cell22_3154326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_3154326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154326 prefixEnd_3154326 := by exact prefixLift 3154326
  have htrace : WordTrace (prefixWord ++ tailWord_3154326) baseStart_3154326 baseEnd_3154326 := by
    simpa [prefixWord, tailWord_3154326, baseEnd_3154326] using wordTrace_append hprefix tailTrace_3154326
  have hstable : (prefixWord ++ tailWord_3154326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154326).length < 2 ^ (prefixWord ++ tailWord_3154326).sum := by decide
  have hdescent : baseEnd_3154326 < baseStart_3154326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154393 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 1, 5]
def baseStart_3154393 : Nat := 118140960795 + 3154393 * 2 ^ 59
def prefixEnd_3154393 : Nat := 4983230072969 + 3 ^ 40 * 3154393 * 2
def baseEnd_3154393 : Nat := 1079813188118654771053811

theorem tailTrace_3154393 : CollatzResearch.WordTrace tailWord_3154393 prefixEnd_3154393 1079813188118654771053811 := by
  unfold tailWord_3154393
  simp only [CollatzResearch.WordTrace]
  refine ⟨115050164461180363279227833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76700109640786908852818555 115050164461180363279227833)
  ·
    refine ⟨86287623345885272459420875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115050164461180363279227833 86287623345885272459420875)
    ·
      refine ⟨129431435018827908689131313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86287623345885272459420875 129431435018827908689131313)
      ·
        refine ⟨97073576264120931516848485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129431435018827908689131313 97073576264120931516848485)
        ·
          refine ⟨18201295549522674659409091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97073576264120931516848485 18201295549522674659409091)
          ·
            refine ⟨27301943324284011989113637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18201295549522674659409091 27301943324284011989113637)
            ·
              refine ⟨5119114373303252247958807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27301943324284011989113637 5119114373303252247958807)
              ·
                refine ⟨7678671559954878371938211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5119114373303252247958807 7678671559954878371938211)
                ·
                  refine ⟨11518007339932317557907317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7678671559954878371938211 11518007339932317557907317)
                  ·
                    refine ⟨1079813188118654771053811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11518007339932317557907317 1079813188118654771053811)
                    ·
                      rfl

theorem cell22_3154393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_3154393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154393 prefixEnd_3154393 := by exact prefixLift 3154393
  have htrace : WordTrace (prefixWord ++ tailWord_3154393) baseStart_3154393 baseEnd_3154393 := by
    simpa [prefixWord, tailWord_3154393, baseEnd_3154393] using wordTrace_append hprefix tailTrace_3154393
  have hstable : (prefixWord ++ tailWord_3154393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154393).length < 2 ^ (prefixWord ++ tailWord_3154393).sum := by decide
  have hdescent : baseEnd_3154393 < baseStart_3154393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154408 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 1, 6]
def baseStart_3154408 : Nat := 118140960795 + 3154408 * 2 ^ 59
def prefixEnd_3154408 : Nat := 4983230072969 + 3 ^ 40 * 3154408 * 2
def baseEnd_3154408 : Nat := 1079818322925199731928765

theorem tailTrace_3154408 : CollatzResearch.WordTrace tailWord_3154408 prefixEnd_3154408 1079818322925199731928765 := by
  unfold tailWord_3154408
  simp only [CollatzResearch.WordTrace]
  refine ⟨57525355778063010420511939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76700474370750680560682585 57525355778063010420511939)
  ·
    refine ⟨86288033667094515630767909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57525355778063010420511939 86288033667094515630767909)
    ·
      refine ⟨16179006312580221680768983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86288033667094515630767909 16179006312580221680768983)
      ·
        refine ⟨24268509468870332521153475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16179006312580221680768983 24268509468870332521153475)
        ·
          refine ⟨36402764203305498781730213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24268509468870332521153475 36402764203305498781730213)
          ·
            refine ⟨6825518288119781021574415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36402764203305498781730213 6825518288119781021574415)
            ·
              refine ⟨10238277432179671532361623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6825518288119781021574415 10238277432179671532361623)
              ·
                refine ⟨15357416148269507298542435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10238277432179671532361623 15357416148269507298542435)
                ·
                  refine ⟨23036124222404260947813653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15357416148269507298542435 23036124222404260947813653)
                  ·
                    refine ⟨1079818322925199731928765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23036124222404260947813653 1079818322925199731928765)
                    ·
                      rfl

theorem cell22_3154408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_3154408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154408 prefixEnd_3154408 := by exact prefixLift 3154408
  have htrace : WordTrace (prefixWord ++ tailWord_3154408) baseStart_3154408 baseEnd_3154408 := by
    simpa [prefixWord, tailWord_3154408, baseEnd_3154408] using wordTrace_append hprefix tailTrace_3154408
  have hstable : (prefixWord ++ tailWord_3154408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154408).length < 2 ^ (prefixWord ++ tailWord_3154408).sum := by decide
  have hdescent : baseEnd_3154408 < baseStart_3154408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154489 : List Nat := [1, 2, 1, 5, 1, 1, 5, 2, 1, 3]
def baseStart_3154489 : Nat := 118140960795 + 3154489 * 2 ^ 59
def prefixEnd_3154489 : Nat := 4983230072969 + 3 ^ 40 * 3154489 * 2
def baseEnd_3154489 : Nat := 1079846050880542520653517

theorem tailTrace_3154489 : CollatzResearch.WordTrace tailWord_3154489 prefixEnd_3154489 1079846050880542520653517 := by
  unfold tailWord_3154489
  simp only [CollatzResearch.WordTrace]
  refine ⟨115053665868832571674722521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76702443912555047783148347 115053665868832571674722521)
  ·
    refine ⟨86290249401624428756041891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115053665868832571674722521 86290249401624428756041891)
    ·
      refine ⟨129435374102436643134062837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86290249401624428756041891 129435374102436643134062837)
      ·
        refine ⟨12134566322103435293818391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129435374102436643134062837 12134566322103435293818391)
        ·
          refine ⟨18201849483155152940727587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12134566322103435293818391 18201849483155152940727587)
          ·
            refine ⟨27302774224732729411091381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18201849483155152940727587 27302774224732729411091381)
            ·
              refine ⟨2559635083568693382289817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27302774224732729411091381 2559635083568693382289817)
              ·
                refine ⟨1919726312676520036717363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2559635083568693382289817 1919726312676520036717363)
                ·
                  refine ⟨2879589469014780055076045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919726312676520036717363 2879589469014780055076045)
                  ·
                    refine ⟨1079846050880542520653517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2879589469014780055076045 1079846050880542520653517)
                    ·
                      rfl

theorem cell22_3154489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 1, 3].length) (baseStart_3154489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154489 prefixEnd_3154489 := by exact prefixLift 3154489
  have htrace : WordTrace (prefixWord ++ tailWord_3154489) baseStart_3154489 baseEnd_3154489 := by
    simpa [prefixWord, tailWord_3154489, baseEnd_3154489] using wordTrace_append hprefix tailTrace_3154489
  have hstable : (prefixWord ++ tailWord_3154489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154489).length < 2 ^ (prefixWord ++ tailWord_3154489).sum := by decide
  have hdescent : baseEnd_3154489 < baseStart_3154489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154528 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 3, 5]
def baseStart_3154528 : Nat := 118140960795 + 3154528 * 2 ^ 59
def prefixEnd_3154528 : Nat := 4983230072969 + 3 ^ 40 * 3154528 * 2
def baseEnd_3154528 : Nat := 1079859401377559418928397

theorem tailTrace_3154528 : CollatzResearch.WordTrace tailWord_3154528 prefixEnd_3154528 1079859401377559418928397 := by
  unfold tailWord_3154528
  simp only [CollatzResearch.WordTrace]
  refine ⟨57527544157845640667696119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76703392210460854223594825 57527544157845640667696119)
  ·
    refine ⟨86291316236768461001544179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57527544157845640667696119 86291316236768461001544179)
    ·
      refine ⟨129436974355152691502316269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86291316236768461001544179 129436974355152691502316269)
      ·
        refine ⟨48538865383182259313368601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129436974355152691502316269 48538865383182259313368601)
        ·
          refine ⟨36404149037386694485026451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48538865383182259313368601 36404149037386694485026451)
          ·
            refine ⟨54606223556080041727539677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36404149037386694485026451 54606223556080041727539677)
            ·
              refine ⟨20477333833530015647827379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54606223556080041727539677 20477333833530015647827379)
              ·
                refine ⟨30716000750295023471741069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20477333833530015647827379 30716000750295023471741069)
                ·
                  refine ⟨11518500281360633801902901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30716000750295023471741069 11518500281360633801902901)
                  ·
                    refine ⟨1079859401377559418928397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11518500281360633801902901 1079859401377559418928397)
                    ·
                      rfl

theorem cell22_3154528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_3154528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154528 prefixEnd_3154528 := by exact prefixLift 3154528
  have htrace : WordTrace (prefixWord ++ tailWord_3154528) baseStart_3154528 baseEnd_3154528 := by
    simpa [prefixWord, tailWord_3154528, baseEnd_3154528] using wordTrace_append hprefix tailTrace_3154528
  have hstable : (prefixWord ++ tailWord_3154528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154528).length < 2 ^ (prefixWord ++ tailWord_3154528).sum := by decide
  have hdescent : baseEnd_3154528 < baseStart_3154528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154532 : List Nat := [2, 3, 1, 1, 2, 2, 5, 1, 1, 4]
def baseStart_3154532 : Nat := 118140960795 + 3154532 * 2 ^ 59
def prefixEnd_3154532 : Nat := 4983230072969 + 3 ^ 40 * 3154532 * 2
def baseEnd_3154532 : Nat := 1079860770659304741828385

theorem tailTrace_3154532 : CollatzResearch.WordTrace tailWord_3154532 prefixEnd_3154532 1079860770659304741828385 := by
  unfold tailWord_3154532
  simp only [CollatzResearch.WordTrace]
  refine ⟨57527617103838395009268925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76703489471784526679025233 57527617103838395009268925)
  ·
    refine ⟨21572856413939398128475847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57527617103838395009268925 21572856413939398128475847)
    ·
      refine ⟨32359284620909097192713771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21572856413939398128475847 32359284620909097192713771)
      ·
        refine ⟨48538926931363645789070657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32359284620909097192713771 48538926931363645789070657)
        ·
          refine ⟨36404195198522734341802993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48538926931363645789070657 36404195198522734341802993)
          ·
            refine ⟨27303146398892050756352245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36404195198522734341802993 27303146398892050756352245)
            ·
              refine ⟨2559669974896129758408023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27303146398892050756352245 2559669974896129758408023)
              ·
                refine ⟨3839504962344194637612035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2559669974896129758408023 3839504962344194637612035)
                ·
                  refine ⟨5759257443516291956418053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3839504962344194637612035 5759257443516291956418053)
                  ·
                    refine ⟨1079860770659304741828385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5759257443516291956418053 1079860770659304741828385)
                    ·
                      rfl

theorem cell22_3154532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_3154532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154532 prefixEnd_3154532 := by exact prefixLift 3154532
  have htrace : WordTrace (prefixWord ++ tailWord_3154532) baseStart_3154532 baseEnd_3154532 := by
    simpa [prefixWord, tailWord_3154532, baseEnd_3154532] using wordTrace_append hprefix tailTrace_3154532
  have hstable : (prefixWord ++ tailWord_3154532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154532).length < 2 ^ (prefixWord ++ tailWord_3154532).sum := by decide
  have hdescent : baseEnd_3154532 < baseStart_3154532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154607 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 3, 3]
def baseStart_3154607 : Nat := 118140960795 + 3154607 * 2 ^ 59
def prefixEnd_3154607 : Nat := 4983230072969 + 3 ^ 40 * 3154607 * 2
def baseEnd_3154607 : Nat := 1079886444692029546203155

theorem tailTrace_3154607 : CollatzResearch.WordTrace tailWord_3154607 prefixEnd_3154607 1079886444692029546203155 := by
  unfold tailWord_3154607
  simp only [CollatzResearch.WordTrace]
  refine ⟨115057969682405077827518075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76705313121603385218345383 115057969682405077827518075)
  ·
    refine ⟨172586954523607616741277113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115057969682405077827518075 172586954523607616741277113)
    ·
      refine ⟨129440215892705712555957835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172586954523607616741277113 129440215892705712555957835)
      ·
        refine ⟨194160323839058568833936753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129440215892705712555957835 194160323839058568833936753)
        ·
          refine ⟨145620242879293926625452565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194160323839058568833936753 145620242879293926625452565)
          ·
            refine ⟨6825948884966902810568089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145620242879293926625452565 6825948884966902810568089)
            ·
              refine ⟨5119461663725177107926067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6825948884966902810568089 5119461663725177107926067)
              ·
                refine ⟨7679192495587765661889101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5119461663725177107926067 7679192495587765661889101)
                ·
                  refine ⟨2879697185845412123208413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7679192495587765661889101 2879697185845412123208413)
                  ·
                    refine ⟨1079886444692029546203155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2879697185845412123208413 1079886444692029546203155)
                    ·
                      rfl

theorem cell22_3154607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 3].length) (baseStart_3154607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154607 prefixEnd_3154607 := by exact prefixLift 3154607
  have htrace : WordTrace (prefixWord ++ tailWord_3154607) baseStart_3154607 baseEnd_3154607 := by
    simpa [prefixWord, tailWord_3154607, baseEnd_3154607] using wordTrace_append hprefix tailTrace_3154607
  have hstable : (prefixWord ++ tailWord_3154607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154607).length < 2 ^ (prefixWord ++ tailWord_3154607).sum := by decide
  have hdescent : baseEnd_3154607 < baseStart_3154607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154633 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 4, 8]
def baseStart_3154633 : Nat := 118140960795 + 3154633 * 2 ^ 59
def prefixEnd_3154633 : Nat := 4983230072969 + 3 ^ 40 * 3154633 * 2
def baseEnd_3154633 : Nat := 1079895345023374145053075

theorem tailTrace_3154633 : CollatzResearch.WordTrace tailWord_3154633 prefixEnd_3154633 1079895345023374145053075 := by
  unfold tailWord_3154633
  simp only [CollatzResearch.WordTrace]
  refine ⟨115058917980310884267964553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76705945320207256178643035 115058917980310884267964553)
  ·
    refine ⟨86294188485233163200973415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115058917980310884267964553 86294188485233163200973415)
    ·
      refine ⟨129441282727849744801460123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86294188485233163200973415 129441282727849744801460123)
      ·
        refine ⟨194161924091774617202190185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129441282727849744801460123 194161924091774617202190185)
        ·
          refine ⟨145621443068830962901642639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194161924091774617202190185 145621443068830962901642639)
          ·
            refine ⟨218432164603246444352463959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145621443068830962901642639 218432164603246444352463959)
            ·
              refine ⟨327648246904869666528695939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218432164603246444352463959 327648246904869666528695939)
              ·
                refine ⟨491472370357304499793043909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327648246904869666528695939 491472370357304499793043909)
                ·
                  refine ⟨92151069441994593711195733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 491472370357304499793043909 92151069441994593711195733)
                  ·
                    refine ⟨1079895345023374145053075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92151069441994593711195733 1079895345023374145053075)
                    ·
                      rfl

theorem cell22_3154633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_3154633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154633 prefixEnd_3154633 := by exact prefixLift 3154633
  have htrace : WordTrace (prefixWord ++ tailWord_3154633) baseStart_3154633 baseEnd_3154633 := by
    simpa [prefixWord, tailWord_3154633, baseEnd_3154633] using wordTrace_append hprefix tailTrace_3154633
  have hstable : (prefixWord ++ tailWord_3154633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154633).length < 2 ^ (prefixWord ++ tailWord_3154633).sum := by decide
  have hdescent : baseEnd_3154633 < baseStart_3154633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154665 : List Nat := [1, 2, 1, 1, 1, 2, 7, 1, 6]
def baseStart_3154665 : Nat := 118140960795 + 3154665 * 2 ^ 59
def prefixEnd_3154665 : Nat := 4983230072969 + 3 ^ 40 * 3154665 * 2
def baseEnd_3154665 : Nat := 359968766425778909417659

theorem tailTrace_3154665 : CollatzResearch.WordTrace tailWord_3154665 prefixEnd_3154665 359968766425778909417659 := by
  unfold tailWord_3154665
  simp only [CollatzResearch.WordTrace]
  refine ⟨115060085116194953733129449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76706723410796635822086299 115060085116194953733129449)
  ·
    refine ⟨86295063837146215299847087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115060085116194953733129449 86295063837146215299847087)
    ·
      refine ⟨129442595755719322949770631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86295063837146215299847087 129442595755719322949770631)
      ·
        refine ⟨194163893633578984424655947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129442595755719322949770631 194163893633578984424655947)
        ·
          refine ⟨291245840450368476636983921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194163893633578984424655947 291245840450368476636983921)
          ·
            refine ⟨218434380337776357477737941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291245840450368476636983921 218434380337776357477737941)
            ·
              refine ⟨5119555789166633378384483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 218434380337776357477737941 5119555789166633378384483)
              ·
                refine ⟨7679333683749950067576725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5119555789166633378384483 7679333683749950067576725)
                ·
                  refine ⟨359968766425778909417659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7679333683749950067576725 359968766425778909417659)
                  ·
                    rfl

theorem cell22_3154665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 1, 6].length) (baseStart_3154665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154665 prefixEnd_3154665 := by exact prefixLift 3154665
  have htrace : WordTrace (prefixWord ++ tailWord_3154665) baseStart_3154665 baseEnd_3154665 := by
    simpa [prefixWord, tailWord_3154665, baseEnd_3154665] using wordTrace_append hprefix tailTrace_3154665
  have hstable : (prefixWord ++ tailWord_3154665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154665).length < 2 ^ (prefixWord ++ tailWord_3154665).sum := by decide
  have hdescent : baseEnd_3154665 < baseStart_3154665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154680 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 1, 5]
def baseStart_3154680 : Nat := 118140960795 + 3154680 * 2 ^ 59
def prefixEnd_3154680 : Nat := 4983230072969 + 3 ^ 40 * 3154680 * 2
def baseEnd_3154680 : Nat := 1079911434083881689127931

theorem tailTrace_3154680 : CollatzResearch.WordTrace tailWord_3154680 prefixEnd_3154680 1079911434083881689127931 := by
  unfold tailWord_3154680
  simp only [CollatzResearch.WordTrace]
  refine ⟨57530316105570305647462747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76707088140760407529950329 57530316105570305647462747)
  ·
    refine ⟨86295474158355458471194121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57530316105570305647462747 86295474158355458471194121)
    ·
      refine ⟨64721605618766593853395591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86295474158355458471194121 64721605618766593853395591)
      ·
        refine ⟨97082408428149890780093387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64721605618766593853395591 97082408428149890780093387)
        ·
          refine ⟨145623612642224836170140081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97082408428149890780093387 145623612642224836170140081)
          ·
            refine ⟨109217709481668627127605061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145623612642224836170140081 109217709481668627127605061)
            ·
              refine ⟨20478320527812867586425949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109217709481668627127605061 20478320527812867586425949)
              ·
                refine ⟨7679370197929825344909731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20478320527812867586425949 7679370197929825344909731)
                ·
                  refine ⟨11519055296894738017364597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7679370197929825344909731 11519055296894738017364597)
                  ·
                    refine ⟨1079911434083881689127931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11519055296894738017364597 1079911434083881689127931)
                    ·
                      rfl

theorem cell22_3154680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_3154680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154680 prefixEnd_3154680 := by exact prefixLift 3154680
  have htrace : WordTrace (prefixWord ++ tailWord_3154680) baseStart_3154680 baseEnd_3154680 := by
    simpa [prefixWord, tailWord_3154680, baseEnd_3154680] using wordTrace_append hprefix tailTrace_3154680
  have hstable : (prefixWord ++ tailWord_3154680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154680).length < 2 ^ (prefixWord ++ tailWord_3154680).sum := by decide
  have hdescent : baseEnd_3154680 < baseStart_3154680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154684 : List Nat := [2, 2, 2, 1, 3, 4, 1, 2, 1, 4]
def baseStart_3154684 : Nat := 118140960795 + 3154684 * 2 ^ 59
def prefixEnd_3154684 : Nat := 4983230072969 + 3 ^ 40 * 3154684 * 2
def baseEnd_3154684 : Nat := 1079912803365627012027919

theorem tailTrace_3154684 : CollatzResearch.WordTrace tailWord_3154684 prefixEnd_3154684 1079912803365627012027919 := by
  unfold tailWord_3154684
  simp only [CollatzResearch.WordTrace]
  refine ⟨57530389051563059989035553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76707185402084079985380737 57530389051563059989035553)
  ·
    refine ⟨43147791788672294991776665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57530389051563059989035553 43147791788672294991776665)
    ·
      refine ⟨32360843841504221243832499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43147791788672294991776665 32360843841504221243832499)
      ·
        refine ⟨48541265762256331865748749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32360843841504221243832499 48541265762256331865748749)
        ·
          refine ⟨18202974660846124449655781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48541265762256331865748749 18202974660846124449655781)
          ·
            refine ⟨3413057748908648334310459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18202974660846124449655781 3413057748908648334310459)
            ·
              refine ⟨5119586623362972501465689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3413057748908648334310459 5119586623362972501465689)
              ·
                refine ⟨3839689967522229376099267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5119586623362972501465689 3839689967522229376099267)
                ·
                  refine ⟨5759534951283344064148901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3839689967522229376099267 5759534951283344064148901)
                  ·
                    refine ⟨1079912803365627012027919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5759534951283344064148901 1079912803365627012027919)
                    ·
                      rfl

theorem cell22_3154684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_3154684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154684 prefixEnd_3154684 := by exact prefixLift 3154684
  have htrace : WordTrace (prefixWord ++ tailWord_3154684) baseStart_3154684 baseEnd_3154684 := by
    simpa [prefixWord, tailWord_3154684, baseEnd_3154684] using wordTrace_append hprefix tailTrace_3154684
  have hstable : (prefixWord ++ tailWord_3154684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154684).length < 2 ^ (prefixWord ++ tailWord_3154684).sum := by decide
  have hdescent : baseEnd_3154684 < baseStart_3154684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154714 : List Nat := [3, 1, 1, 3, 2, 1, 4, 2, 2, 3]
def baseStart_3154714 : Nat := 118140960795 + 3154714 * 2 ^ 59
def prefixEnd_3154714 : Nat := 4983230072969 + 3 ^ 40 * 3154714 * 2
def baseEnd_3154714 : Nat := 1079923072978716933777827

theorem tailTrace_3154714 : CollatzResearch.WordTrace tailWord_3154714 prefixEnd_3154714 1079923072978716933777827 := by
  unfold tailWord_3154714
  simp only [CollatzResearch.WordTrace]
  refine ⟨28765468073254358775415799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76707914862011623401108797 28765468073254358775415799)
  ·
    refine ⟨43148202109881538163123699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28765468073254358775415799 43148202109881538163123699)
    ·
      refine ⟨64722303164822307244685549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43148202109881538163123699 64722303164822307244685549)
      ·
        refine ⟨24270863686808365216757081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64722303164822307244685549 24270863686808365216757081)
        ·
          refine ⟨18203147765106273912567811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24270863686808365216757081 18203147765106273912567811)
          ·
            refine ⟨27304721647659410868851717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18203147765106273912567811 27304721647659410868851717)
            ·
              refine ⟨5119635308936139537909697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27304721647659410868851717 5119635308936139537909697)
              ·
                refine ⟨3839726481702104653432273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5119635308936139537909697 3839726481702104653432273)
                ·
                  refine ⟨2879794861276578490074205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3839726481702104653432273 2879794861276578490074205)
                  ·
                    refine ⟨1079923072978716933777827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2879794861276578490074205 1079923072978716933777827)
                    ·
                      rfl

theorem cell22_3154714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_3154714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154714 prefixEnd_3154714 := by exact prefixLift 3154714
  have htrace : WordTrace (prefixWord ++ tailWord_3154714) baseStart_3154714 baseEnd_3154714 := by
    simpa [prefixWord, tailWord_3154714, baseEnd_3154714] using wordTrace_append hprefix tailTrace_3154714
  have hstable : (prefixWord ++ tailWord_3154714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154714).length < 2 ^ (prefixWord ++ tailWord_3154714).sum := by decide
  have hdescent : baseEnd_3154714 < baseStart_3154714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154716 : List Nat := [2, 2, 3, 1, 1, 5, 2, 2, 4]
def baseStart_3154716 : Nat := 118140960795 + 3154716 * 2 ^ 59
def prefixEnd_3154716 : Nat := 4983230072969 + 3 ^ 40 * 3154716 * 2
def baseEnd_3154716 : Nat := 359974585873196531742607

theorem tailTrace_3154716 : CollatzResearch.WordTrace tailWord_3154716 prefixEnd_3154716 359974585873196531742607 := by
  unfold tailWord_3154716
  simp only [CollatzResearch.WordTrace]
  refine ⟨57530972619505094721618001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76707963492673459628824001 57530972619505094721618001)
  ·
    refine ⟨43148229464628821041213501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57530972619505094721618001 43148229464628821041213501)
    ·
      refine ⟨16180586049235807890455063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43148229464628821041213501 16180586049235807890455063)
      ·
        refine ⟨24270879073853711835682595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16180586049235807890455063 24270879073853711835682595)
        ·
          refine ⟨36406318610780567753523893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24270879073853711835682595 36406318610780567753523893)
          ·
            refine ⟨3413092369760678226892865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36406318610780567753523893 3413092369760678226892865)
            ·
              refine ⟨2559819277320508670169649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3413092369760678226892865 2559819277320508670169649)
              ·
                refine ⟨1919864457990381502627237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2559819277320508670169649 1919864457990381502627237)
                ·
                  refine ⟨359974585873196531742607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1919864457990381502627237 359974585873196531742607)
                  ·
                    rfl

theorem cell22_3154716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_3154716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154716 prefixEnd_3154716 := by exact prefixLift 3154716
  have htrace : WordTrace (prefixWord ++ tailWord_3154716) baseStart_3154716 baseEnd_3154716 := by
    simpa [prefixWord, tailWord_3154716, baseEnd_3154716] using wordTrace_append hprefix tailTrace_3154716
  have hstable : (prefixWord ++ tailWord_3154716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154716).length < 2 ^ (prefixWord ++ tailWord_3154716).sum := by decide
  have hdescent : baseEnd_3154716 < baseStart_3154716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154746 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 2, 4]
def baseStart_3154746 : Nat := 118140960795 + 3154746 * 2 ^ 59
def prefixEnd_3154746 : Nat := 4983230072969 + 3 ^ 40 * 3154746 * 2
def baseEnd_3154746 : Nat := 1079934027232679516977729

theorem tailTrace_3154746 : CollatzResearch.WordTrace tailWord_3154746 prefixEnd_3154746 1079934027232679516977729 := by
  unfold tailWord_3154746
  simp only [CollatzResearch.WordTrace]
  refine ⟨28765759857225376141707023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76708692952601003044552061 28765759857225376141707023)
  ·
    refine ⟨43148639785838064212560535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28765759857225376141707023 43148639785838064212560535)
    ·
      refine ⟨64722959678757096318840803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43148639785838064212560535 64722959678757096318840803)
      ·
        refine ⟨97084439518135644478261205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64722959678757096318840803 97084439518135644478261205)
        ·
          refine ⟨2275416551206304167459247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 97084439518135644478261205 2275416551206304167459247)
          ·
            refine ⟨3413124826809456251188871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275416551206304167459247 3413124826809456251188871)
            ·
              refine ⟨5119687240214184376783307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3413124826809456251188871 5119687240214184376783307)
              ·
                refine ⟨7679530860321276565174961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5119687240214184376783307 7679530860321276565174961)
                ·
                  refine ⟨5759648145240957423881221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7679530860321276565174961 5759648145240957423881221)
                  ·
                    refine ⟨1079934027232679516977729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5759648145240957423881221 1079934027232679516977729)
                    ·
                      rfl

theorem cell22_3154746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_3154746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154746 prefixEnd_3154746 := by exact prefixLift 3154746
  have htrace : WordTrace (prefixWord ++ tailWord_3154746) baseStart_3154746 baseEnd_3154746 := by
    simpa [prefixWord, tailWord_3154746, baseEnd_3154746] using wordTrace_append hprefix tailTrace_3154746
  have hstable : (prefixWord ++ tailWord_3154746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154746).length < 2 ^ (prefixWord ++ tailWord_3154746).sum := by decide
  have hdescent : baseEnd_3154746 < baseStart_3154746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154755 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 7]
def baseStart_3154755 : Nat := 118140960795 + 3154755 * 2 ^ 59
def prefixEnd_3154755 : Nat := 4983230072969 + 3 ^ 40 * 3154755 * 2
def baseEnd_3154755 : Nat := 359979036038868831167567

theorem tailTrace_3154755 : CollatzResearch.WordTrace tailWord_3154755 prefixEnd_3154755 359979036038868831167567 := by
  unfold tailWord_3154755
  simp only [CollatzResearch.WordTrace]
  refine ⟨115063367685868899103905719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76708911790579266069270479 115063367685868899103905719)
  ·
    refine ⟨172595051528803348655858579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115063367685868899103905719 172595051528803348655858579)
    ·
      refine ⟨258892577293205022983787869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172595051528803348655858579 258892577293205022983787869)
      ·
        refine ⟨97084716484951883618920451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258892577293205022983787869 97084716484951883618920451)
        ·
          refine ⟨145627074727427825428380677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97084716484951883618920451 145627074727427825428380677)
          ·
            refine ⟨27305076511392717267821377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145627074727427825428380677 27305076511392717267821377)
            ·
              refine ⟨20478807383544537950866033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27305076511392717267821377 20478807383544537950866033)
              ·
                refine ⟨15359105537658403463149525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20478807383544537950866033 15359105537658403463149525)
                ·
                  refine ⟨359979036038868831167567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15359105537658403463149525 359979036038868831167567)
                  ·
                    rfl

theorem cell22_3154755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 7].length) (baseStart_3154755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154755 prefixEnd_3154755 := by exact prefixLift 3154755
  have htrace : WordTrace (prefixWord ++ tailWord_3154755) baseStart_3154755 baseEnd_3154755 := by
    simpa [prefixWord, tailWord_3154755, baseEnd_3154755] using wordTrace_append hprefix tailTrace_3154755
  have hstable : (prefixWord ++ tailWord_3154755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154755).length < 2 ^ (prefixWord ++ tailWord_3154755).sum := by decide
  have hdescent : baseEnd_3154755 < baseStart_3154755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154765 : List Nat := [1, 6, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_3154765 : Nat := 118140960795 + 3154765 * 2 ^ 59
def prefixEnd_3154765 : Nat := 4983230072969 + 3 ^ 40 * 3154765 * 2
def baseEnd_3154765 : Nat := 1079940531320969800752671

theorem tailTrace_3154765 : CollatzResearch.WordTrace tailWord_3154765 prefixEnd_3154765 1079940531320969800752671 := by
  unfold tailWord_3154765
  simp only [CollatzResearch.WordTrace]
  refine ⟨115063732415832670811769749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76709154943888447207846499 115063732415832670811769749)
  ·
    refine ⟨5393612456992156444301707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115063732415832670811769749 5393612456992156444301707)
    ·
      refine ⟨8090418685488234666452561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5393612456992156444301707 8090418685488234666452561)
      ·
        refine ⟨6067814014116175999839421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8090418685488234666452561 6067814014116175999839421)
        ·
          refine ⟨2275430255293565999939783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6067814014116175999839421 2275430255293565999939783)
          ·
            refine ⟨3413145382940348999909675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275430255293565999939783 3413145382940348999909675)
            ·
              refine ⟨5119718074410523499864513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3413145382940348999909675 5119718074410523499864513)
              ·
                refine ⟨3839788555807892624898385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5119718074410523499864513 3839788555807892624898385)
                ·
                  refine ⟨2879841416855919468673789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3839788555807892624898385 2879841416855919468673789)
                  ·
                    refine ⟨1079940531320969800752671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2879841416855919468673789 1079940531320969800752671)
                    ·
                      rfl

theorem cell22_3154765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_3154765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154765 prefixEnd_3154765 := by exact prefixLift 3154765
  have htrace : WordTrace (prefixWord ++ tailWord_3154765) baseStart_3154765 baseEnd_3154765 := by
    simpa [prefixWord, tailWord_3154765, baseEnd_3154765] using wordTrace_append hprefix tailTrace_3154765
  have hstable : (prefixWord ++ tailWord_3154765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154765).length < 2 ^ (prefixWord ++ tailWord_3154765).sum := by decide
  have hdescent : baseEnd_3154765 < baseStart_3154765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154785 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3154785 : Nat := 118140960795 + 3154785 * 2 ^ 59
def prefixEnd_3154785 : Nat := 4983230072969 + 3 ^ 40 * 3154785 * 2
def baseEnd_3154785 : Nat := 1079947377729696415252609

theorem tailTrace_3154785 : CollatzResearch.WordTrace tailWord_3154785 prefixEnd_3154785 1079947377729696415252609 := by
  unfold tailWord_3154785
  simp only [CollatzResearch.WordTrace]
  refine ⟨115064461875760214227497809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76709641250506809484998539 115064461875760214227497809)
  ·
    refine ⟨86298346406820160670623357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115064461875760214227497809 86298346406820160670623357)
    ·
      refine ⟨32361879902557560251483759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86298346406820160670623357 32361879902557560251483759)
      ·
        refine ⟨48542819853836340377225639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32361879902557560251483759 48542819853836340377225639)
        ·
          refine ⟨72814229780754510565838459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48542819853836340377225639 72814229780754510565838459)
          ·
            refine ⟨109221344671131765848757689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72814229780754510565838459 109221344671131765848757689)
            ·
              refine ⟨81916008503348824386568267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109221344671131765848757689 81916008503348824386568267)
              ·
                refine ⟨122874012755023236579852401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81916008503348824386568267 122874012755023236579852401)
                ·
                  refine ⟨92155509566267427434889301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122874012755023236579852401 92155509566267427434889301)
                  ·
                    refine ⟨1079947377729696415252609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92155509566267427434889301 1079947377729696415252609)
                    ·
                      rfl

theorem cell22_3154785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3154785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154785 prefixEnd_3154785 := by exact prefixLift 3154785
  have htrace : WordTrace (prefixWord ++ tailWord_3154785) baseStart_3154785 baseEnd_3154785 := by
    simpa [prefixWord, tailWord_3154785, baseEnd_3154785] using wordTrace_append hprefix tailTrace_3154785
  have hstable : (prefixWord ++ tailWord_3154785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154785).length < 2 ^ (prefixWord ++ tailWord_3154785).sum := by decide
  have hdescent : baseEnd_3154785 < baseStart_3154785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154787 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 2, 5]
def baseStart_3154787 : Nat := 118140960795 + 3154787 * 2 ^ 59
def prefixEnd_3154787 : Nat := 4983230072969 + 3 ^ 40 * 3154787 * 2
def baseEnd_3154787 : Nat := 1079948062370569076702603

theorem tailTrace_3154787 : CollatzResearch.WordTrace tailWord_3154787 prefixEnd_3154787 1079948062370569076702603 := by
  unfold tailWord_3154787
  simp only [CollatzResearch.WordTrace]
  refine ⟨115064534821752968569070615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76709689881168645712713743 115064534821752968569070615)
  ·
    refine ⟨172596802232629452853605923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115064534821752968569070615 172596802232629452853605923)
    ·
      refine ⟨258895203348944179280408885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172596802232629452853605923 258895203348944179280408885)
      ·
        refine ⟨24271425313963516807538333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 258895203348944179280408885 24271425313963516807538333)
        ·
          refine ⟨9101784492736318802826875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24271425313963516807538333 9101784492736318802826875)
          ·
            refine ⟨13652676739104478204240313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9101784492736318802826875 13652676739104478204240313)
            ·
              refine ⟨10239507554328358653180235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13652676739104478204240313 10239507554328358653180235)
              ·
                refine ⟨15359261331492537979770353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10239507554328358653180235 15359261331492537979770353)
                ·
                  refine ⟨11519445998619403484827765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15359261331492537979770353 11519445998619403484827765)
                  ·
                    refine ⟨1079948062370569076702603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11519445998619403484827765 1079948062370569076702603)
                    ·
                      rfl

theorem cell22_3154787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 5].length) (baseStart_3154787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154787 prefixEnd_3154787 := by exact prefixLift 3154787
  have htrace : WordTrace (prefixWord ++ tailWord_3154787) baseStart_3154787 baseEnd_3154787 := by
    simpa [prefixWord, tailWord_3154787, baseEnd_3154787] using wordTrace_append hprefix tailTrace_3154787
  have hstable : (prefixWord ++ tailWord_3154787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154787).length < 2 ^ (prefixWord ++ tailWord_3154787).sum := by decide
  have hdescent : baseEnd_3154787 < baseStart_3154787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154802 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_3154802 : Nat := 118140960795 + 3154802 * 2 ^ 59
def prefixEnd_3154802 : Nat := 4983230072969 + 3 ^ 40 * 3154802 * 2
def baseEnd_3154802 : Nat := 1079953197177114037577557

theorem tailTrace_3154802 : CollatzResearch.WordTrace tailWord_3154802 prefixEnd_3154802 1079953197177114037577557 := by
  unfold tailWord_3154802
  simp only [CollatzResearch.WordTrace]
  refine ⟨28766270479174656532716665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76710054611132417420577773 28766270479174656532716665)
  ·
    refine ⟨21574702859380992399537499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28766270479174656532716665 21574702859380992399537499)
    ·
      refine ⟨32362054289071488599306249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21574702859380992399537499 32362054289071488599306249)
      ·
        refine ⟨24271540716803616449479687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32362054289071488599306249 24271540716803616449479687)
        ·
          refine ⟨36407311075205424674219531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24271540716803616449479687 36407311075205424674219531)
          ·
            refine ⟨54610966612808137011329297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36407311075205424674219531 54610966612808137011329297)
            ·
              refine ⟨40958224959606102758496973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54610966612808137011329297 40958224959606102758496973)
              ·
                refine ⟨15359334359852288534436365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40958224959606102758496973 15359334359852288534436365)
                ·
                  refine ⟨5759750384944608200413637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15359334359852288534436365 5759750384944608200413637)
                  ·
                    refine ⟨1079953197177114037577557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5759750384944608200413637 1079953197177114037577557)
                    ·
                      rfl

theorem cell22_3154802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_3154802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154802 prefixEnd_3154802 := by exact prefixLift 3154802
  have htrace : WordTrace (prefixWord ++ tailWord_3154802) baseStart_3154802 baseEnd_3154802 := by
    simpa [prefixWord, tailWord_3154802, baseEnd_3154802] using wordTrace_append hprefix tailTrace_3154802
  have hstable : (prefixWord ++ tailWord_3154802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154802).length < 2 ^ (prefixWord ++ tailWord_3154802).sum := by decide
  have hdescent : baseEnd_3154802 < baseStart_3154802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154832 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 8, 3]
def baseStart_3154832 : Nat := 118140960795 + 3154832 * 2 ^ 59
def prefixEnd_3154832 : Nat := 4983230072969 + 3 ^ 40 * 3154832 * 2
def baseEnd_3154832 : Nat := 1079963466790203959327465

theorem tailTrace_3154832 : CollatzResearch.WordTrace tailWord_3154832 prefixEnd_3154832 1079963466790203959327465 := by
  unfold tailWord_3154832
  simp only [CollatzResearch.WordTrace]
  refine ⟨57533088053294970627229375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76710784071059960836305833 57533088053294970627229375)
  ·
    refine ⟨86299632079942455940844063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57533088053294970627229375 86299632079942455940844063)
    ·
      refine ⟨129449448119913683911266095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86299632079942455940844063 129449448119913683911266095)
      ·
        refine ⟨194174172179870525866899143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129449448119913683911266095 194174172179870525866899143)
        ·
          refine ⟨291261258269805788800348715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194174172179870525866899143 291261258269805788800348715)
          ·
            refine ⟨436891887404708683200523073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291261258269805788800348715 436891887404708683200523073)
            ·
              refine ⟨327668915553531512400392305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436891887404708683200523073 327668915553531512400392305)
              ·
                refine ⟨245751686665148634300294229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327668915553531512400392305 245751686665148634300294229)
                ·
                  refine ⟨2879902578107210558206573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 245751686665148634300294229 2879902578107210558206573)
                  ·
                    refine ⟨1079963466790203959327465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2879902578107210558206573 1079963466790203959327465)
                    ·
                      rfl

theorem cell22_3154832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 8, 3].length) (baseStart_3154832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154832 prefixEnd_3154832 := by exact prefixLift 3154832
  have htrace : WordTrace (prefixWord ++ tailWord_3154832) baseStart_3154832 baseEnd_3154832 := by
    simpa [prefixWord, tailWord_3154832, baseEnd_3154832] using wordTrace_append hprefix tailTrace_3154832
  have hstable : (prefixWord ++ tailWord_3154832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154832).length < 2 ^ (prefixWord ++ tailWord_3154832).sum := by decide
  have hdescent : baseEnd_3154832 < baseStart_3154832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154892 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_3154892 : Nat := 118140960795 + 3154892 * 2 ^ 59
def prefixEnd_3154892 : Nat := 4983230072969 + 3 ^ 40 * 3154892 * 2
def baseEnd_3154892 : Nat := 1079984006016383802827281

theorem tailTrace_3154892 : CollatzResearch.WordTrace tailWord_3154892 prefixEnd_3154892 1079984006016383802827281 := by
  unfold tailWord_3154892
  simp only [CollatzResearch.WordTrace]
  refine ⟨57534182243186285750821465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76712242990915047667761953 57534182243186285750821465)
  ·
    refine ⟨43150636682389714313116099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57534182243186285750821465 43150636682389714313116099)
    ·
      refine ⟨64725955023584571469674149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43150636682389714313116099 64725955023584571469674149)
      ·
        refine ⟨12136116566922107150563903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64725955023584571469674149 12136116566922107150563903)
        ·
          refine ⟨18204174850383160725845855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12136116566922107150563903 18204174850383160725845855)
          ·
            refine ⟨27306262275574741088768783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18204174850383160725845855 27306262275574741088768783)
            ·
              refine ⟨40959393413362111633153175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27306262275574741088768783 40959393413362111633153175)
              ·
                refine ⟨61439090120043167449729763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40959393413362111633153175 61439090120043167449729763)
                ·
                  refine ⟨92158635180064751174594645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61439090120043167449729763 92158635180064751174594645)
                  ·
                    refine ⟨1079984006016383802827281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92158635180064751174594645 1079984006016383802827281)
                    ·
                      rfl

theorem cell22_3154892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_3154892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154892 prefixEnd_3154892 := by exact prefixLift 3154892
  have htrace : WordTrace (prefixWord ++ tailWord_3154892) baseStart_3154892 baseEnd_3154892 := by
    simpa [prefixWord, tailWord_3154892, baseEnd_3154892] using wordTrace_append hprefix tailTrace_3154892
  have hstable : (prefixWord ++ tailWord_3154892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154892).length < 2 ^ (prefixWord ++ tailWord_3154892).sum := by decide
  have hdescent : baseEnd_3154892 < baseStart_3154892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3154911 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 3, 3]
def baseStart_3154911 : Nat := 118140960795 + 3154911 * 2 ^ 59
def prefixEnd_3154911 : Nat := 4983230072969 + 3 ^ 40 * 3154911 * 2
def baseEnd_3154911 : Nat := 1079990510104674086602223

theorem tailTrace_3154911 : CollatzResearch.WordTrace tailWord_3154911 prefixEnd_3154911 1079990510104674086602223 := by
  unfold tailWord_3154911
  simp only [CollatzResearch.WordTrace]
  refine ⟨115069057473303737746584587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76712704982202491831056391 115069057473303737746584587)
  ·
    refine ⟨172603586209955606619876881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115069057473303737746584587 172603586209955606619876881)
    ·
      refine ⟨129452689657466704964907661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172603586209955606619876881 129452689657466704964907661)
      ·
        refine ⟨48544758621550014361840373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129452689657466704964907661 48544758621550014361840373)
        ·
          refine ⟨4551071120770313846422535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48544758621550014361840373 4551071120770313846422535)
          ·
            refine ⟨6826606681155470769633803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4551071120770313846422535 6826606681155470769633803)
            ·
              refine ⟨10239910021733206154450705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6826606681155470769633803 10239910021733206154450705)
              ·
                refine ⟨7679932516299904615838029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10239910021733206154450705 7679932516299904615838029)
                ·
                  refine ⟨2879974693612464230939261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7679932516299904615838029 2879974693612464230939261)
                  ·
                    refine ⟨1079990510104674086602223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2879974693612464230939261 1079990510104674086602223)
                    ·
                      rfl

theorem cell22_3154911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 3].length) (baseStart_3154911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3154911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3154911 prefixEnd_3154911 := by exact prefixLift 3154911
  have htrace : WordTrace (prefixWord ++ tailWord_3154911) baseStart_3154911 baseEnd_3154911 := by
    simpa [prefixWord, tailWord_3154911, baseEnd_3154911] using wordTrace_append hprefix tailTrace_3154911
  have hstable : (prefixWord ++ tailWord_3154911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3154911).length < 2 ^ (prefixWord ++ tailWord_3154911).sum := by decide
  have hdescent : baseEnd_3154911 < baseStart_3154911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3154911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155001 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 4, 3]
def baseStart_3155001 : Nat := 118140960795 + 3155001 * 2 ^ 59
def prefixEnd_3155001 : Nat := 4983230072969 + 3 ^ 40 * 3155001 * 2
def baseEnd_3155001 : Nat := 1080021318943943851851947

theorem tailTrace_3155001 : CollatzResearch.WordTrace tailWord_3155001 prefixEnd_3155001 1080021318943943851851947 := by
  unfold tailWord_3155001
  simp only [CollatzResearch.WordTrace]
  refine ⟨115072340042977683117360857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76714893361985122078240571 115072340042977683117360857)
  ·
    refine ⟨86304255032233262338020643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115072340042977683117360857 86304255032233262338020643)
    ·
      refine ⟨129456382548349893507030965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86304255032233262338020643 129456382548349893507030965)
      ·
        refine ⟨12136535863907802516284153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129456382548349893507030965 12136535863907802516284153)
        ·
          refine ⟨9102401897930851887213115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12136535863907802516284153 9102401897930851887213115)
          ·
            refine ⟨13653602846896277830819673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9102401897930851887213115 13653602846896277830819673)
            ·
              refine ⟨10240202135172208373114755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13653602846896277830819673 10240202135172208373114755)
              ·
                refine ⟨15360303202758312559672133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10240202135172208373114755 15360303202758312559672133)
                ·
                  refine ⟨2880056850517183604938525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15360303202758312559672133 2880056850517183604938525)
                  ·
                    refine ⟨1080021318943943851851947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2880056850517183604938525 1080021318943943851851947)
                    ·
                      rfl

theorem cell22_3155001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 3].length) (baseStart_3155001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155001 prefixEnd_3155001 := by exact prefixLift 3155001
  have htrace : WordTrace (prefixWord ++ tailWord_3155001) baseStart_3155001 baseEnd_3155001 := by
    simpa [prefixWord, tailWord_3155001, baseEnd_3155001] using wordTrace_append hprefix tailTrace_3155001
  have hstable : (prefixWord ++ tailWord_3155001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155001).length < 2 ^ (prefixWord ++ tailWord_3155001).sum := by decide
  have hdescent : baseEnd_3155001 < baseStart_3155001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155018 : List Nat := [3, 1, 2, 1, 1, 2, 6, 1, 2, 3]
def baseStart_3155018 : Nat := 118140960795 + 3155018 * 2 ^ 59
def prefixEnd_3155018 : Nat := 4983230072969 + 3 ^ 40 * 3155018 * 2
def baseEnd_3155018 : Nat := 1080027138391361474176895

theorem tailTrace_3155018 : CollatzResearch.WordTrace tailWord_3155018 prefixEnd_3155018 1080027138391361474176895 := by
  unfold tailWord_3155018
  simp only [CollatzResearch.WordTrace]
  refine ⟨28768240020979023755182427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76715306722610730013819805 28768240020979023755182427)
  ·
    refine ⟨43152360031468535632773641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28768240020979023755182427 43152360031468535632773641)
    ·
      refine ⟨32364270023601401724580231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43152360031468535632773641 32364270023601401724580231)
      ·
        refine ⟨48546405035402102586870347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32364270023601401724580231 48546405035402102586870347)
        ·
          refine ⟨72819607553103153880305521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48546405035402102586870347 72819607553103153880305521)
          ·
            refine ⟨54614705664827365410229141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72819607553103153880305521 54614705664827365410229141)
            ·
              refine ⟨2560064328038782753604491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54614705664827365410229141 2560064328038782753604491)
              ·
                refine ⟨3840096492058174130406737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2560064328038782753604491 3840096492058174130406737)
                ·
                  refine ⟨2880072369043630597805053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3840096492058174130406737 2880072369043630597805053)
                  ·
                    refine ⟨1080027138391361474176895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2880072369043630597805053 1080027138391361474176895)
                    ·
                      rfl

theorem cell22_3155018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_3155018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155018 prefixEnd_3155018 := by exact prefixLift 3155018
  have htrace : WordTrace (prefixWord ++ tailWord_3155018) baseStart_3155018 baseEnd_3155018 := by
    simpa [prefixWord, tailWord_3155018, baseEnd_3155018] using wordTrace_append hprefix tailTrace_3155018
  have hstable : (prefixWord ++ tailWord_3155018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155018).length < 2 ^ (prefixWord ++ tailWord_3155018).sum := by decide
  have hdescent : baseEnd_3155018 < baseStart_3155018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155063 : List Nat := [1, 1, 3, 1, 1, 4, 3, 4, 1, 3]
def baseStart_3155063 : Nat := 118140960795 + 3155063 * 2 ^ 59
def prefixEnd_3155063 : Nat := 4983230072969 + 3 ^ 40 * 3155063 * 2
def baseEnd_3155063 : Nat := 1080042542810996356801757

theorem tailTrace_3155063 : CollatzResearch.WordTrace tailWord_3155063 prefixEnd_3155063 1080042542810996356801757 := by
  unfold tailWord_3155063
  simp only [CollatzResearch.WordTrace]
  refine ⟨115074601368753067706117843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76716400912502045137411895 115074601368753067706117843)
  ·
    refine ⟨172611902053129601559176765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115074601368753067706117843 172611902053129601559176765)
    ·
      refine ⟨64729463269923600584691287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172611902053129601559176765 64729463269923600584691287)
      ·
        refine ⟨97094194904885400877036931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64729463269923600584691287 97094194904885400877036931)
        ·
          refine ⟨145641292357328101315555397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97094194904885400877036931 145641292357328101315555397)
          ·
            refine ⟨27307742316999018996666637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145641292357328101315555397 27307742316999018996666637)
            ·
              refine ⟨10240403368874632123749989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27307742316999018996666637 10240403368874632123749989)
              ·
                refine ⟨1920075631663993523203123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10240403368874632123749989 1920075631663993523203123)
                ·
                  refine ⟨2880113447495990284804685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920075631663993523203123 2880113447495990284804685)
                  ·
                    refine ⟨1080042542810996356801757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2880113447495990284804685 1080042542810996356801757)
                    ·
                      rfl

theorem cell22_3155063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_3155063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155063 prefixEnd_3155063 := by exact prefixLift 3155063
  have htrace : WordTrace (prefixWord ++ tailWord_3155063) baseStart_3155063 baseEnd_3155063 := by
    simpa [prefixWord, tailWord_3155063, baseEnd_3155063] using wordTrace_append hprefix tailTrace_3155063
  have hstable : (prefixWord ++ tailWord_3155063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155063).length < 2 ^ (prefixWord ++ tailWord_3155063).sum := by decide
  have hdescent : baseEnd_3155063 < baseStart_3155063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155076 : List Nat := [2, 3, 2, 1, 2, 2, 2, 3, 5]
def baseStart_3155076 : Nat := 118140960795 + 3155076 * 2 ^ 59
def prefixEnd_3155076 : Nat := 4983230072969 + 3 ^ 40 * 3155076 * 2
def baseEnd_3155076 : Nat := 360015664325556218742239

theorem tailTrace_3155076 : CollatzResearch.WordTrace tailWord_3155076 prefixEnd_3155076 360015664325556218742239 := by
  unfold tailWord_3155076
  simp only [CollatzResearch.WordTrace]
  refine ⟨57537537758852985463170541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76716717011803980617560721 57537537758852985463170541)
  ·
    refine ⟨21576576659569869548688953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57537537758852985463170541 21576576659569869548688953)
    ·
      refine ⟨16182432494677402161516715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21576576659569869548688953 16182432494677402161516715)
      ·
        refine ⟨24273648742016103242275073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16182432494677402161516715 24273648742016103242275073)
        ·
          refine ⟨18205236556512077431706305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24273648742016103242275073 18205236556512077431706305)
          ·
            refine ⟨13653927417384058073779729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18205236556512077431706305 13653927417384058073779729)
            ·
              refine ⟨10240445563038043555334797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13653927417384058073779729 10240445563038043555334797)
              ·
                refine ⟨3840167086139266333250549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10240445563038043555334797 3840167086139266333250549)
                ·
                  refine ⟨360015664325556218742239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3840167086139266333250549 360015664325556218742239)
                  ·
                    rfl

theorem cell22_3155076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_3155076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155076 prefixEnd_3155076 := by exact prefixLift 3155076
  have htrace : WordTrace (prefixWord ++ tailWord_3155076) baseStart_3155076 baseEnd_3155076 := by
    simpa [prefixWord, tailWord_3155076, baseEnd_3155076] using wordTrace_append hprefix tailTrace_3155076
  have hstable : (prefixWord ++ tailWord_3155076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155076).length < 2 ^ (prefixWord ++ tailWord_3155076).sum := by decide
  have hdescent : baseEnd_3155076 < baseStart_3155076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155104 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 8]
def baseStart_3155104 : Nat := 118140960795 + 3155104 * 2 ^ 59
def prefixEnd_3155104 : Nat := 4983230072969 + 3 ^ 40 * 3155104 * 2
def baseEnd_3155104 : Nat := 360018859316295305508877

theorem tailTrace_3155104 : CollatzResearch.WordTrace tailWord_3155104 prefixEnd_3155104 360018859316295305508877 := by
  unfold tailWord_3155104
  simp only [CollatzResearch.WordTrace]
  refine ⟨57538048380802265854180183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76717397841069687805573577 57538048380802265854180183)
  ·
    refine ⟨86307072571203398781270275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57538048380802265854180183 86307072571203398781270275)
    ·
      refine ⟨129460608856805098171905413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86307072571203398781270275 129460608856805098171905413)
      ·
        refine ⟨24273864160650955907232265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129460608856805098171905413 24273864160650955907232265)
        ·
          refine ⟨18205398120488216930424199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24273864160650955907232265 18205398120488216930424199)
          ·
            refine ⟨27308097180732325395636299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18205398120488216930424199 27308097180732325395636299)
            ·
              refine ⟨40962145771098488093454449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27308097180732325395636299 40962145771098488093454449)
              ·
                refine ⟨30721609328323866070090837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40962145771098488093454449 30721609328323866070090837)
                ·
                  refine ⟨360018859316295305508877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30721609328323866070090837 360018859316295305508877)
                  ·
                    rfl

theorem cell22_3155104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_3155104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155104 prefixEnd_3155104 := by exact prefixLift 3155104
  have htrace : WordTrace (prefixWord ++ tailWord_3155104) baseStart_3155104 baseEnd_3155104 := by
    simpa [prefixWord, tailWord_3155104, baseEnd_3155104] using wordTrace_append hprefix tailTrace_3155104
  have hstable : (prefixWord ++ tailWord_3155104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155104).length < 2 ^ (prefixWord ++ tailWord_3155104).sum := by decide
  have hdescent : baseEnd_3155104 < baseStart_3155104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155119 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 3, 5]
def baseStart_3155119 : Nat := 118140960795 + 3155119 * 2 ^ 59
def prefixEnd_3155119 : Nat := 4983230072969 + 3 ^ 40 * 3155119 * 2
def baseEnd_3155119 : Nat := 1080061712755430877401585

theorem tailTrace_3155119 : CollatzResearch.WordTrace tailWord_3155119 prefixEnd_3155119 1080061712755430877401585 := by
  unfold tailWord_3155119
  simp only [CollatzResearch.WordTrace]
  refine ⟨115076643856550189270156411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76717762571033459513437607 115076643856550189270156411)
  ·
    refine ⟨172614965784825283905234617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115076643856550189270156411 172614965784825283905234617)
    ·
      refine ⟨129461224338618962928925963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172614965784825283905234617 129461224338618962928925963)
      ·
        refine ⟨194191836507928444393388945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129461224338618962928925963 194191836507928444393388945)
        ·
          refine ⟨145643877380946333295041709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194191836507928444393388945 145643877380946333295041709)
          ·
            refine ⟨54616454017854874985640641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145643877380946333295041709 54616454017854874985640641)
            ·
              refine ⟨40962340513391156239230481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54616454017854874985640641 40962340513391156239230481)
              ·
                refine ⟨30721755385043367179422861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40962340513391156239230481 30721755385043367179422861)
                ·
                  refine ⟨11520658269391262692283573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30721755385043367179422861 11520658269391262692283573)
                  ·
                    refine ⟨1080061712755430877401585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11520658269391262692283573 1080061712755430877401585)
                    ·
                      rfl

theorem cell22_3155119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_3155119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155119 prefixEnd_3155119 := by exact prefixLift 3155119
  have htrace : WordTrace (prefixWord ++ tailWord_3155119) baseStart_3155119 baseEnd_3155119 := by
    simpa [prefixWord, tailWord_3155119, baseEnd_3155119] using wordTrace_append hprefix tailTrace_3155119
  have hstable : (prefixWord ++ tailWord_3155119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155119).length < 2 ^ (prefixWord ++ tailWord_3155119).sum := by decide
  have hdescent : baseEnd_3155119 < baseStart_3155119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155121 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 6]
def baseStart_3155121 : Nat := 118140960795 + 3155121 * 2 ^ 59
def prefixEnd_3155121 : Nat := 4983230072969 + 3 ^ 40 * 3155121 * 2
def baseEnd_3155121 : Nat := 360020799132101179617193

theorem tailTrace_3155121 : CollatzResearch.WordTrace tailWord_3155121 prefixEnd_3155121 360020799132101179617193 := by
  unfold tailWord_3155121
  simp only [CollatzResearch.WordTrace]
  refine ⟨115076716802542943611729217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76717811201695295741152811 115076716802542943611729217)
  ·
    refine ⟨86307537601907207708796913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115076716802542943611729217 86307537601907207708796913)
    ·
      refine ⟨64730653201430405781597685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86307537601907207708796913 64730653201430405781597685)
      ·
        refine ⟨6068498737634100542024783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64730653201430405781597685 6068498737634100542024783)
        ·
          refine ⟨9102748106451150813037175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6068498737634100542024783 9102748106451150813037175)
          ·
            refine ⟨13654122159676726219555763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9102748106451150813037175 13654122159676726219555763)
            ·
              refine ⟨20481183239515089329333645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13654122159676726219555763 20481183239515089329333645)
              ·
                refine ⟨7680443714818158498500117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20481183239515089329333645 7680443714818158498500117)
                ·
                  refine ⟨360020799132101179617193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7680443714818158498500117 360020799132101179617193)
                  ·
                    rfl

theorem cell22_3155121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 6].length) (baseStart_3155121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155121 prefixEnd_3155121 := by exact prefixLift 3155121
  have htrace : WordTrace (prefixWord ++ tailWord_3155121) baseStart_3155121 baseEnd_3155121 := by
    simpa [prefixWord, tailWord_3155121, baseEnd_3155121] using wordTrace_append hprefix tailTrace_3155121
  have hstable : (prefixWord ++ tailWord_3155121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155121).length < 2 ^ (prefixWord ++ tailWord_3155121).sum := by decide
  have hdescent : baseEnd_3155121 < baseStart_3155121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155140 : List Nat := [2, 3, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_3155140 : Nat := 118140960795 + 3155140 * 2 ^ 59
def prefixEnd_3155140 : Nat := 4983230072969 + 3 ^ 40 * 3155140 * 2
def baseEnd_3155140 : Nat := 1080068901484593822626521

theorem tailTrace_3155140 : CollatzResearch.WordTrace tailWord_3155140 prefixEnd_3155140 1080068901484593822626521 := by
  unfold tailWord_3155140
  simp only [CollatzResearch.WordTrace]
  refine ⟨57538704894737054928335437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76718273192982739904447249 57538704894737054928335437)
  ·
    refine ⟨21577014335526395598125789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57538704894737054928335437 21577014335526395598125789)
    ·
      refine ⟨8091380375822398349297171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21577014335526395598125789 8091380375822398349297171)
      ·
        refine ⟨12137070563733597523945757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8091380375822398349297171 12137070563733597523945757)
        ·
          refine ⟨4551401461400099071479659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12137070563733597523945757 4551401461400099071479659)
          ·
            refine ⟨6827102192100148607219489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4551401461400099071479659 6827102192100148607219489)
            ·
              refine ⟨5120326644075111455414617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6827102192100148607219489 5120326644075111455414617)
              ·
                refine ⟨3840244983056333591560963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5120326644075111455414617 3840244983056333591560963)
                ·
                  refine ⟨5760367474584500387341445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3840244983056333591560963 5760367474584500387341445)
                  ·
                    refine ⟨1080068901484593822626521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5760367474584500387341445 1080068901484593822626521)
                    ·
                      rfl

theorem cell22_3155140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_3155140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155140 prefixEnd_3155140 := by exact prefixLift 3155140
  have htrace : WordTrace (prefixWord ++ tailWord_3155140) baseStart_3155140 baseEnd_3155140 := by
    simpa [prefixWord, tailWord_3155140, baseEnd_3155140] using wordTrace_append hprefix tailTrace_3155140
  have hstable : (prefixWord ++ tailWord_3155140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155140).length < 2 ^ (prefixWord ++ tailWord_3155140).sum := by decide
  have hdescent : baseEnd_3155140 < baseStart_3155140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155232 : List Nat := [2, 1, 1, 5, 3, 1, 1, 4, 1, 3]
def baseStart_3155232 : Nat := 118140960795 + 3155232 * 2 ^ 59
def prefixEnd_3155232 : Nat := 4983230072969 + 3 ^ 40 * 3155232 * 2
def baseEnd_3155232 : Nat := 1080100394964736249326239

theorem tailTrace_3155232 : CollatzResearch.WordTrace tailWord_3155232 prefixEnd_3155232 1080100394964736249326239 := by
  unfold tailWord_3155232
  simp only [CollatzResearch.WordTrace]
  refine ⟨57540382652570404784509975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76720510203427206379346633 57540382652570404784509975)
  ·
    refine ⟨86310573978855607176764963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57540382652570404784509975 86310573978855607176764963)
    ·
      refine ⟨129465860968283410765147445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86310573978855607176764963 129465860968283410765147445)
      ·
        refine ⟨12137424465776569759232573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129465860968283410765147445 12137424465776569759232573)
        ·
          refine ⟨4551534174666213659712215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12137424465776569759232573 4551534174666213659712215)
          ·
            refine ⟨6827301261999320489568323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4551534174666213659712215 6827301261999320489568323)
            ·
              refine ⟨10240951892998980734352485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6827301261999320489568323 10240951892998980734352485)
              ·
                refine ⟨1920178479937308887691091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10240951892998980734352485 1920178479937308887691091)
                ·
                  refine ⟨2880267719905963331536637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920178479937308887691091 2880267719905963331536637)
                  ·
                    refine ⟨1080100394964736249326239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2880267719905963331536637 1080100394964736249326239)
                    ·
                      rfl

theorem cell22_3155232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 1, 3].length) (baseStart_3155232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155232 prefixEnd_3155232 := by exact prefixLift 3155232
  have htrace : WordTrace (prefixWord ++ tailWord_3155232) baseStart_3155232 baseEnd_3155232 := by
    simpa [prefixWord, tailWord_3155232, baseEnd_3155232] using wordTrace_append hprefix tailTrace_3155232
  have hstable : (prefixWord ++ tailWord_3155232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155232).length < 2 ^ (prefixWord ++ tailWord_3155232).sum := by decide
  have hdescent : baseEnd_3155232 < baseStart_3155232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155245 : List Nat := [1, 5, 3, 1, 1, 1, 2, 3, 5]
def baseStart_3155245 : Nat := 118140960795 + 3155245 * 2 ^ 59
def prefixEnd_3155245 : Nat := 4983230072969 + 3 ^ 40 * 3155245 * 2
def baseEnd_3155245 : Nat := 360034948376802849583733

theorem tailTrace_3155245 : CollatzResearch.WordTrace tailWord_3155245 prefixEnd_3155245 360034948376802849583733 := by
  unfold tailWord_3155245
  simp only [CollatzResearch.WordTrace]
  refine ⟨115081239454093712789243189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76720826302729141859495459 115081239454093712789243189)
  ·
    refine ⟨10788866198821285573991549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115081239454093712789243189 10788866198821285573991549)
    ·
      refine ⟨4045824824557982090246831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10788866198821285573991549 4045824824557982090246831)
      ·
        refine ⟨6068737236836973135370247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4045824824557982090246831 6068737236836973135370247)
        ·
          refine ⟨9103105855255459703055371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6068737236836973135370247 9103105855255459703055371)
          ·
            refine ⟨13654658782883189554583057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9103105855255459703055371 13654658782883189554583057)
            ·
              refine ⟨10240994087162392165937293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13654658782883189554583057 10240994087162392165937293)
              ·
                refine ⟨3840372782685897062226485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10240994087162392165937293 3840372782685897062226485)
                ·
                  refine ⟨360034948376802849583733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3840372782685897062226485 360034948376802849583733)
                  ·
                    rfl

theorem cell22_3155245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_3155245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155245 prefixEnd_3155245 := by exact prefixLift 3155245
  have htrace : WordTrace (prefixWord ++ tailWord_3155245) baseStart_3155245 baseEnd_3155245 := by
    simpa [prefixWord, tailWord_3155245, baseEnd_3155245] using wordTrace_append hprefix tailTrace_3155245
  have hstable : (prefixWord ++ tailWord_3155245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155245).length < 2 ^ (prefixWord ++ tailWord_3155245).sum := by decide
  have hdescent : baseEnd_3155245 < baseStart_3155245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155258 : List Nat := [3, 1, 1, 1, 4, 1, 2, 4, 1, 4]
def baseStart_3155258 : Nat := 118140960795 + 3155258 * 2 ^ 59
def prefixEnd_3155258 : Nat := 4983230072969 + 3 ^ 40 * 3155258 * 2
def baseEnd_3155258 : Nat := 1080109295296080848176159

theorem tailTrace_3155258 : CollatzResearch.WordTrace tailWord_3155258 prefixEnd_3155258 1080109295296080848176159 := by
  unfold tailWord_3155258
  simp only [CollatzResearch.WordTrace]
  refine ⟨28770428400761654002366607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76721142402031077339644285 28770428400761654002366607)
  ·
    refine ⟨43155642601142481003549911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28770428400761654002366607 43155642601142481003549911)
    ·
      refine ⟨64733463901713721505324867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43155642601142481003549911 64733463901713721505324867)
      ·
        refine ⟨97100195852570582257987301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64733463901713721505324867 97100195852570582257987301)
        ·
          refine ⟨18206286722356984173372619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97100195852570582257987301 18206286722356984173372619)
          ·
            refine ⟨27309430083535476260058929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18206286722356984173372619 27309430083535476260058929)
            ·
              refine ⟨20482072562651607195044197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27309430083535476260058929 20482072562651607195044197)
              ·
                refine ⟨3840388605497176349070787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20482072562651607195044197 3840388605497176349070787)
                ·
                  refine ⟨5760582908245764523606181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3840388605497176349070787 5760582908245764523606181)
                  ·
                    refine ⟨1080109295296080848176159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5760582908245764523606181 1080109295296080848176159)
                    ·
                      rfl

theorem cell22_3155258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_3155258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155258 prefixEnd_3155258 := by exact prefixLift 3155258
  have htrace : WordTrace (prefixWord ++ tailWord_3155258) baseStart_3155258 baseEnd_3155258 := by
    simpa [prefixWord, tailWord_3155258, baseEnd_3155258] using wordTrace_append hprefix tailTrace_3155258
  have hstable : (prefixWord ++ tailWord_3155258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155258).length < 2 ^ (prefixWord ++ tailWord_3155258).sum := by decide
  have hdescent : baseEnd_3155258 < baseStart_3155258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155273 : List Nat := [1, 2, 1, 1, 2, 3, 3, 5, 4]
def baseStart_3155273 : Nat := 118140960795 + 3155273 * 2 ^ 59
def prefixEnd_3155273 : Nat := 4983230072969 + 3 ^ 40 * 3155273 * 2
def baseEnd_3155273 : Nat := 360038143367541936350371

theorem tailTrace_3155273 : CollatzResearch.WordTrace tailWord_3155273 prefixEnd_3155273 360038143367541936350371 := by
  unfold tailWord_3155273
  simp only [CollatzResearch.WordTrace]
  refine ⟨115082260697992273571262473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76721507131994849047508315 115082260697992273571262473)
  ·
    refine ⟨86311695523494205178446855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115082260697992273571262473 86311695523494205178446855)
    ·
      refine ⟨129467543285241307767670283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86311695523494205178446855 129467543285241307767670283)
      ·
        refine ⟨194201314927861961651505425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129467543285241307767670283 194201314927861961651505425)
        ·
          refine ⟨145650986195896471238629069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194201314927861961651505425 145650986195896471238629069)
          ·
            refine ⟨54619119823461176714485901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145650986195896471238629069 54619119823461176714485901)
            ·
              refine ⟨20482169933797941267932213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54619119823461176714485901 20482169933797941267932213)
              ·
                refine ⟨1920203431293556993868645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20482169933797941267932213 1920203431293556993868645)
                ·
                  refine ⟨360038143367541936350371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1920203431293556993868645 360038143367541936350371)
                  ·
                    rfl

theorem cell22_3155273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 5, 4].length) (baseStart_3155273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155273 prefixEnd_3155273 := by exact prefixLift 3155273
  have htrace : WordTrace (prefixWord ++ tailWord_3155273) baseStart_3155273 baseEnd_3155273 := by
    simpa [prefixWord, tailWord_3155273, baseEnd_3155273] using wordTrace_append hprefix tailTrace_3155273
  have hstable : (prefixWord ++ tailWord_3155273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155273).length < 2 ^ (prefixWord ++ tailWord_3155273).sum := by decide
  have hdescent : baseEnd_3155273 < baseStart_3155273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155288 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 4, 3]
def baseStart_3155288 : Nat := 118140960795 + 3155288 * 2 ^ 59
def prefixEnd_3155288 : Nat := 4983230072969 + 3 ^ 40 * 3155288 * 2
def baseEnd_3155288 : Nat := 1080119564909170769926067

theorem tailTrace_3155288 : CollatzResearch.WordTrace tailWord_3155288 prefixEnd_3155288 1080119564909170769926067 := by
  unfold tailWord_3155288
  simp only [CollatzResearch.WordTrace]
  refine ⟨57541403896468965566529259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76721871861958620755372345 57541403896468965566529259)
  ·
    refine ⟨86312105844703448349793889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57541403896468965566529259 86312105844703448349793889)
    ·
      refine ⟨64734079383527586262345417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86312105844703448349793889 64734079383527586262345417)
      ·
        refine ⟨48550559537645689696759063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64734079383527586262345417 48550559537645689696759063)
        ·
          refine ⟨72825839306468534545138595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48550559537645689696759063 72825839306468534545138595)
          ·
            refine ⟨109238758959702801817707893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72825839306468534545138595 109238758959702801817707893)
            ·
              refine ⟨10241133652472137670410115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109238758959702801817707893 10241133652472137670410115)
              ·
                refine ⟨15361700478708206505615173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10241133652472137670410115 15361700478708206505615173)
                ·
                  refine ⟨2880318839757788719802845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15361700478708206505615173 2880318839757788719802845)
                  ·
                    refine ⟨1080119564909170769926067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2880318839757788719802845 1080119564909170769926067)
                    ·
                      rfl

theorem cell22_3155288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_3155288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155288 prefixEnd_3155288 := by exact prefixLift 3155288
  have htrace : WordTrace (prefixWord ++ tailWord_3155288) baseStart_3155288 baseEnd_3155288 := by
    simpa [prefixWord, tailWord_3155288, baseEnd_3155288] using wordTrace_append hprefix tailTrace_3155288
  have hstable : (prefixWord ++ tailWord_3155288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155288).length < 2 ^ (prefixWord ++ tailWord_3155288).sum := by decide
  have hdescent : baseEnd_3155288 < baseStart_3155288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155301 : List Nat := [1, 3, 1, 3, 1, 2, 2, 9]
def baseStart_3155301 : Nat := 118140960795 + 3155301 * 2 ^ 59
def prefixEnd_3155301 : Nat := 4983230072969 + 3 ^ 40 * 3155301 * 2
def baseEnd_3155301 : Nat := 120013779452760341039003

theorem tailTrace_3155301 : CollatzResearch.WordTrace tailWord_3155301 prefixEnd_3155301 120013779452760341039003 := by
  unfold tailWord_3155301
  simp only [CollatzResearch.WordTrace]
  refine ⟨115083281941890834353281757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76722187961260556235521171 115083281941890834353281757)
  ·
    refine ⟨43156230728209062882480659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115083281941890834353281757 43156230728209062882480659)
    ·
      refine ⟨64734346092313594323720989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43156230728209062882480659 64734346092313594323720989)
      ·
        refine ⟨24275379784617597871395371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64734346092313594323720989 24275379784617597871395371)
        ·
          refine ⟨36413069676926396807093057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24275379784617597871395371 36413069676926396807093057)
          ·
            refine ⟨27309802257694797605319793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36413069676926396807093057 27309802257694797605319793)
            ·
              refine ⟨20482351693271098203989845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27309802257694797605319793 20482351693271098203989845)
              ·
                refine ⟨120013779452760341039003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20482351693271098203989845 120013779452760341039003)
                ·
                  rfl

theorem cell22_3155301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 9].length) (baseStart_3155301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155301 prefixEnd_3155301 := by exact prefixLift 3155301
  have htrace : WordTrace (prefixWord ++ tailWord_3155301) baseStart_3155301 baseEnd_3155301 := by
    simpa [prefixWord, tailWord_3155301, baseEnd_3155301] using wordTrace_append hprefix tailTrace_3155301
  have hstable : (prefixWord ++ tailWord_3155301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155301).length < 2 ^ (prefixWord ++ tailWord_3155301).sum := by decide
  have hdescent : baseEnd_3155301 < baseStart_3155301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155333 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 5, 3]
def baseStart_3155333 : Nat := 118140960795 + 3155333 * 2 ^ 59
def prefixEnd_3155333 : Nat := 4983230072969 + 3 ^ 40 * 3155333 * 2
def baseEnd_3155333 : Nat := 1080134969328805652550929

theorem tailTrace_3155333 : CollatzResearch.WordTrace tailWord_3155333 prefixEnd_3155333 1080134969328805652550929 := by
  unfold tailWord_3155333
  simp only [CollatzResearch.WordTrace]
  refine ⟨115084449077774903818446653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76722966051849935878964435 115084449077774903818446653)
  ·
    refine ⟨43156668404165588931917495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115084449077774903818446653 43156668404165588931917495)
    ·
      refine ⟨64735002606248383397876243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43156668404165588931917495 64735002606248383397876243)
      ·
        refine ⟨97102503909372575096814365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64735002606248383397876243 97102503909372575096814365)
        ·
          refine ⟨36413438966014715661305387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97102503909372575096814365 36413438966014715661305387)
          ·
            refine ⟨54620158449022073491958081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36413438966014715661305387 54620158449022073491958081)
            ·
              refine ⟨40965118836766555118968561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54620158449022073491958081 40965118836766555118968561)
              ·
                refine ⟨30723839127574916339226421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40965118836766555118968561 30723839127574916339226421)
                ·
                  refine ⟨2880359918210148406802477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30723839127574916339226421 2880359918210148406802477)
                  ·
                    refine ⟨1080134969328805652550929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2880359918210148406802477 1080134969328805652550929)
                    ·
                      rfl

theorem cell22_3155333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_3155333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155333 prefixEnd_3155333 := by exact prefixLift 3155333
  have htrace : WordTrace (prefixWord ++ tailWord_3155333) baseStart_3155333 baseEnd_3155333 := by
    simpa [prefixWord, tailWord_3155333, baseEnd_3155333] using wordTrace_append hprefix tailTrace_3155333
  have hstable : (prefixWord ++ tailWord_3155333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155333).length < 2 ^ (prefixWord ++ tailWord_3155333).sum := by decide
  have hdescent : baseEnd_3155333 < baseStart_3155333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155356 : List Nat := [2, 2, 3, 4, 1, 2, 2, 1, 2, 3]
def baseStart_3155356 : Nat := 118140960795 + 3155356 * 2 ^ 59
def prefixEnd_3155356 : Nat := 4983230072969 + 3 ^ 40 * 3155356 * 2
def baseEnd_3155356 : Nat := 1080142842698841259225859

theorem tailTrace_3155356 : CollatzResearch.WordTrace tailWord_3155356 prefixEnd_3155356 1080142842698841259225859 := by
  unfold tailWord_3155356
  simp only [CollatzResearch.WordTrace]
  refine ⟨57542643978345789373266961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76723525304461052497689281 57542643978345789373266961)
  ·
    refine ⟨43156982983759342029950221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57542643978345789373266961 43156982983759342029950221)
    ·
      refine ⟨16183868618909753261231333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43156982983759342029950221 16183868618909753261231333)
      ·
        refine ⟨3034475366045578736480875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16183868618909753261231333 3034475366045578736480875)
        ·
          refine ⟨4551713049068368104721313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034475366045578736480875 4551713049068368104721313)
          ·
            refine ⟨3413784786801276078540985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4551713049068368104721313 3413784786801276078540985)
            ·
              refine ⟨2560338590100957058905739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3413784786801276078540985 2560338590100957058905739)
              ·
                refine ⟨3840507885151435588358609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2560338590100957058905739 3840507885151435588358609)
                ·
                  refine ⟨2880380913863576691268957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3840507885151435588358609 2880380913863576691268957)
                  ·
                    refine ⟨1080142842698841259225859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2880380913863576691268957 1080142842698841259225859)
                    ·
                      rfl

theorem cell22_3155356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_3155356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155356 prefixEnd_3155356 := by exact prefixLift 3155356
  have htrace : WordTrace (prefixWord ++ tailWord_3155356) baseStart_3155356 baseEnd_3155356 := by
    simpa [prefixWord, tailWord_3155356, baseEnd_3155356] using wordTrace_append hprefix tailTrace_3155356
  have hstable : (prefixWord ++ tailWord_3155356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155356).length < 2 ^ (prefixWord ++ tailWord_3155356).sum := by decide
  have hdescent : baseEnd_3155356 < baseStart_3155356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155363 : List Nat := [1, 1, 1, 4, 1, 3, 3, 3, 5]
def baseStart_3155363 : Nat := 118140960795 + 3155363 * 2 ^ 59
def prefixEnd_3155363 : Nat := 4983230072969 + 3 ^ 40 * 3155363 * 2
def baseEnd_3155363 : Nat := 360048412980631858100279

theorem tailTrace_3155363 : CollatzResearch.WordTrace tailWord_3155363 prefixEnd_3155363 360048412980631858100279 := by
  unfold tailWord_3155363
  simp only [CollatzResearch.WordTrace]
  refine ⟨115085543267666218942038743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76723695511777479294692495 115085543267666218942038743)
  ·
    refine ⟨172628314901499328413058115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115085543267666218942038743 172628314901499328413058115)
    ·
      refine ⟨258942472352248992619587173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172628314901499328413058115 258942472352248992619587173)
      ·
        refine ⟨48551713566046686116172595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258942472352248992619587173 48551713566046686116172595)
        ·
          refine ⟨72827570349070029174258893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48551713566046686116172595 72827570349070029174258893)
          ·
            refine ⟨27310338880901260940347085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72827570349070029174258893 27310338880901260940347085)
            ·
              refine ⟨10241377080337972852630157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27310338880901260940347085 10241377080337972852630157)
              ·
                refine ⟨3840516405126739819736309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10241377080337972852630157 3840516405126739819736309)
                ·
                  refine ⟨360048412980631858100279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3840516405126739819736309 360048412980631858100279)
                  ·
                    rfl

theorem cell22_3155363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 3, 5].length) (baseStart_3155363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155363 prefixEnd_3155363 := by exact prefixLift 3155363
  have htrace : WordTrace (prefixWord ++ tailWord_3155363) baseStart_3155363 baseEnd_3155363 := by
    simpa [prefixWord, tailWord_3155363, baseEnd_3155363] using wordTrace_append hprefix tailTrace_3155363
  have hstable : (prefixWord ++ tailWord_3155363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155363).length < 2 ^ (prefixWord ++ tailWord_3155363).sum := by decide
  have hdescent : baseEnd_3155363 < baseStart_3155363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155442 : List Nat := [3, 2, 1, 4, 1, 1, 1, 5, 4]
def baseStart_3155442 : Nat := 118140960795 + 3155442 * 2 ^ 59
def prefixEnd_3155442 : Nat := 4983230072969 + 3 ^ 40 * 3155442 * 2
def baseEnd_3155442 : Nat := 360057427418788567191865

theorem tailTrace_3155442 : CollatzResearch.WordTrace tailWord_3155442 prefixEnd_3155442 360057427418788567191865 := by
  unfold tailWord_3155442
  simp only [CollatzResearch.WordTrace]
  refine ⟨28772106158595003858541145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76725616422920010289443053 28772106158595003858541145)
  ·
    refine ⟨21579079618946252893905859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28772106158595003858541145 21579079618946252893905859)
    ·
      refine ⟨32368619428419379340858789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21579079618946252893905859 32368619428419379340858789)
      ·
        refine ⟨6069116142828633626411023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32368619428419379340858789 6069116142828633626411023)
        ·
          refine ⟨9103674214242950439616535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6069116142828633626411023 9103674214242950439616535)
          ·
            refine ⟨13655511321364425659424803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9103674214242950439616535 13655511321364425659424803)
            ·
              refine ⟨20483266982046638489137205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13655511321364425659424803 20483266982046638489137205)
              ·
                refine ⟨1920306279566872358356613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20483266982046638489137205 1920306279566872358356613)
                ·
                  refine ⟨360057427418788567191865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1920306279566872358356613 360057427418788567191865)
                  ·
                    rfl

theorem cell22_3155442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_3155442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155442 prefixEnd_3155442 := by exact prefixLift 3155442
  have htrace : WordTrace (prefixWord ++ tailWord_3155442) baseStart_3155442 baseEnd_3155442 := by
    simpa [prefixWord, tailWord_3155442, baseEnd_3155442] using wordTrace_append hprefix tailTrace_3155442
  have hstable : (prefixWord ++ tailWord_3155442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155442).length < 2 ^ (prefixWord ++ tailWord_3155442).sum := by decide
  have hdescent : baseEnd_3155442 < baseStart_3155442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155453 : List Nat := [1, 4, 1, 1, 1, 5, 9]
def baseStart_3155453 : Nat := 118140960795 + 3155453 * 2 ^ 59
def prefixEnd_3155453 : Nat := 4983230072969 + 3 ^ 40 * 3155453 * 2
def baseEnd_3155453 : Nat := 40006520288191308872243

theorem tailTrace_3155453 : CollatzResearch.WordTrace tailWord_3155453 prefixEnd_3155453 40006520288191308872243 := by
  unfold tailWord_3155453
  simp only [CollatzResearch.WordTrace]
  refine ⟨115088825837340164312815013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76725883891560109541876675 115088825837340164312815013)
  ·
    refine ⟨21579154844501280808652815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115088825837340164312815013 21579154844501280808652815)
    ·
      refine ⟨32368732266751921212979223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21579154844501280808652815 32368732266751921212979223)
      ·
        refine ⟨48553098400127881819468835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32368732266751921212979223 48553098400127881819468835)
        ·
          refine ⟨72829647600191822729203253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48553098400127881819468835 72829647600191822729203253)
          ·
            refine ⟨6827779462517983380862805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72829647600191822729203253 6827779462517983380862805)
            ·
              refine ⟨40006520288191308872243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6827779462517983380862805 40006520288191308872243)
              ·
                rfl

theorem cell22_3155453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 9].length) (baseStart_3155453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155453 prefixEnd_3155453 := by exact prefixLift 3155453
  have htrace : WordTrace (prefixWord ++ tailWord_3155453) baseStart_3155453 baseEnd_3155453 := by
    simpa [prefixWord, tailWord_3155453, baseEnd_3155453] using wordTrace_append hprefix tailTrace_3155453
  have hstable : (prefixWord ++ tailWord_3155453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155453).length < 2 ^ (prefixWord ++ tailWord_3155453).sum := by decide
  have hdescent : baseEnd_3155453 < baseStart_3155453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155457 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 4, 3]
def baseStart_3155457 : Nat := 118140960795 + 3155457 * 2 ^ 59
def prefixEnd_3155457 : Nat := 4983230072969 + 3 ^ 40 * 3155457 * 2
def baseEnd_3155457 : Nat := 1080177417062910662450549

theorem tailTrace_3155457 : CollatzResearch.WordTrace tailWord_3155457 prefixEnd_3155457 1080177417062910662450549 := by
  unfold tailWord_3155457
  simp only [CollatzResearch.WordTrace]
  refine ⟨115088971729325672995960625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76725981152883781997307083 115088971729325672995960625)
  ·
    refine ⟨86316728796994254746970469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115088971729325672995960625 86316728796994254746970469)
    ·
      refine ⟨16184386649436422765056963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86316728796994254746970469 16184386649436422765056963)
      ·
        refine ⟨24276579974154634147585445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16184386649436422765056963 24276579974154634147585445)
        ·
          refine ⟨4551858745153993902672271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24276579974154634147585445 4551858745153993902672271)
          ·
            refine ⟨6827788117730990854008407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4551858745153993902672271 6827788117730990854008407)
            ·
              refine ⟨10241682176596486281012611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6827788117730990854008407 10241682176596486281012611)
              ·
                refine ⟨15362523264894729421518917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10241682176596486281012611 15362523264894729421518917)
                ·
                  refine ⟨2880473112167761766534797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15362523264894729421518917 2880473112167761766534797)
                  ·
                    refine ⟨1080177417062910662450549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2880473112167761766534797 1080177417062910662450549)
                    ·
                      rfl

theorem cell22_3155457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_3155457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155457 prefixEnd_3155457 := by exact prefixLift 3155457
  have htrace : WordTrace (prefixWord ++ tailWord_3155457) baseStart_3155457 baseEnd_3155457 := by
    simpa [prefixWord, tailWord_3155457, baseEnd_3155457] using wordTrace_append hprefix tailTrace_3155457
  have hstable : (prefixWord ++ tailWord_3155457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155457).length < 2 ^ (prefixWord ++ tailWord_3155457).sum := by decide
  have hdescent : baseEnd_3155457 < baseStart_3155457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155528 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 1, 10]
def baseStart_3155528 : Nat := 118140960795 + 3155528 * 2 ^ 59
def prefixEnd_3155528 : Nat := 4983230072969 + 3 ^ 40 * 3155528 * 2
def baseEnd_3155528 : Nat := 1080201721813890143925331

theorem tailTrace_3155528 : CollatzResearch.WordTrace tailWord_3155528 prefixEnd_3155528 1080201721813890143925331 := by
  unfold tailWord_3155528
  simp only [CollatzResearch.WordTrace]
  refine ⟨57545780656034226060897619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76727707541378968081196825 57545780656034226060897619)
  ·
    refine ⟨86318670984051339091346429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57545780656034226060897619 86318670984051339091346429)
    ·
      refine ⟨32369501619019252159254911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86318670984051339091346429 32369501619019252159254911)
      ·
        refine ⟨48554252428528878238882367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32369501619019252159254911 48554252428528878238882367)
        ·
          refine ⟨72831378642793317358323551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48554252428528878238882367 72831378642793317358323551)
          ·
            refine ⟨109247067964189976037485327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72831378642793317358323551 109247067964189976037485327)
            ·
              refine ⟨163870601946284964056227991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109247067964189976037485327 163870601946284964056227991)
              ·
                refine ⟨245805902919427446084341987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163870601946284964056227991 245805902919427446084341987)
                ·
                  refine ⟨368708854379141169126512981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245805902919427446084341987 368708854379141169126512981)
                  ·
                    refine ⟨1080201721813890143925331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 368708854379141169126512981 1080201721813890143925331)
                    ·
                      rfl

theorem cell22_3155528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_3155528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155528 prefixEnd_3155528 := by exact prefixLift 3155528
  have htrace : WordTrace (prefixWord ++ tailWord_3155528) baseStart_3155528 baseEnd_3155528 := by
    simpa [prefixWord, tailWord_3155528, baseEnd_3155528] using wordTrace_append hprefix tailTrace_3155528
  have hstable : (prefixWord ++ tailWord_3155528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155528).length < 2 ^ (prefixWord ++ tailWord_3155528).sum := by decide
  have hdescent : baseEnd_3155528 < baseStart_3155528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155532 : List Nat := [2, 2, 1, 3, 1, 3, 4, 1, 5]
def baseStart_3155532 : Nat := 118140960795 + 3155532 * 2 ^ 59
def prefixEnd_3155532 : Nat := 4983230072969 + 3 ^ 40 * 3155532 * 2
def baseEnd_3155532 : Nat := 360067697031878488941773

theorem tailTrace_3155532 : CollatzResearch.WordTrace tailWord_3155532 prefixEnd_3155532 360067697031878488941773 := by
  unfold tailWord_3155532
  simp only [CollatzResearch.WordTrace]
  refine ⟨57545853602026980402470425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76727804802702640536627233 57545853602026980402470425)
  ·
    refine ⟨43159390201520235301852819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57545853602026980402470425 43159390201520235301852819)
    ·
      refine ⟨64739085302280352952779229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43159390201520235301852819 64739085302280352952779229)
      ·
        refine ⟨24277156988355132357292211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64739085302280352952779229 24277156988355132357292211)
        ·
          refine ⟨36415735482532698535938317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24277156988355132357292211 36415735482532698535938317)
          ·
            refine ⟨13655900805949761950976869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36415735482532698535938317 13655900805949761950976869)
            ·
              refine ⟨2560481401115580365808163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13655900805949761950976869 2560481401115580365808163)
              ·
                refine ⟨3840722101673370548712245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2560481401115580365808163 3840722101673370548712245)
                ·
                  refine ⟨360067697031878488941773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3840722101673370548712245 360067697031878488941773)
                  ·
                    rfl

theorem cell22_3155532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_3155532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155532 prefixEnd_3155532 := by exact prefixLift 3155532
  have htrace : WordTrace (prefixWord ++ tailWord_3155532) baseStart_3155532 baseEnd_3155532 := by
    simpa [prefixWord, tailWord_3155532, baseEnd_3155532] using wordTrace_append hprefix tailTrace_3155532
  have hstable : (prefixWord ++ tailWord_3155532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155532).length < 2 ^ (prefixWord ++ tailWord_3155532).sum := by decide
  have hdescent : baseEnd_3155532 < baseStart_3155532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155577 : List Nat := [1, 2, 1, 3, 3, 1, 3, 4, 4]
def baseStart_3155577 : Nat := 118140960795 + 3155577 * 2 ^ 59
def prefixEnd_3155577 : Nat := 4983230072969 + 3 ^ 40 * 3155577 * 2
def baseEnd_3155577 : Nat := 360072831838423449816727

theorem tailTrace_3155577 : CollatzResearch.WordTrace tailWord_3155577 prefixEnd_3155577 360072831838423449816727 := by
  unfold tailWord_3155577
  simp only [CollatzResearch.WordTrace]
  refine ⟨115093348488890933490328985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76728898992593955660219323 115093348488890933490328985)
  ·
    refine ⟨86320011366668200117746739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115093348488890933490328985 86320011366668200117746739)
    ·
      refine ⟨129480017050002300176620109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86320011366668200117746739 129480017050002300176620109)
      ·
        refine ⟨48555006393750862566232541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129480017050002300176620109 48555006393750862566232541)
        ·
          refine ⟨18208127397656573462337203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48555006393750862566232541 18208127397656573462337203)
          ·
            refine ⟨27312191096484860193505805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18208127397656573462337203 27312191096484860193505805)
            ·
              refine ⟨10242071661181822572564677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27312191096484860193505805 10242071661181822572564677)
              ·
                refine ⟨1920388436471591732355877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10242071661181822572564677 1920388436471591732355877)
                ·
                  refine ⟨360072831838423449816727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1920388436471591732355877 360072831838423449816727)
                  ·
                    rfl

theorem cell22_3155577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 4, 4].length) (baseStart_3155577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155577 prefixEnd_3155577 := by exact prefixLift 3155577
  have htrace : WordTrace (prefixWord ++ tailWord_3155577) baseStart_3155577 baseEnd_3155577 := by
    simpa [prefixWord, tailWord_3155577, baseEnd_3155577] using wordTrace_append hprefix tailTrace_3155577
  have hstable : (prefixWord ++ tailWord_3155577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155577).length < 2 ^ (prefixWord ++ tailWord_3155577).sum := by decide
  have hdescent : baseEnd_3155577 < baseStart_3155577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155607 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 2, 4]
def baseStart_3155607 : Nat := 118140960795 + 3155607 * 2 ^ 59
def prefixEnd_3155607 : Nat := 4983230072969 + 3 ^ 40 * 3155607 * 2
def baseEnd_3155607 : Nat := 1080228765128360271200089

theorem tailTrace_3155607 : CollatzResearch.WordTrace tailWord_3155607 prefixEnd_3155607 1080228765128360271200089 := by
  unfold tailWord_3155607
  simp only [CollatzResearch.WordTrace]
  refine ⟨115094442678782248613921075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76729628452521499075947383 115094442678782248613921075)
  ·
    refine ⟨172641664018173372920881613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115094442678782248613921075 172641664018173372920881613)
    ·
      refine ⟨64740624006815014845330605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172641664018173372920881613 64740624006815014845330605)
      ·
        refine ⟨24277734002555630566998977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64740624006815014845330605 24277734002555630566998977)
        ·
          refine ⟨18208300501916722925249233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24277734002555630566998977 18208300501916722925249233)
          ·
            refine ⟨13656225376437542193936925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18208300501916722925249233 13656225376437542193936925)
            ·
              refine ⟨5121084516164078322726347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13656225376437542193936925 5121084516164078322726347)
              ·
                refine ⟨7681626774246117484089521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121084516164078322726347 7681626774246117484089521)
                ·
                  refine ⟨5761220080684588113067141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7681626774246117484089521 5761220080684588113067141)
                  ·
                    refine ⟨1080228765128360271200089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5761220080684588113067141 1080228765128360271200089)
                    ·
                      rfl

theorem cell22_3155607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_3155607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155607 prefixEnd_3155607 := by exact prefixLift 3155607
  have htrace : WordTrace (prefixWord ++ tailWord_3155607) baseStart_3155607 baseEnd_3155607 := by
    simpa [prefixWord, tailWord_3155607, baseEnd_3155607] using wordTrace_append hprefix tailTrace_3155607
  have hstable : (prefixWord ++ tailWord_3155607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155607).length < 2 ^ (prefixWord ++ tailWord_3155607).sum := by decide
  have hdescent : baseEnd_3155607 < baseStart_3155607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155688 : List Nat := [2, 1, 4, 1, 3, 2, 3, 2, 1, 3]
def baseStart_3155688 : Nat := 118140960795 + 3155688 * 2 ^ 59
def prefixEnd_3155688 : Nat := 4983230072969 + 3 ^ 40 * 3155688 * 2
def baseEnd_3155688 : Nat := 1080256493083703059924841

theorem tailTrace_3155688 : CollatzResearch.WordTrace tailWord_3155688 prefixEnd_3155688 1080256493083703059924841 := by
  unfold tailWord_3155688
  simp only [CollatzResearch.WordTrace]
  refine ⟨57548698495744399723809859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76731597994325866298413145 57548698495744399723809859)
  ·
    refine ⟨86323047743616599585714789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57548698495744399723809859 86323047743616599585714789)
    ·
      refine ⟨16185571451928112422321523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86323047743616599585714789 16185571451928112422321523)
      ·
        refine ⟨24278357177892168633482285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16185571451928112422321523 24278357177892168633482285)
        ·
          refine ⟨9104383941709563237555857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24278357177892168633482285 9104383941709563237555857)
          ·
            refine ⟨6828287956282172428166893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9104383941709563237555857 6828287956282172428166893)
            ·
              refine ⟨2560607983605814660562585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6828287956282172428166893 2560607983605814660562585)
              ·
                refine ⟨1920455987704360995421939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2560607983605814660562585 1920455987704360995421939)
                ·
                  refine ⟨2880683981556541493132909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920455987704360995421939 2880683981556541493132909)
                  ·
                    refine ⟨1080256493083703059924841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2880683981556541493132909 1080256493083703059924841)
                    ·
                      rfl

theorem cell22_3155688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_3155688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155688 prefixEnd_3155688 := by exact prefixLift 3155688
  have htrace : WordTrace (prefixWord ++ tailWord_3155688) baseStart_3155688 baseEnd_3155688 := by
    simpa [prefixWord, tailWord_3155688, baseEnd_3155688] using wordTrace_append hprefix tailTrace_3155688
  have hstable : (prefixWord ++ tailWord_3155688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155688).length < 2 ^ (prefixWord ++ tailWord_3155688).sum := by decide
  have hdescent : baseEnd_3155688 < baseStart_3155688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155714 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3155714 : Nat := 118140960795 + 3155714 * 2 ^ 59
def prefixEnd_3155714 : Nat := 4983230072969 + 3 ^ 40 * 3155714 * 2
def baseEnd_3155714 : Nat := 1080265393415047658774761

theorem tailTrace_3155714 : CollatzResearch.WordTrace tailWord_3155714 prefixEnd_3155714 1080265393415047658774761 := by
  unfold tailWord_3155714
  simp only [CollatzResearch.WordTrace]
  refine ⟨28774586322348651472016549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76732230192929737258710797 28774586322348651472016549)
  ·
    refine ⟨5395234935440372151003103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28774586322348651472016549 5395234935440372151003103)
    ·
      refine ⟨8092852403160558226504655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5395234935440372151003103 8092852403160558226504655)
      ·
        refine ⟨12139278604740837339756983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8092852403160558226504655 12139278604740837339756983)
        ·
          refine ⟨18208917907111256009635475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12139278604740837339756983 18208917907111256009635475)
          ·
            refine ⟨27313376860666884014453213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18208917907111256009635475 27313376860666884014453213)
            ·
              refine ⟨10242516322750081505419955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27313376860666884014453213 10242516322750081505419955)
              ·
                refine ⟨15363774484125122258129933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10242516322750081505419955 15363774484125122258129933)
                ·
                  refine ⟨5761415431546920846798725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15363774484125122258129933 5761415431546920846798725)
                  ·
                    refine ⟨1080265393415047658774761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5761415431546920846798725 1080265393415047658774761)
                    ·
                      rfl

theorem cell22_3155714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3155714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155714 prefixEnd_3155714 := by exact prefixLift 3155714
  have htrace : WordTrace (prefixWord ++ tailWord_3155714) baseStart_3155714 baseEnd_3155714 := by
    simpa [prefixWord, tailWord_3155714, baseEnd_3155714] using wordTrace_append hprefix tailTrace_3155714
  have hstable : (prefixWord ++ tailWord_3155714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155714).length < 2 ^ (prefixWord ++ tailWord_3155714).sum := by decide
  have hdescent : baseEnd_3155714 < baseStart_3155714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155727 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 4, 3]
def baseStart_3155727 : Nat := 118140960795 + 3155727 * 2 ^ 59
def prefixEnd_3155727 : Nat := 4983230072969 + 3 ^ 40 * 3155727 * 2
def baseEnd_3155727 : Nat := 1080269843580719958199721

theorem tailTrace_3155727 : CollatzResearch.WordTrace tailWord_3155727 prefixEnd_3155727 1080269843580719958199721 := by
  unfold tailWord_3155727
  simp only [CollatzResearch.WordTrace]
  refine ⟨115098819438347509108289435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76732546292231672738859623 115098819438347509108289435)
  ·
    refine ⟨172648229157521263662434153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115098819438347509108289435 172648229157521263662434153)
    ·
      refine ⟨129486171868140947746825615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172648229157521263662434153 129486171868140947746825615)
      ·
        refine ⟨194229257802211421620238423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129486171868140947746825615 194229257802211421620238423)
        ·
          refine ⟨291343886703317132430357635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194229257802211421620238423 291343886703317132430357635)
          ·
            refine ⟨437015830054975698645536453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291343886703317132430357635 437015830054975698645536453)
            ·
              refine ⟨81940468135307943496038085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 437015830054975698645536453 81940468135307943496038085)
              ·
                refine ⟨15363837775370239405507141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81940468135307943496038085 15363837775370239405507141)
                ·
                  refine ⟨2880719582881919888532589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15363837775370239405507141 2880719582881919888532589)
                  ·
                    refine ⟨1080269843580719958199721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2880719582881919888532589 1080269843580719958199721)
                    ·
                      rfl

theorem cell22_3155727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 3].length) (baseStart_3155727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155727 prefixEnd_3155727 := by exact prefixLift 3155727
  have htrace : WordTrace (prefixWord ++ tailWord_3155727) baseStart_3155727 baseEnd_3155727 := by
    simpa [prefixWord, tailWord_3155727, baseEnd_3155727] using wordTrace_append hprefix tailTrace_3155727
  have hstable : (prefixWord ++ tailWord_3155727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155727).length < 2 ^ (prefixWord ++ tailWord_3155727).sum := by decide
  have hdescent : baseEnd_3155727 < baseStart_3155727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155802 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 7]
def baseStart_3155802 : Nat := 118140960795 + 3155802 * 2 ^ 59
def prefixEnd_3155802 : Nat := 4983230072969 + 3 ^ 40 * 3155802 * 2
def baseEnd_3155802 : Nat := 360098505871148254191497

theorem tailTrace_3155802 : CollatzResearch.WordTrace tailWord_3155802 prefixEnd_3155802 360098505871148254191497 := by
  unfold tailWord_3155802
  simp only [CollatzResearch.WordTrace]
  refine ⟨28775388728268949229317415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76734369942050531278179773 28775388728268949229317415)
  ·
    refine ⟨43163083092403423843976123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28775388728268949229317415 43163083092403423843976123)
    ·
      refine ⟨64744624638605135765964185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43163083092403423843976123 64744624638605135765964185)
      ·
        refine ⟨48558468478953851824473139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64744624638605135765964185 48558468478953851824473139)
        ·
          refine ⟨72837702718430777736709709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48558468478953851824473139 72837702718430777736709709)
          ·
            refine ⟨27314138519411541651266141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72837702718430777736709709 27314138519411541651266141)
            ·
              refine ⟨10242801944779328119224803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27314138519411541651266141 10242801944779328119224803)
              ·
                refine ⟨15364202917168992178837205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10242801944779328119224803 15364202917168992178837205)
                ·
                  refine ⟨360098505871148254191497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15364202917168992178837205 360098505871148254191497)
                  ·
                    rfl

theorem cell22_3155802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_3155802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155802 prefixEnd_3155802 := by exact prefixLift 3155802
  have htrace : WordTrace (prefixWord ++ tailWord_3155802) baseStart_3155802 baseEnd_3155802 := by
    simpa [prefixWord, tailWord_3155802, baseEnd_3155802] using wordTrace_append hprefix tailTrace_3155802
  have hstable : (prefixWord ++ tailWord_3155802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155802).length < 2 ^ (prefixWord ++ tailWord_3155802).sum := by decide
  have hdescent : baseEnd_3155802 < baseStart_3155802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155832 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 7, 4]
def baseStart_3155832 : Nat := 118140960795 + 3155832 * 2 ^ 59
def prefixEnd_3155832 : Nat := 4983230072969 + 3 ^ 40 * 3155832 * 2
def baseEnd_3155832 : Nat := 1080305787226534684324399

theorem tailTrace_3155832 : CollatzResearch.WordTrace tailWord_3155832 prefixEnd_3155832 1080305787226534684324399 := by
  unfold tailWord_3155832
  simp only [CollatzResearch.WordTrace]
  refine ⟨57551324551483556020430875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76735099401978074693907833 57551324551483556020430875)
  ·
    refine ⟨86326986827225334030646313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57551324551483556020430875 86326986827225334030646313)
    ·
      refine ⟨64745240120419000522984735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86326986827225334030646313 64745240120419000522984735)
      ·
        refine ⟨97117860180628500784477103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64745240120419000522984735 97117860180628500784477103)
        ·
          refine ⟨145676790270942751176715655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97117860180628500784477103 145676790270942751176715655)
          ·
            refine ⟨218515185406414126765073483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145676790270942751176715655 218515185406414126765073483)
            ·
              refine ⟨327772778109621190147610225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218515185406414126765073483 327772778109621190147610225)
              ·
                refine ⟨245829583582215892610707669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327772778109621190147610225 245829583582215892610707669)
                ·
                  refine ⟨5761630865208184983063461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 245829583582215892610707669 5761630865208184983063461)
                  ·
                    refine ⟨1080305787226534684324399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5761630865208184983063461 1080305787226534684324399)
                    ·
                      rfl

theorem cell22_3155832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_3155832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155832 prefixEnd_3155832 := by exact prefixLift 3155832
  have htrace : WordTrace (prefixWord ++ tailWord_3155832) baseStart_3155832 baseEnd_3155832 := by
    simpa [prefixWord, tailWord_3155832, baseEnd_3155832] using wordTrace_append hprefix tailTrace_3155832
  have hstable : (prefixWord ++ tailWord_3155832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155832).length < 2 ^ (prefixWord ++ tailWord_3155832).sum := by decide
  have hdescent : baseEnd_3155832 < baseStart_3155832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155849 : List Nat := [1, 2, 1, 1, 5, 1, 1, 5, 1, 4]
def baseStart_3155849 : Nat := 118140960795 + 3155849 * 2 ^ 59
def prefixEnd_3155849 : Nat := 4983230072969 + 3 ^ 40 * 3155849 * 2
def baseEnd_3155849 : Nat := 1080311606673952306649347

theorem tailTrace_3155849 : CollatzResearch.WordTrace tailWord_3155849 prefixEnd_3155849 1080311606673952306649347 := by
  unfold tailWord_3155849
  simp only [CollatzResearch.WordTrace]
  refine ⟨115103269143905523944230601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76735512762603682629487067 115103269143905523944230601)
  ·
    refine ⟨86327451857929142958172951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115103269143905523944230601 86327451857929142958172951)
    ·
      refine ⟨129491177786893714437259427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86327451857929142958172951 129491177786893714437259427)
      ·
        refine ⟨194236766680340571655889141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129491177786893714437259427 194236766680340571655889141)
        ·
          refine ⟨18209696876281928592739607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194236766680340571655889141 18209696876281928592739607)
          ·
            refine ⟨27314545314422892889109411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18209696876281928592739607 27314545314422892889109411)
            ·
              refine ⟨40971817971634339333664117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27314545314422892889109411 40971817971634339333664117)
              ·
                refine ⟨3841107934840719312531011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40971817971634339333664117 3841107934840719312531011)
                ·
                  refine ⟨5761661902261078968796517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3841107934840719312531011 5761661902261078968796517)
                  ·
                    refine ⟨1080311606673952306649347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5761661902261078968796517 1080311606673952306649347)
                    ·
                      rfl

theorem cell22_3155849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_3155849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155849 prefixEnd_3155849 := by exact prefixLift 3155849
  have htrace : WordTrace (prefixWord ++ tailWord_3155849) baseStart_3155849 baseEnd_3155849 := by
    simpa [prefixWord, tailWord_3155849, baseEnd_3155849] using wordTrace_append hprefix tailTrace_3155849
  have hstable : (prefixWord ++ tailWord_3155849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155849).length < 2 ^ (prefixWord ++ tailWord_3155849).sum := by decide
  have hdescent : baseEnd_3155849 < baseStart_3155849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155877 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_3155877 : Nat := 118140960795 + 3155877 * 2 ^ 59
def prefixEnd_3155877 : Nat := 4983230072969 + 3 ^ 40 * 3155877 * 2
def baseEnd_3155877 : Nat := 1080321191646169566949261

theorem tailTrace_3155877 : CollatzResearch.WordTrace tailWord_3155877 prefixEnd_3155877 1080321191646169566949261 := by
  unfold tailWord_3155877
  simp only [CollatzResearch.WordTrace]
  refine ⟨115104290387804084726249885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76736193591869389817499923 115104290387804084726249885)
  ·
    refine ⟨43164108895426531772343707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115104290387804084726249885 43164108895426531772343707)
    ·
      refine ⟨64746163343139797658515561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43164108895426531772343707 64746163343139797658515561)
      ·
        refine ⟨48559622507354848243886671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64746163343139797658515561 48559622507354848243886671)
        ·
          refine ⟨72839433761032272365830007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48559622507354848243886671 72839433761032272365830007)
          ·
            refine ⟨109259150641548408548745011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72839433761032272365830007 109259150641548408548745011)
            ·
              refine ⟨163888725962322612823117517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109259150641548408548745011 163888725962322612823117517)
              ·
                refine ⟨61458272235870979808669069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163888725962322612823117517 61458272235870979808669069)
                ·
                  refine ⟨23046852088451617428250901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61458272235870979808669069 23046852088451617428250901)
                  ·
                    refine ⟨1080321191646169566949261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23046852088451617428250901 1080321191646169566949261)
                    ·
                      rfl

theorem cell22_3155877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_3155877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155877 prefixEnd_3155877 := by exact prefixLift 3155877
  have htrace : WordTrace (prefixWord ++ tailWord_3155877) baseStart_3155877 baseEnd_3155877 := by
    simpa [prefixWord, tailWord_3155877, baseEnd_3155877] using wordTrace_append hprefix tailTrace_3155877
  have hstable : (prefixWord ++ tailWord_3155877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155877).length < 2 ^ (prefixWord ++ tailWord_3155877).sum := by decide
  have hdescent : baseEnd_3155877 < baseStart_3155877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155900 : List Nat := [2, 2, 2, 5, 1, 1, 3, 1, 1, 4]
def baseStart_3155900 : Nat := 118140960795 + 3155900 * 2 ^ 59
def prefixEnd_3155900 : Nat := 4983230072969 + 3 ^ 40 * 3155900 * 2
def baseEnd_3155900 : Nat := 1080329065016205173624191

theorem tailTrace_3155900 : CollatzResearch.WordTrace tailWord_3155900 prefixEnd_3155900 1080329065016205173624191 := by
  unfold tailWord_3155900
  simp only [CollatzResearch.WordTrace]
  refine ⟨57552564633360379827168577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76736752844480506436224769 57552564633360379827168577)
  ·
    refine ⟨43164423475020284870376433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57552564633360379827168577 43164423475020284870376433)
    ·
      refine ⟨32373317606265213652782325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43164423475020284870376433 32373317606265213652782325)
      ·
        refine ⟨3034998525587363779948343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32373317606265213652782325 3034998525587363779948343)
        ·
          refine ⟨4552497788381045669922515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034998525587363779948343 4552497788381045669922515)
          ·
            refine ⟨6828746682571568504883773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4552497788381045669922515 6828746682571568504883773)
            ·
              refine ⟨2560780005964338189331415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6828746682571568504883773 2560780005964338189331415)
              ·
                refine ⟨3841170008946507283997123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2560780005964338189331415 3841170008946507283997123)
                ·
                  refine ⟨5761755013419760925995685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3841170008946507283997123 5761755013419760925995685)
                  ·
                    refine ⟨1080329065016205173624191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5761755013419760925995685 1080329065016205173624191)
                    ·
                      rfl

theorem cell22_3155900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_3155900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155900 prefixEnd_3155900 := by exact prefixLift 3155900
  have htrace : WordTrace (prefixWord ++ tailWord_3155900) baseStart_3155900 baseEnd_3155900 := by
    simpa [prefixWord, tailWord_3155900, baseEnd_3155900] using wordTrace_append hprefix tailTrace_3155900
  have hstable : (prefixWord ++ tailWord_3155900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155900).length < 2 ^ (prefixWord ++ tailWord_3155900).sum := by decide
  have hdescent : baseEnd_3155900 < baseStart_3155900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155969 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3155969 : Nat := 118140960795 + 3155969 * 2 ^ 59
def prefixEnd_3155969 : Nat := 4983230072969 + 3 ^ 40 * 3155969 * 2
def baseEnd_3155969 : Nat := 1080352685126311993648979

theorem tailTrace_3155969 : CollatzResearch.WordTrace tailWord_3155969 prefixEnd_3155969 1080352685126311993648979 := by
  unfold tailWord_3155969
  simp only [CollatzResearch.WordTrace]
  refine ⟨115107645903470784438598961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76738430602313856292399307 115107645903470784438598961)
  ·
    refine ⟨86330734427603088328949221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115107645903470784438598961 86330734427603088328949221)
    ·
      refine ⟨16187012705175579061677979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86330734427603088328949221 16187012705175579061677979)
      ·
        refine ⟨24280519057763368592516969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16187012705175579061677979 24280519057763368592516969)
        ·
          refine ⟨18210389293322526444387727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24280519057763368592516969 18210389293322526444387727)
          ·
            refine ⟨27315583939983789666581591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18210389293322526444387727 27315583939983789666581591)
            ·
              refine ⟨40973375909975684499872387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27315583939983789666581591 40973375909975684499872387)
              ·
                refine ⟨61460063864963526749808581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40973375909975684499872387 61460063864963526749808581)
                ·
                  refine ⟨11523761974680661265589109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61460063864963526749808581 11523761974680661265589109)
                  ·
                    refine ⟨1080352685126311993648979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11523761974680661265589109 1080352685126311993648979)
                    ·
                      rfl

theorem cell22_3155969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3155969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155969 prefixEnd_3155969 := by exact prefixLift 3155969
  have htrace : WordTrace (prefixWord ++ tailWord_3155969) baseStart_3155969 baseEnd_3155969 := by
    simpa [prefixWord, tailWord_3155969, baseEnd_3155969] using wordTrace_append hprefix tailTrace_3155969
  have hstable : (prefixWord ++ tailWord_3155969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155969).length < 2 ^ (prefixWord ++ tailWord_3155969).sum := by decide
  have hdescent : baseEnd_3155969 < baseStart_3155969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3155999 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 6]
def baseStart_3155999 : Nat := 118140960795 + 3155999 * 2 ^ 59
def prefixEnd_3155999 : Nat := 4983230072969 + 3 ^ 40 * 3155999 * 2
def baseEnd_3155999 : Nat := 360120984913133971799629

theorem tailTrace_3155999 : CollatzResearch.WordTrace tailWord_3155999 prefixEnd_3155999 360120984913133971799629 := by
  unfold tailWord_3155999
  simp only [CollatzResearch.WordTrace]
  refine ⟨115108740093362099562191051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76739160062241399708127367 115108740093362099562191051)
  ·
    refine ⟨172663110140043149343286577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115108740093362099562191051 172663110140043149343286577)
    ·
      refine ⟨129497332605032362007464933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172663110140043149343286577 129497332605032362007464933)
      ·
        refine ⟨24280749863443567876399675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129497332605032362007464933 24280749863443567876399675)
        ·
          refine ⟨36421124795165351814599513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24280749863443567876399675 36421124795165351814599513)
          ·
            refine ⟨27315843596374013860949635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36421124795165351814599513 27315843596374013860949635)
            ·
              refine ⟨40973765394561020791424453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27315843596374013860949635 40973765394561020791424453)
              ·
                refine ⟨7682581011480191398392085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40973765394561020791424453 7682581011480191398392085)
                ·
                  refine ⟨360120984913133971799629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7682581011480191398392085 360120984913133971799629)
                  ·
                    rfl

theorem cell22_3155999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 6].length) (baseStart_3155999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3155999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3155999 prefixEnd_3155999 := by exact prefixLift 3155999
  have htrace : WordTrace (prefixWord ++ tailWord_3155999) baseStart_3155999 baseEnd_3155999 := by
    simpa [prefixWord, tailWord_3155999, baseEnd_3155999] using wordTrace_append hprefix tailTrace_3155999
  have hstable : (prefixWord ++ tailWord_3155999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3155999).length < 2 ^ (prefixWord ++ tailWord_3155999).sum := by decide
  have hdescent : baseEnd_3155999 < baseStart_3155999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3155999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156031 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 4, 3]
def baseStart_3156031 : Nat := 118140960795 + 3156031 * 2 ^ 59
def prefixEnd_3156031 : Nat := 4983230072969 + 3 ^ 40 * 3156031 * 2
def baseEnd_3156031 : Nat := 1080373908993364498598789

theorem tailTrace_3156031 : CollatzResearch.WordTrace tailWord_3156031 prefixEnd_3156031 1080373908993364498598789 := by
  unfold tailWord_3156031
  simp only [CollatzResearch.WordTrace]
  refine ⟨115109907229246169027355947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76739938152830779351570631 115109907229246169027355947)
  ·
    refine ⟨172664860843869253541033921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115109907229246169027355947 172664860843869253541033921)
    ·
      refine ⟨129498645632901940155775441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172664860843869253541033921 129498645632901940155775441)
      ·
        refine ⟨97123984224676455116831581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129498645632901940155775441 97123984224676455116831581)
        ·
          refine ⟨36421494084253670668811843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97123984224676455116831581 36421494084253670668811843)
          ·
            refine ⟨54632241126380506003217765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36421494084253670668811843 54632241126380506003217765)
            ·
              refine ⟨10243545211196344875603331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54632241126380506003217765 10243545211196344875603331)
              ·
                refine ⟨15365317816794517313404997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10243545211196344875603331 15365317816794517313404997)
                ·
                  refine ⟨2880997090648971996263437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15365317816794517313404997 2880997090648971996263437)
                  ·
                    refine ⟨1080373908993364498598789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2880997090648971996263437 1080373908993364498598789)
                    ·
                      rfl

theorem cell22_3156031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 3].length) (baseStart_3156031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156031 prefixEnd_3156031 := by exact prefixLift 3156031
  have htrace : WordTrace (prefixWord ++ tailWord_3156031) baseStart_3156031 baseEnd_3156031 := by
    simpa [prefixWord, tailWord_3156031, baseEnd_3156031] using wordTrace_append hprefix tailTrace_3156031
  have hstable : (prefixWord ++ tailWord_3156031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156031).length < 2 ^ (prefixWord ++ tailWord_3156031).sum := by decide
  have hdescent : baseEnd_3156031 < baseStart_3156031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156033 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 6]
def baseStart_3156033 : Nat := 118140960795 + 3156033 * 2 ^ 59
def prefixEnd_3156033 : Nat := 4983230072969 + 3 ^ 40 * 3156033 * 2
def baseEnd_3156033 : Nat := 360124864544745720016261

theorem tailTrace_3156033 : CollatzResearch.WordTrace tailWord_3156033 prefixEnd_3156033 360124864544745720016261 := by
  unfold tailWord_3156033
  simp only [CollatzResearch.WordTrace]
  refine ⟨115109980175238923368928753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76739986783492615579285835 115109980175238923368928753)
  ·
    refine ⟨86332485131429192526696565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115109980175238923368928753 86332485131429192526696565)
    ·
      refine ⟨8093670481071486799377803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86332485131429192526696565 8093670481071486799377803)
      ·
        refine ⟨12140505721607230199066705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8093670481071486799377803 12140505721607230199066705)
        ·
          refine ⟨9105379291205422649300029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12140505721607230199066705 9105379291205422649300029)
          ·
            refine ⟨3414517234202033493487511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9105379291205422649300029 3414517234202033493487511)
            ·
              refine ⟨5121775851303050240231267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3414517234202033493487511 5121775851303050240231267)
              ·
                refine ⟨7682663776954575360346901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121775851303050240231267 7682663776954575360346901)
                ·
                  refine ⟨360124864544745720016261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7682663776954575360346901 360124864544745720016261)
                  ·
                    rfl

theorem cell22_3156033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 6].length) (baseStart_3156033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156033 prefixEnd_3156033 := by exact prefixLift 3156033
  have htrace : WordTrace (prefixWord ++ tailWord_3156033) baseStart_3156033 baseEnd_3156033 := by
    simpa [prefixWord, tailWord_3156033, baseEnd_3156033] using wordTrace_append hprefix tailTrace_3156033
  have hstable : (prefixWord ++ tailWord_3156033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156033).length < 2 ^ (prefixWord ++ tailWord_3156033).sum := by decide
  have hdescent : baseEnd_3156033 < baseStart_3156033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156044 : List Nat := [2, 2, 1, 3, 1, 1, 3, 9]
def baseStart_3156044 : Nat := 118140960795 + 3156044 * 2 ^ 59
def prefixEnd_3156044 : Nat := 4983230072969 + 3 ^ 40 * 3156044 * 2
def baseEnd_3156044 : Nat := 120042039906559644224861

theorem tailTrace_3156044 : CollatzResearch.WordTrace tailWord_3156044 prefixEnd_3156044 120042039906559644224861 := by
  unfold tailWord_3156044
  simp only [CollatzResearch.WordTrace]
  refine ⟨57555190689099536123789593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76740254252132714831719457 57555190689099536123789593)
  ·
    refine ⟨43166393016824652092842195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57555190689099536123789593 43166393016824652092842195)
    ·
      refine ⟨64749589525236978139263293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43166393016824652092842195 64749589525236978139263293)
      ·
        refine ⟨24281096071963866802223735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64749589525236978139263293 24281096071963866802223735)
        ·
          refine ⟨36421644107945800203335603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24281096071963866802223735 36421644107945800203335603)
          ·
            refine ⟨54632466161918700305003405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36421644107945800203335603 54632466161918700305003405)
            ·
              refine ⟨20487174810719512614376277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54632466161918700305003405 20487174810719512614376277)
              ·
                refine ⟨120042039906559644224861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20487174810719512614376277 120042039906559644224861)
                ·
                  rfl

theorem cell22_3156044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 9].length) (baseStart_3156044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156044 prefixEnd_3156044 := by exact prefixLift 3156044
  have htrace : WordTrace (prefixWord ++ tailWord_3156044) baseStart_3156044 baseEnd_3156044 := by
    simpa [prefixWord, tailWord_3156044, baseEnd_3156044] using wordTrace_append hprefix tailTrace_3156044
  have hstable : (prefixWord ++ tailWord_3156044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156044).length < 2 ^ (prefixWord ++ tailWord_3156044).sum := by decide
  have hdescent : baseEnd_3156044 < baseStart_3156044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156110 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_3156110 : Nat := 118140960795 + 3156110 * 2 ^ 59
def prefixEnd_3156110 : Nat := 4983230072969 + 3 ^ 40 * 3156110 * 2
def baseEnd_3156110 : Nat := 1080400952307834625873547

theorem tailTrace_3156110 : CollatzResearch.WordTrace tailWord_3156110 prefixEnd_3156110 1080400952307834625873547 := by
  unfold tailWord_3156110
  simp only [CollatzResearch.WordTrace]
  refine ⟨14389098574494995689935223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76741859063973310346321189 14389098574494995689935223)
  ·
    refine ⟨21583647861742493534902835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14389098574494995689935223 21583647861742493534902835)
    ·
      refine ⟨32375471792613740302354253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21583647861742493534902835 32375471792613740302354253)
      ·
        refine ⟨12140801922230152613382845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32375471792613740302354253 12140801922230152613382845)
        ·
          refine ⟨4552800720836307230018567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12140801922230152613382845 4552800720836307230018567)
          ·
            refine ⟨6829201081254460845027851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4552800720836307230018567 6829201081254460845027851)
            ·
              refine ⟨10243801621881691267541777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6829201081254460845027851 10243801621881691267541777)
              ·
                refine ⟨7682851216411268450656333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10243801621881691267541777 7682851216411268450656333)
                ·
                  refine ⟨2881069206154225668996125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7682851216411268450656333 2881069206154225668996125)
                  ·
                    refine ⟨1080400952307834625873547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2881069206154225668996125 1080400952307834625873547)
                    ·
                      rfl

theorem cell22_3156110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_3156110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156110 prefixEnd_3156110 := by exact prefixLift 3156110
  have htrace : WordTrace (prefixWord ++ tailWord_3156110) baseStart_3156110 baseEnd_3156110 := by
    simpa [prefixWord, tailWord_3156110, baseEnd_3156110] using wordTrace_append hprefix tailTrace_3156110
  have hstable : (prefixWord ++ tailWord_3156110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156110).length < 2 ^ (prefixWord ++ tailWord_3156110).sum := by decide
  have hdescent : baseEnd_3156110 < baseStart_3156110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156127 : List Nat := [1, 1, 2, 6, 1, 2, 2, 3, 1, 3]
def baseStart_3156127 : Nat := 118140960795 + 3156127 * 2 ^ 59
def prefixEnd_3156127 : Nat := 4983230072969 + 3 ^ 40 * 3156127 * 2
def baseEnd_3156127 : Nat := 1080406771755252248198495

theorem tailTrace_3156127 : CollatzResearch.WordTrace tailWord_3156127 prefixEnd_3156127 1080406771755252248198495 := by
  unfold tailWord_3156127
  simp only [CollatzResearch.WordTrace]
  refine ⟨115113408636898377422850635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76742272424598918281900423 115113408636898377422850635)
  ·
    refine ⟨172670112955347566134275953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115113408636898377422850635 172670112955347566134275953)
    ·
      refine ⟨129502584716510674600706965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172670112955347566134275953 129502584716510674600706965)
      ·
        refine ⟨6070433658586437871908139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 129502584716510674600706965 6070433658586437871908139)
        ·
          refine ⟨9105650487879656807862209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6070433658586437871908139 9105650487879656807862209)
          ·
            refine ⟨6829237865909742605896657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9105650487879656807862209 6829237865909742605896657)
            ·
              refine ⟨5121928399432306954422493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6829237865909742605896657 5121928399432306954422493)
              ·
                refine ⟨1920723149787115107908435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5121928399432306954422493 1920723149787115107908435)
                ·
                  refine ⟨2881084724680672661862653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920723149787115107908435 2881084724680672661862653)
                  ·
                    refine ⟨1080406771755252248198495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2881084724680672661862653 1080406771755252248198495)
                    ·
                      rfl

theorem cell22_3156127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 1, 3].length) (baseStart_3156127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156127 prefixEnd_3156127 := by exact prefixLift 3156127
  have htrace : WordTrace (prefixWord ++ tailWord_3156127) baseStart_3156127 baseEnd_3156127 := by
    simpa [prefixWord, tailWord_3156127, baseEnd_3156127] using wordTrace_append hprefix tailTrace_3156127
  have hstable : (prefixWord ++ tailWord_3156127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156127).length < 2 ^ (prefixWord ++ tailWord_3156127).sum := by decide
  have hdescent : baseEnd_3156127 < baseStart_3156127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156151 : List Nat := [1, 1, 3, 1, 4, 2, 1, 3, 6]
def baseStart_3156151 : Nat := 118140960795 + 3156151 * 2 ^ 59
def prefixEnd_3156151 : Nat := 4983230072969 + 3 ^ 40 * 3156151 * 2
def baseEnd_3156151 : Nat := 360138329148574728532807

theorem tailTrace_3156151 : CollatzResearch.WordTrace tailWord_3156151 prefixEnd_3156151 360138329148574728532807 := by
  unfold tailWord_3156151
  simp only [CollatzResearch.WordTrace]
  refine ⟨115114283988811429521724307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76742855992540953014482871 115114283988811429521724307)
  ·
    refine ⟨172671425983217144282586461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115114283988811429521724307 172671425983217144282586461)
    ·
      refine ⟨64751784743706429105969923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172671425983217144282586461 64751784743706429105969923)
      ·
        refine ⟨97127677115559643658954885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64751784743706429105969923 97127677115559643658954885)
        ·
          refine ⟨18211439459167433186054041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97127677115559643658954885 18211439459167433186054041)
          ·
            refine ⟨13658579594375574889540531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18211439459167433186054041 13658579594375574889540531)
            ·
              refine ⟨20487869391563362334310797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13658579594375574889540531 20487869391563362334310797)
              ·
                refine ⟨7682951021836260875366549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20487869391563362334310797 7682951021836260875366549)
                ·
                  refine ⟨360138329148574728532807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7682951021836260875366549 360138329148574728532807)
                  ·
                    rfl

theorem cell22_3156151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3, 6].length) (baseStart_3156151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156151 prefixEnd_3156151 := by exact prefixLift 3156151
  have htrace : WordTrace (prefixWord ++ tailWord_3156151) baseStart_3156151 baseEnd_3156151 := by
    simpa [prefixWord, tailWord_3156151, baseEnd_3156151] using wordTrace_append hprefix tailTrace_3156151
  have hstable : (prefixWord ++ tailWord_3156151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156151).length < 2 ^ (prefixWord ++ tailWord_3156151).sum := by decide
  have hdescent : baseEnd_3156151 < baseStart_3156151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156305 : List Nat := [1, 2, 2, 1, 4, 3, 1, 3, 1, 4]
def baseStart_3156305 : Nat := 118140960795 + 3156305 * 2 ^ 59
def prefixEnd_3156305 : Nat := 4983230072969 + 3 ^ 40 * 3156305 * 2
def baseEnd_3156305 : Nat := 1080467704792919117247949

theorem tailTrace_3156305 : CollatzResearch.WordTrace tailWord_3156305 prefixEnd_3156305 1080467704792919117247949 := by
  unfold tailWord_3156305
  simp only [CollatzResearch.WordTrace]
  refine ⟨115119900830253513822830369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76746600553502342548553579 115119900830253513822830369)
  ·
    refine ⟨86339925622690135367122777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115119900830253513822830369 86339925622690135367122777)
    ·
      refine ⟨64754944217017601525342083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86339925622690135367122777 64754944217017601525342083)
      ·
        refine ⟨97132416325526402288013125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64754944217017601525342083 97132416325526402288013125)
        ·
          refine ⟨18212328061036200429002461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97132416325526402288013125 18212328061036200429002461)
          ·
            refine ⟨6829623022888575160875923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18212328061036200429002461 6829623022888575160875923)
            ·
              refine ⟨10244434534332862741313885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6829623022888575160875923 10244434534332862741313885)
              ·
                refine ⟨3841662950374823527992707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10244434534332862741313885 3841662950374823527992707)
                ·
                  refine ⟨5762494425562235291989061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3841662950374823527992707 5762494425562235291989061)
                  ·
                    refine ⟨1080467704792919117247949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5762494425562235291989061 1080467704792919117247949)
                    ·
                      rfl

theorem cell22_3156305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_3156305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156305 prefixEnd_3156305 := by exact prefixLift 3156305
  have htrace : WordTrace (prefixWord ++ tailWord_3156305) baseStart_3156305 baseEnd_3156305 := by
    simpa [prefixWord, tailWord_3156305, baseEnd_3156305] using wordTrace_append hprefix tailTrace_3156305
  have hstable : (prefixWord ++ tailWord_3156305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156305).length < 2 ^ (prefixWord ++ tailWord_3156305).sum := by decide
  have hdescent : baseEnd_3156305 < baseStart_3156305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156320 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 6]
def baseStart_3156320 : Nat := 118140960795 + 3156320 * 2 ^ 59
def prefixEnd_3156320 : Nat := 4983230072969 + 3 ^ 40 * 3156320 * 2
def baseEnd_3156320 : Nat := 360157613199821359374301

theorem tailTrace_3156320 : CollatzResearch.WordTrace tailWord_3156320 prefixEnd_3156320 360157613199821359374301 := by
  unfold tailWord_3156320
  simp only [CollatzResearch.WordTrace]
  refine ⟨57560223962599585692313207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76746965283466114256417609 57560223962599585692313207)
  ·
    refine ⟨86340335943899378538469811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57560223962599585692313207 86340335943899378538469811)
    ·
      refine ⟨129510503915849067807704717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86340335943899378538469811 129510503915849067807704717)
      ·
        refine ⟨48566438968443400427889269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129510503915849067807704717 48566438968443400427889269)
        ·
          refine ⟨4553103653291568790114619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48566438968443400427889269 4553103653291568790114619)
          ·
            refine ⟨6829655479937353185171929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4553103653291568790114619 6829655479937353185171929)
            ·
              refine ⟨5122241609953014888878947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6829655479937353185171929 5122241609953014888878947)
              ·
                refine ⟨7683362414929522333318421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5122241609953014888878947 7683362414929522333318421)
                ·
                  refine ⟨360157613199821359374301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7683362414929522333318421 360157613199821359374301)
                  ·
                    rfl

theorem cell22_3156320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 6].length) (baseStart_3156320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156320 prefixEnd_3156320 := by exact prefixLift 3156320
  have htrace : WordTrace (prefixWord ++ tailWord_3156320) baseStart_3156320 baseEnd_3156320 := by
    simpa [prefixWord, tailWord_3156320, baseEnd_3156320] using wordTrace_append hprefix tailTrace_3156320
  have hstable : (prefixWord ++ tailWord_3156320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156320).length < 2 ^ (prefixWord ++ tailWord_3156320).sum := by decide
  have hdescent : baseEnd_3156320 < baseStart_3156320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156333 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_3156333 : Nat := 118140960795 + 3156333 * 2 ^ 59
def prefixEnd_3156333 : Nat := 4983230072969 + 3 ^ 40 * 3156333 * 2
def baseEnd_3156333 : Nat := 1080477289765136377547863

theorem tailTrace_3156333 : CollatzResearch.WordTrace tailWord_3156333 prefixEnd_3156333 1080477289765136377547863 := by
  unfold tailWord_3156333
  simp only [CollatzResearch.WordTrace]
  refine ⟨115120922074152074604849653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76747281382768049736566435 115120922074152074604849653)
  ·
    refine ⟨10792586444451756994204655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115120922074152074604849653 10792586444451756994204655)
    ·
      refine ⟨16188879666677635491306983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10792586444451756994204655 16188879666677635491306983)
      ·
        refine ⟨24283319500016453236960475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16188879666677635491306983 24283319500016453236960475)
        ·
          refine ⟨36424979250024679855440713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24283319500016453236960475 36424979250024679855440713)
          ·
            refine ⟨27318734437518509891580535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36424979250024679855440713 27318734437518509891580535)
            ·
              refine ⟨40978101656277764837370803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27318734437518509891580535 40978101656277764837370803)
              ·
                refine ⟨61467152484416647256056205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40978101656277764837370803 61467152484416647256056205)
                ·
                  refine ⟨23050182181656242721021077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61467152484416647256056205 23050182181656242721021077)
                  ·
                    refine ⟨1080477289765136377547863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23050182181656242721021077 1080477289765136377547863)
                    ·
                      rfl

theorem cell22_3156333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_3156333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156333 prefixEnd_3156333 := by exact prefixLift 3156333
  have htrace : WordTrace (prefixWord ++ tailWord_3156333) baseStart_3156333 baseEnd_3156333 := by
    simpa [prefixWord, tailWord_3156333, baseEnd_3156333] using wordTrace_append hprefix tailTrace_3156333
  have hstable : (prefixWord ++ tailWord_3156333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156333).length < 2 ^ (prefixWord ++ tailWord_3156333).sum := by decide
  have hdescent : baseEnd_3156333 < baseStart_3156333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156382 : List Nat := [4, 3, 1, 2, 1, 2, 2, 7]
def baseStart_3156382 : Nat := 118140960795 + 3156382 * 2 ^ 59
def prefixEnd_3156382 : Nat := 4983230072969 + 3 ^ 40 * 3156382 * 2
def baseEnd_3156382 : Nat := 120054895940724064785857

theorem tailTrace_3156382 : CollatzResearch.WordTrace tailWord_3156382 prefixEnd_3156382 120054895940724064785857 := by
  unfold tailWord_3156382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14390338656371819496672925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76748472833983037315588933 14390338656371819496672925)
  ·
    refine ⟨5396376996139432311252347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14390338656371819496672925 5396376996139432311252347)
    ·
      refine ⟨8094565494209148466878521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5396376996139432311252347 8094565494209148466878521)
      ·
        refine ⟨6070924120656861350158891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8094565494209148466878521 6070924120656861350158891)
        ·
          refine ⟨9106386180985292025238337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6070924120656861350158891 9106386180985292025238337)
          ·
            refine ⟨6829789635738969018928753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9106386180985292025238337 6829789635738969018928753)
            ·
              refine ⟨5122342226804226764196565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6829789635738969018928753 5122342226804226764196565)
              ·
                refine ⟨120054895940724064785857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5122342226804226764196565 120054895940724064785857)
                ·
                  rfl

theorem cell22_3156382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_3156382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156382 prefixEnd_3156382 := by exact prefixLift 3156382
  have htrace : WordTrace (prefixWord ++ tailWord_3156382) baseStart_3156382 baseEnd_3156382 := by
    simpa [prefixWord, tailWord_3156382, baseEnd_3156382] using wordTrace_append hprefix tailTrace_3156382
  have hstable : (prefixWord ++ tailWord_3156382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156382).length < 2 ^ (prefixWord ++ tailWord_3156382).sum := by decide
  have hdescent : baseEnd_3156382 < baseStart_3156382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156408 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 4, 5]
def baseStart_3156408 : Nat := 118140960795 + 3156408 * 2 ^ 59
def prefixEnd_3156408 : Nat := 4983230072969 + 3 ^ 40 * 3156408 * 2
def baseEnd_3156408 : Nat := 1080502963797861181922633

theorem tailTrace_3156408 : CollatzResearch.WordTrace tailWord_3156408 prefixEnd_3156408 1080502963797861181922633 := by
  unfold tailWord_3156408
  simp only [CollatzResearch.WordTrace]
  refine ⟨57561828774440181206914939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76749105032586908275886585 57561828774440181206914939)
  ·
    refine ⟨86342743161660271810372409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57561828774440181206914939 86342743161660271810372409)
    ·
      refine ⟨64757057371245203857779307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86342743161660271810372409 64757057371245203857779307)
      ·
        refine ⟨97135586056867805786668961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64757057371245203857779307 97135586056867805786668961)
        ·
          refine ⟨72851689542650854340001721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97135586056867805786668961 72851689542650854340001721)
          ·
            refine ⟨54638767156988140755001291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72851689542650854340001721 54638767156988140755001291)
            ·
              refine ⟨81958150735482211132501937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54638767156988140755001291 81958150735482211132501937)
              ·
                refine ⟨61468613051611658349376453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81958150735482211132501937 61468613051611658349376453)
                ·
                  refine ⟨11525364947177185940508085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61468613051611658349376453 11525364947177185940508085)
                  ·
                    refine ⟨1080502963797861181922633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11525364947177185940508085 1080502963797861181922633)
                    ·
                      rfl

theorem cell22_3156408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_3156408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156408 prefixEnd_3156408 := by exact prefixLift 3156408
  have htrace : WordTrace (prefixWord ++ tailWord_3156408) baseStart_3156408 baseEnd_3156408 := by
    simpa [prefixWord, tailWord_3156408, baseEnd_3156408] using wordTrace_append hprefix tailTrace_3156408
  have hstable : (prefixWord ++ tailWord_3156408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156408).length < 2 ^ (prefixWord ++ tailWord_3156408).sum := by decide
  have hdescent : baseEnd_3156408 < baseStart_3156408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156455 : List Nat := [1, 1, 5, 2, 1, 1, 3, 2, 6]
def baseStart_3156455 : Nat := 118140960795 + 3156455 * 2 ^ 59
def prefixEnd_3156455 : Nat := 4983230072969 + 3 ^ 40 * 3156455 * 2
def baseEnd_3156455 : Nat := 360173017619456241999163

theorem tailTrace_3156455 : CollatzResearch.WordTrace tailWord_3156455 prefixEnd_3156455 360173017619456241999163 := by
  unfold tailWord_3156455
  simp only [CollatzResearch.WordTrace]
  refine ⟨115125371779710089440790819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76750247853140059627193879 115125371779710089440790819)
  ·
    refine ⟨172688057669565134161186229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115125371779710089440790819 172688057669565134161186229)
    ·
      refine ⟨16189505406521731327611209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172688057669565134161186229 16189505406521731327611209)
      ·
        refine ⟨12142129054891298495708407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16189505406521731327611209 12142129054891298495708407)
        ·
          refine ⟨18213193582336947743562611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12142129054891298495708407 18213193582336947743562611)
          ·
            refine ⟨27319790373505421615343917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18213193582336947743562611 27319790373505421615343917)
            ·
              refine ⟨10244921390064533105753969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27319790373505421615343917 10244921390064533105753969)
              ·
                refine ⟨7683691042548399829315477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10244921390064533105753969 7683691042548399829315477)
                ·
                  refine ⟨360173017619456241999163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7683691042548399829315477 360173017619456241999163)
                  ·
                    rfl

theorem cell22_3156455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 6].length) (baseStart_3156455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156455 prefixEnd_3156455 := by exact prefixLift 3156455
  have htrace : WordTrace (prefixWord ++ tailWord_3156455) baseStart_3156455 baseEnd_3156455 := by
    simpa [prefixWord, tailWord_3156455, baseEnd_3156455] using wordTrace_append hprefix tailTrace_3156455
  have hstable : (prefixWord ++ tailWord_3156455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156455).length < 2 ^ (prefixWord ++ tailWord_3156455).sum := by decide
  have hdescent : baseEnd_3156455 < baseStart_3156455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156472 : List Nat := [2, 1, 2, 1, 1, 4, 4, 3, 4]
def baseStart_3156472 : Nat := 118140960795 + 3156472 * 2 ^ 59
def prefixEnd_3156472 : Nat := 4983230072969 + 3 ^ 40 * 3156472 * 2
def baseEnd_3156472 : Nat := 360174957435262116107479

theorem tailTrace_3156472 : CollatzResearch.WordTrace tailWord_3156472 prefixEnd_3156472 360174957435262116107479 := by
  unfold tailWord_3156472
  simp only [CollatzResearch.WordTrace]
  refine ⟨57562995910324250672079835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76750661213765667562773113 57562995910324250672079835)
  ·
    refine ⟨86344493865486376008119753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57562995910324250672079835 86344493865486376008119753)
    ·
      refine ⟨64758370399114782006089815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86344493865486376008119753 64758370399114782006089815)
      ·
        refine ⟨97137555598672173009134723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64758370399114782006089815 97137555598672173009134723)
        ·
          refine ⟨145706333398008259513702085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97137555598672173009134723 145706333398008259513702085)
          ·
            refine ⟨27319937512126548658819141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145706333398008259513702085 27319937512126548658819141)
            ·
              refine ⟨5122488283523727873528589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27319937512126548658819141 5122488283523727873528589)
              ·
                refine ⟨1920933106321397952573221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5122488283523727873528589 1920933106321397952573221)
                ·
                  refine ⟨360174957435262116107479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1920933106321397952573221 360174957435262116107479)
                  ·
                    rfl

theorem cell22_3156472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 3, 4].length) (baseStart_3156472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156472 prefixEnd_3156472 := by exact prefixLift 3156472
  have htrace : WordTrace (prefixWord ++ tailWord_3156472) baseStart_3156472 baseEnd_3156472 := by
    simpa [prefixWord, tailWord_3156472, baseEnd_3156472] using wordTrace_append hprefix tailTrace_3156472
  have hstable : (prefixWord ++ tailWord_3156472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156472).length < 2 ^ (prefixWord ++ tailWord_3156472).sum := by decide
  have hdescent : baseEnd_3156472 < baseStart_3156472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156483 : List Nat := [1, 1, 1, 3, 2, 1, 13]
def baseStart_3156483 : Nat := 118140960795 + 3156483 * 2 ^ 59
def prefixEnd_3156483 : Nat := 4983230072969 + 3 ^ 40 * 3156483 * 2
def baseEnd_3156483 : Nat := 40019579178910592085089

theorem tailTrace_3156483 : CollatzResearch.WordTrace tailWord_3156483 prefixEnd_3156483 40019579178910592085089 := by
  unfold tailWord_3156483
  simp only [CollatzResearch.WordTrace]
  refine ⟨115126393023608650222810103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76750928682405766815206735 115126393023608650222810103)
  ·
    refine ⟨172689589535412975334215155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115126393023608650222810103 172689589535412975334215155)
    ·
      refine ⟨259034384303119463001322733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172689589535412975334215155 259034384303119463001322733)
      ·
        refine ⟨97137894113669798625496025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259034384303119463001322733 97137894113669798625496025)
        ·
          refine ⟨72853420585252348969122019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97137894113669798625496025 72853420585252348969122019)
          ·
            refine ⟨109280130877878523453683029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72853420585252348969122019 109280130877878523453683029)
            ·
              refine ⟨40019579178910592085089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 109280130877878523453683029 40019579178910592085089)
              ·
                rfl

theorem cell22_3156483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 13].length) (baseStart_3156483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156483 prefixEnd_3156483 := by exact prefixLift 3156483
  have htrace : WordTrace (prefixWord ++ tailWord_3156483) baseStart_3156483 baseEnd_3156483 := by
    simpa [prefixWord, tailWord_3156483, baseEnd_3156483] using wordTrace_append hprefix tailTrace_3156483
  have hstable : (prefixWord ++ tailWord_3156483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156483).length < 2 ^ (prefixWord ++ tailWord_3156483).sum := by decide
  have hdescent : baseEnd_3156483 < baseStart_3156483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156485 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_3156485 : Nat := 118140960795 + 3156485 * 2 ^ 59
def prefixEnd_3156485 : Nat := 4983230072969 + 3 ^ 40 * 3156485 * 2
def baseEnd_3156485 : Nat := 1080529322471458647747397

theorem tailTrace_3156485 : CollatzResearch.WordTrace tailWord_3156485 prefixEnd_3156485 1080529322471458647747397 := by
  unfold tailWord_3156485
  simp only [CollatzResearch.WordTrace]
  refine ⟨115126465969601404564382909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76750977313067603042921939 115126465969601404564382909)
  ·
    refine ⟨43172424738600526711643591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115126465969601404564382909 43172424738600526711643591)
    ·
      refine ⟨64758637107900790067465387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43172424738600526711643591 64758637107900790067465387)
      ·
        refine ⟨97137955661851185101198081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64758637107900790067465387 97137955661851185101198081)
        ·
          refine ⟨72853466746388388825898561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97137955661851185101198081 72853466746388388825898561)
          ·
            refine ⟨54640100059791291619423921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72853466746388388825898561 54640100059791291619423921)
            ·
              refine ⟨40980075044843468714567941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54640100059791291619423921 40980075044843468714567941)
              ·
                refine ⟨7683764070908150383981489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40980075044843468714567941 7683764070908150383981489)
                ·
                  refine ⟨5762823053181112787986117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7683764070908150383981489 5762823053181112787986117)
                  ·
                    refine ⟨1080529322471458647747397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5762823053181112787986117 1080529322471458647747397)
                    ·
                      rfl

theorem cell22_3156485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_3156485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156485 prefixEnd_3156485 := by exact prefixLift 3156485
  have htrace : WordTrace (prefixWord ++ tailWord_3156485) baseStart_3156485 baseEnd_3156485 := by
    simpa [prefixWord, tailWord_3156485, baseEnd_3156485] using wordTrace_append hprefix tailTrace_3156485
  have hstable : (prefixWord ++ tailWord_3156485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156485).length < 2 ^ (prefixWord ++ tailWord_3156485).sum := by decide
  have hdescent : baseEnd_3156485 < baseStart_3156485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156549 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 3, 3]
def baseStart_3156549 : Nat := 118140960795 + 3156549 * 2 ^ 59
def prefixEnd_3156549 : Nat := 4983230072969 + 3 ^ 40 * 3156549 * 2
def baseEnd_3156549 : Nat := 1080551230979383814147201

theorem tailTrace_3156549 : CollatzResearch.WordTrace tailWord_3156549 prefixEnd_3156549 1080551230979383814147201 := by
  unfold tailWord_3156549
  simp only [CollatzResearch.WordTrace]
  refine ⟨115128800241369543494712701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76752533494246362329808467 115128800241369543494712701)
  ·
    refine ⟨43173300090513578810517263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115128800241369543494712701 43173300090513578810517263)
    ·
      refine ⟨64759950135770368215775895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43173300090513578810517263 64759950135770368215775895)
      ·
        refine ⟨97139925203655552323663843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64759950135770368215775895 97139925203655552323663843)
        ·
          refine ⟨145709887805483328485495765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97139925203655552323663843 145709887805483328485495765)
          ·
            refine ⟨3415075495441015511378807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 145709887805483328485495765 3415075495441015511378807)
            ·
              refine ⟨5122613243161523267068211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3415075495441015511378807 5122613243161523267068211)
              ·
                refine ⟨7683919864742284900602317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5122613243161523267068211 7683919864742284900602317)
                ·
                  refine ⟨2881469949278356837725869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7683919864742284900602317 2881469949278356837725869)
                  ·
                    refine ⟨1080551230979383814147201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2881469949278356837725869 1080551230979383814147201)
                    ·
                      rfl

theorem cell22_3156549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_3156549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156549 prefixEnd_3156549 := by exact prefixLift 3156549
  have htrace : WordTrace (prefixWord ++ tailWord_3156549) baseStart_3156549 baseEnd_3156549 := by
    simpa [prefixWord, tailWord_3156549, baseEnd_3156549] using wordTrace_append hprefix tailTrace_3156549
  have hstable : (prefixWord ++ tailWord_3156549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156549).length < 2 ^ (prefixWord ++ tailWord_3156549).sum := by decide
  have hdescent : baseEnd_3156549 < baseStart_3156549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156562 : List Nat := [3, 2, 2, 1, 2, 1, 3, 3, 5]
def baseStart_3156562 : Nat := 118140960795 + 3156562 * 2 ^ 59
def prefixEnd_3156562 : Nat := 4983230072969 + 3 ^ 40 * 3156562 * 2
def baseEnd_3156562 : Nat := 360185227048352037857387

theorem tailTrace_3156562 : CollatzResearch.WordTrace tailWord_3156562 prefixEnd_3156562 360185227048352037857387 := by
  unfold tailWord_3156562
  simp only [CollatzResearch.WordTrace]
  refine ⟨28782318597580611678733985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76752849593548297809957293 28782318597580611678733985)
  ·
    refine ⟨21586738948185458759050489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28782318597580611678733985 21586738948185458759050489)
    ·
      refine ⟨16190054211139094069287867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21586738948185458759050489 16190054211139094069287867)
      ·
        refine ⟨24285081316708641103931801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16190054211139094069287867 24285081316708641103931801)
        ·
          refine ⟨18213810987531480827948851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24285081316708641103931801 18213810987531480827948851)
          ·
            refine ⟨27320716481297221241923277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18213810987531480827948851 27320716481297221241923277)
            ·
              refine ⟨10245268680486457965721229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27320716481297221241923277 10245268680486457965721229)
              ·
                refine ⟨3841975755182421737145461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10245268680486457965721229 3841975755182421737145461)
                ·
                  refine ⟨360185227048352037857387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3841975755182421737145461 360185227048352037857387)
                  ·
                    rfl

theorem cell22_3156562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_3156562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156562 prefixEnd_3156562 := by exact prefixLift 3156562
  have htrace : WordTrace (prefixWord ++ tailWord_3156562) baseStart_3156562 baseEnd_3156562 := by
    simpa [prefixWord, tailWord_3156562, baseEnd_3156562] using wordTrace_append hprefix tailTrace_3156562
  have hstable : (prefixWord ++ tailWord_3156562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156562).length < 2 ^ (prefixWord ++ tailWord_3156562).sum := by decide
  have hdescent : baseEnd_3156562 < baseStart_3156562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156641 : List Nat := [1, 2, 3, 3, 3, 1, 2, 3, 4]
def baseStart_3156641 : Nat := 118140960795 + 3156641 * 2 ^ 59
def prefixEnd_3156641 : Nat := 4983230072969 + 3 ^ 40 * 3156641 * 2
def baseEnd_3156641 : Nat := 360194241486508746948973

theorem tailTrace_3156641 : CollatzResearch.WordTrace tailWord_3156641 prefixEnd_3156641 360194241486508746948973 := by
  unfold tailWord_3156641
  simp only [CollatzResearch.WordTrace]
  refine ⟨115132155757036243207061777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76754770504690828804707851 115132155757036243207061777)
  ·
    refine ⟨86349116817777182405296333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115132155757036243207061777 86349116817777182405296333)
    ·
      refine ⟨32380918806666443401986125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86349116817777182405296333 32380918806666443401986125)
      ·
        refine ⟨12142844552499916275744797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32380918806666443401986125 12142844552499916275744797)
        ·
          refine ⟨4553566707187468603404299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12142844552499916275744797 4553566707187468603404299)
          ·
            refine ⟨6830350060781202905106449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4553566707187468603404299 6830350060781202905106449)
            ·
              refine ⟨5122762545585902178829837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6830350060781202905106449 5122762545585902178829837)
              ·
                refine ⟨1921035954594713317061189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5122762545585902178829837 1921035954594713317061189)
                ·
                  refine ⟨360194241486508746948973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1921035954594713317061189 360194241486508746948973)
                  ·
                    rfl

theorem cell22_3156641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3, 4].length) (baseStart_3156641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156641 prefixEnd_3156641 := by exact prefixLift 3156641
  have htrace : WordTrace (prefixWord ++ tailWord_3156641) baseStart_3156641 baseEnd_3156641 := by
    simpa [prefixWord, tailWord_3156641, baseEnd_3156641] using wordTrace_append hprefix tailTrace_3156641
  have hstable : (prefixWord ++ tailWord_3156641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156641).length < 2 ^ (prefixWord ++ tailWord_3156641).sum := by decide
  have hdescent : baseEnd_3156641 < baseStart_3156641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156673 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3156673 : Nat := 118140960795 + 3156673 * 2 ^ 59
def prefixEnd_3156673 : Nat := 4983230072969 + 3 ^ 40 * 3156673 * 2
def baseEnd_3156673 : Nat := 1080593678713488824046821

theorem tailTrace_3156673 : CollatzResearch.WordTrace tailWord_3156673 prefixEnd_3156673 1080593678713488824046821 := by
  unfold tailWord_3156673
  simp only [CollatzResearch.WordTrace]
  refine ⟨115133322892920312672226673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76755548595280208448151115 115133322892920312672226673)
  ·
    refine ⟨86349992169690234504170005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115133322892920312672226673 86349992169690234504170005)
    ·
      refine ⟨4047655882954229742382969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86349992169690234504170005 4047655882954229742382969)
      ·
        refine ⟨3035741912215672306787227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4047655882954229742382969 3035741912215672306787227)
        ·
          refine ⟨4553612868323508460180841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3035741912215672306787227 4553612868323508460180841)
          ·
            refine ⟨3415209651242631345135631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4553612868323508460180841 3415209651242631345135631)
            ·
              refine ⟨5122814476863947017703447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3415209651242631345135631 5122814476863947017703447)
              ·
                refine ⟨7684221715295920526555171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5122814476863947017703447 7684221715295920526555171)
                ·
                  refine ⟨11526332572943880789832757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7684221715295920526555171 11526332572943880789832757)
                  ·
                    refine ⟨1080593678713488824046821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11526332572943880789832757 1080593678713488824046821)
                    ·
                      rfl

theorem cell22_3156673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3156673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156673 prefixEnd_3156673 := by exact prefixLift 3156673
  have htrace : WordTrace (prefixWord ++ tailWord_3156673) baseStart_3156673 baseEnd_3156673 := by
    simpa [prefixWord, tailWord_3156673, baseEnd_3156673] using wordTrace_append hprefix tailTrace_3156673
  have hstable : (prefixWord ++ tailWord_3156673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156673).length < 2 ^ (prefixWord ++ tailWord_3156673).sum := by decide
  have hdescent : baseEnd_3156673 < baseStart_3156673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156724 : List Nat := [2, 6, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3156724 : Nat := 118140960795 + 3156724 * 2 ^ 59
def prefixEnd_3156724 : Nat := 4983230072969 + 3 ^ 40 * 3156724 * 2
def baseEnd_3156724 : Nat := 1080611137055741691021665

theorem tailTrace_3156724 : CollatzResearch.WordTrace tailWord_3156724 prefixEnd_3156724 1080611137055741691021665 := by
  unfold tailWord_3156724
  simp only [CollatzResearch.WordTrace]
  refine ⟨57567591507867774191166613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76756788677157032254888817 57567591507867774191166613)
  ·
    refine ⟨2698480851931301915210935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57567591507867774191166613 2698480851931301915210935)
    ·
      refine ⟨4047721277896952872816403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2698480851931301915210935 4047721277896952872816403)
      ·
        refine ⟨6071581916845429309224605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4047721277896952872816403 6071581916845429309224605)
        ·
          refine ⟨2276843218817035990959227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6071581916845429309224605 2276843218817035990959227)
          ·
            refine ⟨3415264828225553986438841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276843218817035990959227 3415264828225553986438841)
            ·
              refine ⟨2561448621169165489829131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3415264828225553986438841 2561448621169165489829131)
              ·
                refine ⟨3842172931753748234743697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2561448621169165489829131 3842172931753748234743697)
                ·
                  refine ⟨2881629698815311176057773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3842172931753748234743697 2881629698815311176057773)
                  ·
                    refine ⟨1080611137055741691021665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2881629698815311176057773 1080611137055741691021665)
                    ·
                      rfl

theorem cell22_3156724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3156724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156724 prefixEnd_3156724 := by exact prefixLift 3156724
  have htrace : WordTrace (prefixWord ++ tailWord_3156724) baseStart_3156724 baseEnd_3156724 := by
    simpa [prefixWord, tailWord_3156724, baseEnd_3156724] using wordTrace_append hprefix tailTrace_3156724
  have hstable : (prefixWord ++ tailWord_3156724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156724).length < 2 ^ (prefixWord ++ tailWord_3156724).sum := by decide
  have hdescent : baseEnd_3156724 < baseStart_3156724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156727 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 3, 4]
def baseStart_3156727 : Nat := 118140960795 + 3156727 * 2 ^ 59
def prefixEnd_3156727 : Nat := 4983230072969 + 3 ^ 40 * 3156727 * 2
def baseEnd_3156727 : Nat := 1080612164017050683196655

theorem tailTrace_3156727 : CollatzResearch.WordTrace tailWord_3156727 prefixEnd_3156727 1080612164017050683196655 := by
  unfold tailWord_3156727
  simp only [CollatzResearch.WordTrace]
  refine ⟨115135292434724679894692435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76756861623149786596461623 115135292434724679894692435)
  ·
    refine ⟨172702938652087019842038653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115135292434724679894692435 172702938652087019842038653)
    ·
      refine ⟨64763601994532632440764495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172702938652087019842038653 64763601994532632440764495)
      ·
        refine ⟨97145402991798948661146743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64763601994532632440764495 97145402991798948661146743)
        ·
          refine ⟨145718104487698422991720115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97145402991798948661146743 145718104487698422991720115)
          ·
            refine ⟨218577156731547634487580173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145718104487698422991720115 218577156731547634487580173)
            ·
              refine ⟨81966433774330362932842565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218577156731547634487580173 81966433774330362932842565)
              ·
                refine ⟨15368706332686943049907981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81966433774330362932842565 15368706332686943049907981)
                ·
                  refine ⟨5763264874757603643715493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15368706332686943049907981 5763264874757603643715493)
                  ·
                    refine ⟨1080612164017050683196655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5763264874757603643715493 1080612164017050683196655)
                    ·
                      rfl

theorem cell22_3156727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_3156727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156727 prefixEnd_3156727 := by exact prefixLift 3156727
  have htrace : WordTrace (prefixWord ++ tailWord_3156727) baseStart_3156727 baseEnd_3156727 := by
    simpa [prefixWord, tailWord_3156727, baseEnd_3156727] using wordTrace_append hprefix tailTrace_3156727
  have hstable : (prefixWord ++ tailWord_3156727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156727).length < 2 ^ (prefixWord ++ tailWord_3156727).sum := by decide
  have hdescent : baseEnd_3156727 < baseStart_3156727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156744 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 3, 4]
def baseStart_3156744 : Nat := 118140960795 + 3156744 * 2 ^ 59
def prefixEnd_3156744 : Nat := 4983230072969 + 3 ^ 40 * 3156744 * 2
def baseEnd_3156744 : Nat := 1080617983464468305521603

theorem tailTrace_3156744 : CollatzResearch.WordTrace tailWord_3156744 prefixEnd_3156744 1080617983464468305521603 := by
  unfold tailWord_3156744
  simp only [CollatzResearch.WordTrace]
  refine ⟨57567956237831545899030643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76757274983775394532040857 57567956237831545899030643)
  ·
    refine ⟨86351934356747318848545965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57567956237831545899030643 86351934356747318848545965)
    ·
      refine ⟨32381975383780244568204737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86351934356747318848545965 32381975383780244568204737)
      ·
        refine ⟨24286481537835183426153553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32381975383780244568204737 24286481537835183426153553)
        ·
          refine ⟨18214861153376387569615165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24286481537835183426153553 18214861153376387569615165)
          ·
            refine ⟨6830572932516145338605687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18214861153376387569615165 6830572932516145338605687)
            ·
              refine ⟨10245859398774218007908531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6830572932516145338605687 10245859398774218007908531)
              ·
                refine ⟨15368789098161327011862797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10245859398774218007908531 15368789098161327011862797)
                ·
                  refine ⟨5763295911810497629448549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15368789098161327011862797 5763295911810497629448549)
                  ·
                    refine ⟨1080617983464468305521603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5763295911810497629448549 1080617983464468305521603)
                    ·
                      rfl

theorem cell22_3156744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_3156744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156744 prefixEnd_3156744 := by exact prefixLift 3156744
  have htrace : WordTrace (prefixWord ++ tailWord_3156744) baseStart_3156744 baseEnd_3156744 := by
    simpa [prefixWord, tailWord_3156744, baseEnd_3156744] using wordTrace_append hprefix tailTrace_3156744
  have hstable : (prefixWord ++ tailWord_3156744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156744).length < 2 ^ (prefixWord ++ tailWord_3156744).sum := by decide
  have hdescent : baseEnd_3156744 < baseStart_3156744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156776 : List Nat := [2, 1, 5, 1, 1, 1, 3, 4, 4]
def baseStart_3156776 : Nat := 118140960795 + 3156776 * 2 ^ 59
def prefixEnd_3156776 : Nat := 4983230072969 + 3 ^ 40 * 3156776 * 2
def baseEnd_3156776 : Nat := 360209645906143629573835

theorem tailTrace_3156776 : CollatzResearch.WordTrace tailWord_3156776 prefixEnd_3156776 360209645906143629573835 := by
  unfold tailWord_3156776
  simp only [CollatzResearch.WordTrace]
  refine ⟨57568539805773580631613091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76758053074364774175484121 57568539805773580631613091)
  ·
    refine ⟨86352809708660370947419637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57568539805773580631613091 86352809708660370947419637)
    ·
      refine ⟨8095575910186909776320591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86352809708660370947419637 8095575910186909776320591)
      ·
        refine ⟨12143363865280364664480887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8095575910186909776320591 12143363865280364664480887)
        ·
          refine ⟨18215045797920546996721331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12143363865280364664480887 18215045797920546996721331)
          ·
            refine ⟨27322568696880820495081997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18215045797920546996721331 27322568696880820495081997)
            ·
              refine ⟨10245963261330307685655749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27322568696880820495081997 10245963261330307685655749)
              ·
                refine ⟨1921118111499432691060453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10245963261330307685655749 1921118111499432691060453)
                ·
                  refine ⟨360209645906143629573835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1921118111499432691060453 360209645906143629573835)
                  ·
                    rfl

theorem cell22_3156776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4, 4].length) (baseStart_3156776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156776 prefixEnd_3156776 := by exact prefixLift 3156776
  have htrace : WordTrace (prefixWord ++ tailWord_3156776) baseStart_3156776 baseEnd_3156776 := by
    simpa [prefixWord, tailWord_3156776, baseEnd_3156776] using wordTrace_append hprefix tailTrace_3156776
  have hstable : (prefixWord ++ tailWord_3156776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156776).length < 2 ^ (prefixWord ++ tailWord_3156776).sum := by decide
  have hdescent : baseEnd_3156776 < baseStart_3156776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156836 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_3156836 : Nat := 118140960795 + 3156836 * 2 ^ 59
def prefixEnd_3156836 : Nat := 4983230072969 + 3 ^ 40 * 3156836 * 2
def baseEnd_3156836 : Nat := 1080649476944610732221321

theorem tailTrace_3156836 : CollatzResearch.WordTrace tailWord_3156836 prefixEnd_3156836 1080649476944610732221321 := by
  unfold tailWord_3156836
  simp only [CollatzResearch.WordTrace]
  refine ⟨57569633995664895755205181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76759511994219861006940241 57569633995664895755205181)
  ·
    refine ⟨21588612748374335908201943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57569633995664895755205181 21588612748374335908201943)
    ·
      refine ⟨32382919122561503862302915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21588612748374335908201943 32382919122561503862302915)
      ·
        refine ⟨48574378683842255793454373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32382919122561503862302915 48574378683842255793454373)
        ·
          refine ⟨9107696003220422961272695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48574378683842255793454373 9107696003220422961272695)
          ·
            refine ⟨13661544004830634441909043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9107696003220422961272695 13661544004830634441909043)
            ·
              refine ⟨20492316007245951662863565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13661544004830634441909043 20492316007245951662863565)
              ·
                refine ⟨7684618502717231873573837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20492316007245951662863565 7684618502717231873573837)
                ·
                  refine ⟨2881731938518961952590189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7684618502717231873573837 2881731938518961952590189)
                  ·
                    refine ⟨1080649476944610732221321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2881731938518961952590189 1080649476944610732221321)
                    ·
                      rfl

theorem cell22_3156836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_3156836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156836 prefixEnd_3156836 := by exact prefixLift 3156836
  have htrace : WordTrace (prefixWord ++ tailWord_3156836) baseStart_3156836 baseEnd_3156836 := by
    simpa [prefixWord, tailWord_3156836, baseEnd_3156836] using wordTrace_append hprefix tailTrace_3156836
  have hstable : (prefixWord ++ tailWord_3156836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156836).length < 2 ^ (prefixWord ++ tailWord_3156836).sum := by decide
  have hdescent : baseEnd_3156836 < baseStart_3156836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156926 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_3156926 : Nat := 118140960795 + 3156926 * 2 ^ 59
def prefixEnd_3156926 : Nat := 4983230072969 + 3 ^ 40 * 3156926 * 2
def baseEnd_3156926 : Nat := 1080680285783880497471045

theorem tailTrace_3156926 : CollatzResearch.WordTrace tailWord_3156926 prefixEnd_3156926 1080680285783880497471045 := by
  unfold tailWord_3156926
  simp only [CollatzResearch.WordTrace]
  refine ⟨14392818820125467110148329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76761700374002491254124421 14392818820125467110148329)
  ·
    refine ⟨10794614115094100332611247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14392818820125467110148329 10794614115094100332611247)
    ·
      refine ⟨16191921172641150498916871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10794614115094100332611247 16191921172641150498916871)
      ·
        refine ⟨24287881758961725748375307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16191921172641150498916871 24287881758961725748375307)
        ·
          refine ⟨36431822638442588622562961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24287881758961725748375307 36431822638442588622562961)
          ·
            refine ⟨27323866978831941466922221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36431822638442588622562961 27323866978831941466922221)
            ·
              refine ⟨10246450117061978050095833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27323866978831941466922221 10246450117061978050095833)
              ·
                refine ⟨7684837587796483537571875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10246450117061978050095833 7684837587796483537571875)
                ·
                  refine ⟨11527256381694725306357813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7684837587796483537571875 11527256381694725306357813)
                  ·
                    refine ⟨1080680285783880497471045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11527256381694725306357813 1080680285783880497471045)
                    ·
                      rfl

theorem cell22_3156926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_3156926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156926 prefixEnd_3156926 := by exact prefixLift 3156926
  have htrace : WordTrace (prefixWord ++ tailWord_3156926) baseStart_3156926 baseEnd_3156926 := by
    simpa [prefixWord, tailWord_3156926, baseEnd_3156926] using wordTrace_append hprefix tailTrace_3156926
  have hstable : (prefixWord ++ tailWord_3156926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156926).length < 2 ^ (prefixWord ++ tailWord_3156926).sum := by decide
  have hdescent : baseEnd_3156926 < baseStart_3156926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156934 : List Nat := [6, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_3156934 : Nat := 118140960795 + 3156934 * 2 ^ 59
def prefixEnd_3156934 : Nat := 4983230072969 + 3 ^ 40 * 3156934 * 2
def baseEnd_3156934 : Nat := 360227674782457047757007

theorem tailTrace_3156934 : CollatzResearch.WordTrace tailWord_3156934 prefixEnd_3156934 360227674782457047757007 := by
  unfold tailWord_3156934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3598213823280461070233683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76761894896649836164985237 3598213823280461070233683)
  ·
    refine ⟨5397320734920691605350525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3598213823280461070233683 5397320734920691605350525)
    ·
      refine ⟨2023995275595259352006447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5397320734920691605350525 2023995275595259352006447)
      ·
        refine ⟨3035992913392889028009671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2023995275595259352006447 3035992913392889028009671)
        ·
          refine ⟨4553989370089333542014507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3035992913392889028009671 4553989370089333542014507)
          ·
            refine ⟨6830984055134000313021761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4553989370089333542014507 6830984055134000313021761)
            ·
              refine ⟨5123238041350500234766321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6830984055134000313021761 5123238041350500234766321)
              ·
                refine ⟨3842428531012875176074741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5123238041350500234766321 3842428531012875176074741)
                ·
                  refine ⟨360227674782457047757007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3842428531012875176074741 360227674782457047757007)
                  ·
                    rfl

theorem cell22_3156934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_3156934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156934 prefixEnd_3156934 := by exact prefixLift 3156934
  have htrace : WordTrace (prefixWord ++ tailWord_3156934) baseStart_3156934 baseEnd_3156934 := by
    simpa [prefixWord, tailWord_3156934, baseEnd_3156934] using wordTrace_append hprefix tailTrace_3156934
  have hstable : (prefixWord ++ tailWord_3156934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156934).length < 2 ^ (prefixWord ++ tailWord_3156934).sum := by decide
  have hdescent : baseEnd_3156934 < baseStart_3156934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156943 : List Nat := [1, 1, 2, 1, 1, 7, 2, 2, 2, 3]
def baseStart_3156943 : Nat := 118140960795 + 3156943 * 2 ^ 59
def prefixEnd_3156943 : Nat := 4983230072969 + 3 ^ 40 * 3156943 * 2
def baseEnd_3156943 : Nat := 1080686105231298119795993

theorem tailTrace_3156943 : CollatzResearch.WordTrace tailWord_3156943 prefixEnd_3156943 1080686105231298119795993 := by
  unfold tailWord_3156943
  simp only [CollatzResearch.WordTrace]
  refine ⟨115143170601942148784555483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76762113734628099189703655 115143170601942148784555483)
  ·
    refine ⟨172714755902913223176833225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115143170601942148784555483 172714755902913223176833225)
    ·
      refine ⟨129536066927184917382624919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172714755902913223176833225 129536066927184917382624919)
      ·
        refine ⟨194304100390777376073937379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129536066927184917382624919 194304100390777376073937379)
        ·
          refine ⟨291456150586166064110906069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194304100390777376073937379 291456150586166064110906069)
          ·
            refine ⟨6831003529363267127599361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 291456150586166064110906069 6831003529363267127599361)
            ·
              refine ⟨5123252647022450345699521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6831003529363267127599361 5123252647022450345699521)
              ·
                refine ⟨3842439485266837759274641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5123252647022450345699521 3842439485266837759274641)
                ·
                  refine ⟨2881829613950128319455981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3842439485266837759274641 2881829613950128319455981)
                  ·
                    refine ⟨1080686105231298119795993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2881829613950128319455981 1080686105231298119795993)
                    ·
                      rfl

theorem cell22_3156943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 3].length) (baseStart_3156943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156943 prefixEnd_3156943 := by exact prefixLift 3156943
  have htrace : WordTrace (prefixWord ++ tailWord_3156943) baseStart_3156943 baseEnd_3156943 := by
    simpa [prefixWord, tailWord_3156943, baseEnd_3156943] using wordTrace_append hprefix tailTrace_3156943
  have hstable : (prefixWord ++ tailWord_3156943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156943).length < 2 ^ (prefixWord ++ tailWord_3156943).sum := by decide
  have hdescent : baseEnd_3156943 < baseStart_3156943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156984 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 7]
def baseStart_3156984 : Nat := 118140960795 + 3156984 * 2 ^ 59
def prefixEnd_3156984 : Nat := 4983230072969 + 3 ^ 40 * 3156984 * 2
def baseEnd_3156984 : Nat := 360233380123062559840289

theorem tailTrace_3156984 : CollatzResearch.WordTrace tailWord_3156984 prefixEnd_3156984 360233380123062559840289 := by
  unfold tailWord_3156984
  simp only [CollatzResearch.WordTrace]
  refine ⟨57572332997396806393399003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76763110663195741857865337 57572332997396806393399003)
  ·
    refine ⟨86358499496095209590098505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57572332997396806393399003 86358499496095209590098505)
    ·
      refine ⟨64768874622071407192573879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86358499496095209590098505 64768874622071407192573879)
      ·
        refine ⟨97153311933107110788860819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64768874622071407192573879 97153311933107110788860819)
        ·
          refine ⟨145729967899660666183291229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97153311933107110788860819 145729967899660666183291229)
          ·
            refine ⟨54648737962372749818734211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145729967899660666183291229 54648737962372749818734211)
            ·
              refine ⟨81973106943559124728101317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54648737962372749818734211 81973106943559124728101317)
              ·
                refine ⟨15369957551917335886518997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81973106943559124728101317 15369957551917335886518997)
                ·
                  refine ⟨360233380123062559840289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15369957551917335886518997 360233380123062559840289)
                  ·
                    rfl

theorem cell22_3156984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_3156984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156984 prefixEnd_3156984 := by exact prefixLift 3156984
  have htrace : WordTrace (prefixWord ++ tailWord_3156984) baseStart_3156984 baseEnd_3156984 := by
    simpa [prefixWord, tailWord_3156984, baseEnd_3156984] using wordTrace_append hprefix tailTrace_3156984
  have hstable : (prefixWord ++ tailWord_3156984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156984).length < 2 ^ (prefixWord ++ tailWord_3156984).sum := by decide
  have hdescent : baseEnd_3156984 < baseStart_3156984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156994 : List Nat := [3, 4, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_3156994 : Nat := 118140960795 + 3156994 * 2 ^ 59
def prefixEnd_3156994 : Nat := 4983230072969 + 3 ^ 40 * 3156994 * 2
def baseEnd_3156994 : Nat := 1080703563573550986770837

theorem tailTrace_3156994 : CollatzResearch.WordTrace tailWord_3156994 prefixEnd_3156994 1080703563573550986770837 := by
  unfold tailWord_3156994
  simp only [CollatzResearch.WordTrace]
  refine ⟨28786257681189346123665509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76763353816504922996441357 28786257681189346123665509)
  ·
    refine ⟨5397423315223002398187283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28786257681189346123665509 5397423315223002398187283)
    ·
      refine ⟨8096134972834503597280925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5397423315223002398187283 8096134972834503597280925)
      ·
        refine ⟨3036050614812938848980347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8096134972834503597280925 3036050614812938848980347)
        ·
          refine ⟨4554075922219408273470521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3036050614812938848980347 4554075922219408273470521)
          ·
            refine ⟨3415556941664556205102891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4554075922219408273470521 3415556941664556205102891)
            ·
              refine ⟨5123335412496834307654337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3415556941664556205102891 5123335412496834307654337)
              ·
                refine ⟨3842501559372625730740753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5123335412496834307654337 3842501559372625730740753)
                ·
                  refine ⟨2881876169529469298055565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3842501559372625730740753 2881876169529469298055565)
                  ·
                    refine ⟨1080703563573550986770837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2881876169529469298055565 1080703563573550986770837)
                    ·
                      rfl

theorem cell22_3156994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_3156994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3156994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3156994 prefixEnd_3156994 := by exact prefixLift 3156994
  have htrace : WordTrace (prefixWord ++ tailWord_3156994) baseStart_3156994 baseEnd_3156994 := by
    simpa [prefixWord, tailWord_3156994, baseEnd_3156994] using wordTrace_append hprefix tailTrace_3156994
  have hstable : (prefixWord ++ tailWord_3156994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156994).length < 2 ^ (prefixWord ++ tailWord_3156994).sum := by decide
  have hdescent : baseEnd_3156994 < baseStart_3156994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157016 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 2, 5]
def baseStart_3157016 : Nat := 118140960795 + 3157016 * 2 ^ 59
def prefixEnd_3157016 : Nat := 4983230072969 + 3 ^ 40 * 3157016 * 2
def baseEnd_3157016 : Nat := 1080711094623150262720769

theorem tailTrace_3157016 : CollatzResearch.WordTrace tailWord_3157016 prefixEnd_3157016 1080711094623150262720769 := by
  unfold tailWord_3157016
  simp only [CollatzResearch.WordTrace]
  refine ⟨57572916565338841125981451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76763888753785121501308601 57572916565338841125981451)
  ·
    refine ⟨86359374848008261688972177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57572916565338841125981451 86359374848008261688972177)
    ·
      refine ⟨64769531136006196266729133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86359374848008261688972177 64769531136006196266729133)
      ·
        refine ⟨24288574176002323600023425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64769531136006196266729133 24288574176002323600023425)
        ·
          refine ⟨18216430632001742700017569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24288574176002323600023425 18216430632001742700017569)
          ·
            refine ⟨13662322974001307025013177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18216430632001742700017569 13662322974001307025013177)
            ·
              refine ⟨10246742230500980268759883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13662322974001307025013177 10246742230500980268759883)
              ·
                refine ⟨15370113345751470403139825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10246742230500980268759883 15370113345751470403139825)
                ·
                  refine ⟨11527585009313602802354869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15370113345751470403139825 11527585009313602802354869)
                  ·
                    refine ⟨1080711094623150262720769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11527585009313602802354869 1080711094623150262720769)
                    ·
                      rfl

theorem cell22_3157016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_3157016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157016 prefixEnd_3157016 := by exact prefixLift 3157016
  have htrace : WordTrace (prefixWord ++ tailWord_3157016) baseStart_3157016 baseEnd_3157016 := by
    simpa [prefixWord, tailWord_3157016, baseEnd_3157016] using wordTrace_append hprefix tailTrace_3157016
  have hstable : (prefixWord ++ tailWord_3157016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157016).length < 2 ^ (prefixWord ++ tailWord_3157016).sum := by decide
  have hdescent : baseEnd_3157016 < baseStart_3157016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157018 : List Nat := [3, 1, 1, 3, 1, 2, 5, 1, 5]
def baseStart_3157018 : Nat := 118140960795 + 3157018 * 2 ^ 59
def prefixEnd_3157018 : Nat := 4983230072969 + 3 ^ 40 * 3157018 * 2
def baseEnd_3157018 : Nat := 360237259754674308056921

theorem tailTrace_3157018 : CollatzResearch.WordTrace tailWord_3157018 prefixEnd_3157018 360237259754674308056921 := by
  unfold tailWord_3157018
  simp only [CollatzResearch.WordTrace]
  refine ⟨28786476519167609148383927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76763937384446957729023805 28786476519167609148383927)
  ·
    refine ⟨43179714778751413722575891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28786476519167609148383927 43179714778751413722575891)
    ·
      refine ⟨64769572168127120583863837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43179714778751413722575891 64769572168127120583863837)
      ·
        refine ⟨24288589563047670218948939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64769572168127120583863837 24288589563047670218948939)
        ·
          refine ⟨36432884344571505328423409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24288589563047670218948939 36432884344571505328423409)
          ·
            refine ⟨27324663258428628996317557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36432884344571505328423409 27324663258428628996317557)
            ·
              refine ⟨2561687180477683968404771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27324663258428628996317557 2561687180477683968404771)
              ·
                refine ⟨3842530770716525952607157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2561687180477683968404771 3842530770716525952607157)
                ·
                  refine ⟨360237259754674308056921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3842530770716525952607157 360237259754674308056921)
                  ·
                    rfl

theorem cell22_3157018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_3157018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157018 prefixEnd_3157018 := by exact prefixLift 3157018
  have htrace : WordTrace (prefixWord ++ tailWord_3157018) baseStart_3157018 baseEnd_3157018 := by
    simpa [prefixWord, tailWord_3157018, baseEnd_3157018] using wordTrace_append hprefix tailTrace_3157018
  have hstable : (prefixWord ++ tailWord_3157018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157018).length < 2 ^ (prefixWord ++ tailWord_3157018).sum := by decide
  have hdescent : baseEnd_3157018 < baseStart_3157018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157048 : List Nat := [2, 1, 2, 1, 5, 1, 2, 3, 1, 4]
def baseStart_3157048 : Nat := 118140960795 + 3157048 * 2 ^ 59
def prefixEnd_3157048 : Nat := 4983230072969 + 3 ^ 40 * 3157048 * 2
def baseEnd_3157048 : Nat := 1080722048877112845920671

theorem tailTrace_3157048 : CollatzResearch.WordTrace tailWord_3157048 prefixEnd_3157048 1080722048877112845920671 := by
  unfold tailWord_3157048
  simp only [CollatzResearch.WordTrace]
  refine ⟨57573500133280875858563899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76764666844374501144751865 57573500133280875858563899)
  ·
    refine ⟨86360250199921313787845849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57573500133280875858563899 86360250199921313787845849)
    ·
      refine ⟨64770187649940985340884387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86360250199921313787845849 64770187649940985340884387)
      ·
        refine ⟨97155281474911478011326581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64770187649940985340884387 97155281474911478011326581)
        ·
          refine ⟨9108307638272951063561867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97155281474911478011326581 9108307638272951063561867)
          ·
            refine ⟨13662461457409426595342801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9108307638272951063561867 13662461457409426595342801)
            ·
              refine ⟨10246846093057069946507101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13662461457409426595342801 10246846093057069946507101)
              ·
                refine ⟨3842567284896401229940163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10246846093057069946507101 3842567284896401229940163)
                ·
                  refine ⟨5763850927344601844910245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3842567284896401229940163 5763850927344601844910245)
                  ·
                    refine ⟨1080722048877112845920671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5763850927344601844910245 1080722048877112845920671)
                    ·
                      rfl

theorem cell22_3157048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_3157048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157048 prefixEnd_3157048 := by exact prefixLift 3157048
  have htrace : WordTrace (prefixWord ++ tailWord_3157048) baseStart_3157048 baseEnd_3157048 := by
    simpa [prefixWord, tailWord_3157048, baseEnd_3157048] using wordTrace_append hprefix tailTrace_3157048
  have hstable : (prefixWord ++ tailWord_3157048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157048).length < 2 ^ (prefixWord ++ tailWord_3157048).sum := by decide
  have hdescent : baseEnd_3157048 < baseStart_3157048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157063 : List Nat := [1, 1, 4, 1, 3, 4, 1, 1, 6]
def baseStart_3157063 : Nat := 118140960795 + 3157063 * 2 ^ 59
def prefixEnd_3157063 : Nat := 4983230072969 + 3 ^ 40 * 3157063 * 2
def baseEnd_3157063 : Nat := 360242394561219268931875

theorem tailTrace_3157063 : CollatzResearch.WordTrace tailWord_3157063 prefixEnd_3157063 360242394561219268931875 := by
  unfold tailWord_3157063
  simp only [CollatzResearch.WordTrace]
  refine ⟨115147547361507409278923843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76765031574338272852615895 115147547361507409278923843)
  ·
    refine ⟨172721321042261113918385765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115147547361507409278923843 172721321042261113918385765)
    ·
      refine ⟨32385247695423958859697331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172721321042261113918385765 32385247695423958859697331)
      ·
        refine ⟨48577871543135938289545997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32385247695423958859697331 48577871543135938289545997)
        ·
          refine ⟨18216701828675976858579749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48577871543135938289545997 18216701828675976858579749)
          ·
            refine ⟨3415631592876745660983703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18216701828675976858579749 3415631592876745660983703)
            ·
              refine ⟨5123447389315118491475555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3415631592876745660983703 5123447389315118491475555)
              ·
                refine ⟨7685171083972677737213333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5123447389315118491475555 7685171083972677737213333)
                ·
                  refine ⟨360242394561219268931875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7685171083972677737213333 360242394561219268931875)
                  ·
                    rfl

theorem cell22_3157063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 1, 6].length) (baseStart_3157063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157063 prefixEnd_3157063 := by exact prefixLift 3157063
  have htrace : WordTrace (prefixWord ++ tailWord_3157063) baseStart_3157063 baseEnd_3157063 := by
    simpa [prefixWord, tailWord_3157063, baseEnd_3157063] using wordTrace_append hprefix tailTrace_3157063
  have hstable : (prefixWord ++ tailWord_3157063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157063).length < 2 ^ (prefixWord ++ tailWord_3157063).sum := by decide
  have hdescent : baseEnd_3157063 < baseStart_3157063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157076 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3157076 : Nat := 118140960795 + 3157076 * 2 ^ 59
def prefixEnd_3157076 : Nat := 4983230072969 + 3 ^ 40 * 3157076 * 2
def baseEnd_3157076 : Nat := 1080731633849330106220585

theorem tailTrace_3157076 : CollatzResearch.WordTrace tailWord_3157076 prefixEnd_3157076 1080731633849330106220585 := by
  unfold tailWord_3157076
  simp only [CollatzResearch.WordTrace]
  refine ⟨57574010755230156249573541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76765347673640208332764721 57574010755230156249573541)
  ·
    refine ⟨10795127016605654296795039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57574010755230156249573541 10795127016605654296795039)
    ·
      refine ⟨16192690524908481445192559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10795127016605654296795039 16192690524908481445192559)
      ·
        refine ⟨24289035787362722167788839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16192690524908481445192559 24289035787362722167788839)
        ·
          refine ⟨36433553681044083251683259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24289035787362722167788839 36433553681044083251683259)
          ·
            refine ⟨54650330521566124877524889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36433553681044083251683259 54650330521566124877524889)
            ·
              refine ⟨40987747891174593658143667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54650330521566124877524889 40987747891174593658143667)
              ·
                refine ⟨61481621836761890487215501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40987747891174593658143667 61481621836761890487215501)
                ·
                  refine ⟨23055608188785708932705813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61481621836761890487215501 23055608188785708932705813)
                  ·
                    refine ⟨1080731633849330106220585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23055608188785708932705813 1080731633849330106220585)
                    ·
                      rfl

theorem cell22_3157076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3157076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157076 prefixEnd_3157076 := by exact prefixLift 3157076
  have htrace : WordTrace (prefixWord ++ tailWord_3157076) baseStart_3157076 baseEnd_3157076 := by
    simpa [prefixWord, tailWord_3157076, baseEnd_3157076] using wordTrace_append hprefix tailTrace_3157076
  have hstable : (prefixWord ++ tailWord_3157076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157076).length < 2 ^ (prefixWord ++ tailWord_3157076).sum := by decide
  have hdescent : baseEnd_3157076 < baseStart_3157076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157093 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 2, 4]
def baseStart_3157093 : Nat := 118140960795 + 3157093 * 2 ^ 59
def prefixEnd_3157093 : Nat := 4983230072969 + 3 ^ 40 * 3157093 * 2
def baseEnd_3157093 : Nat := 1080737453296747728545533

theorem tailTrace_3157093 : CollatzResearch.WordTrace tailWord_3157093 prefixEnd_3157093 1080737453296747728545533 := by
  unfold tailWord_3157093
  simp only [CollatzResearch.WordTrace]
  refine ⟨115148641551398724402515933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76765761034265816268343955 115148641551398724402515933)
  ·
    refine ⟨43180740581774521650943475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115148641551398724402515933 43180740581774521650943475)
    ·
      refine ⟨64771110872661782476415213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43180740581774521650943475 64771110872661782476415213)
      ·
        refine ⟨24289166577248168428655705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64771110872661782476415213 24289166577248168428655705)
        ·
          refine ⟨18216874932936126321491779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24289166577248168428655705 18216874932936126321491779)
          ·
            refine ⟨27325312399404189482237669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18216874932936126321491779 27325312399404189482237669)
            ·
              refine ⟨5123496074888285527919563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27325312399404189482237669 5123496074888285527919563)
              ·
                refine ⟨7685244112332428291879345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5123496074888285527919563 7685244112332428291879345)
                ·
                  refine ⟨5763933084249321218909509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7685244112332428291879345 5763933084249321218909509)
                  ·
                    refine ⟨1080737453296747728545533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5763933084249321218909509 1080737453296747728545533)
                    ·
                      rfl

theorem cell22_3157093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_3157093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157093 prefixEnd_3157093 := by exact prefixLift 3157093
  have htrace : WordTrace (prefixWord ++ tailWord_3157093) baseStart_3157093 baseEnd_3157093 := by
    simpa [prefixWord, tailWord_3157093, baseEnd_3157093] using wordTrace_append hprefix tailTrace_3157093
  have hstable : (prefixWord ++ tailWord_3157093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157093).length < 2 ^ (prefixWord ++ tailWord_3157093).sum := by decide
  have hdescent : baseEnd_3157093 < baseStart_3157093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157123 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 3, 3]
def baseStart_3157123 : Nat := 118140960795 + 3157123 * 2 ^ 59
def prefixEnd_3157123 : Nat := 4983230072969 + 3 ^ 40 * 3157123 * 2
def baseEnd_3157123 : Nat := 1080747722909837650295441

theorem tailTrace_3157123 : CollatzResearch.WordTrace tailWord_3157123 prefixEnd_3157123 1080747722909837650295441 := by
  unfold tailWord_3157123
  simp only [CollatzResearch.WordTrace]
  refine ⟨115149735741290039526108023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76766490494193359684072015 115149735741290039526108023)
  ·
    refine ⟨172724603611935059289162035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115149735741290039526108023 172724603611935059289162035)
    ·
      refine ⟨259086905417902588933743053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172724603611935059289162035 259086905417902588933743053)
      ·
        refine ⟨97157589531713470850153645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259086905417902588933743053 97157589531713470850153645)
        ·
          refine ⟨36434096074392551568807617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97157589531713470850153645 36434096074392551568807617)
          ·
            refine ⟨27325572055794413676605713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36434096074392551568807617 27325572055794413676605713)
            ·
              refine ⟨20494179041845810257454285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27325572055794413676605713 20494179041845810257454285)
              ·
                refine ⟨7685317140692178846545357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20494179041845810257454285 7685317140692178846545357)
                ·
                  refine ⟨2881993927759567067454509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7685317140692178846545357 2881993927759567067454509)
                  ·
                    refine ⟨1080747722909837650295441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2881993927759567067454509 1080747722909837650295441)
                    ·
                      rfl

theorem cell22_3157123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 3].length) (baseStart_3157123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157123 prefixEnd_3157123 := by exact prefixLift 3157123
  have htrace : WordTrace (prefixWord ++ tailWord_3157123) baseStart_3157123 baseEnd_3157123 := by
    simpa [prefixWord, tailWord_3157123, baseEnd_3157123] using wordTrace_append hprefix tailTrace_3157123
  have hstable : (prefixWord ++ tailWord_3157123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157123).length < 2 ^ (prefixWord ++ tailWord_3157123).sum := by decide
  have hdescent : baseEnd_3157123 < baseStart_3157123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157125 : List Nat := [1, 3, 1, 1, 7, 1, 1, 7]
def baseStart_3157125 : Nat := 118140960795 + 3157125 * 2 ^ 59
def prefixEnd_3157125 : Nat := 4983230072969 + 3 ^ 40 * 3157125 * 2
def baseEnd_3157125 : Nat := 120083156394523367971715

theorem tailTrace_3157125 : CollatzResearch.WordTrace tailWord_3157125 prefixEnd_3157125 120083156394523367971715 := by
  unfold tailWord_3157125
  simp only [CollatzResearch.WordTrace]
  refine ⟨115149808687282793867680829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76766539124855195911787219 115149808687282793867680829)
  ·
    refine ⟨43181178257731047700380311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115149808687282793867680829 43181178257731047700380311)
    ·
      refine ⟨64771767386596571550570467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43181178257731047700380311 64771767386596571550570467)
      ·
        refine ⟨97157651079894857325855701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64771767386596571550570467 97157651079894857325855701)
        ·
          refine ⟨2277132447185035718574743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 97157651079894857325855701 2277132447185035718574743)
          ·
            refine ⟨3415698670777553577862115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2277132447185035718574743 3415698670777553577862115)
            ·
              refine ⟨5123548006166330366793173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3415698670777553577862115 5123548006166330366793173)
              ·
                refine ⟨120083156394523367971715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5123548006166330366793173 120083156394523367971715)
                ·
                  rfl

theorem cell22_3157125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 7].length) (baseStart_3157125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157125 prefixEnd_3157125 := by exact prefixLift 3157125
  have htrace : WordTrace (prefixWord ++ tailWord_3157125) baseStart_3157125 baseEnd_3157125 := by
    simpa [prefixWord, tailWord_3157125, baseEnd_3157125] using wordTrace_append hprefix tailTrace_3157125
  have hstable : (prefixWord ++ tailWord_3157125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157125).length < 2 ^ (prefixWord ++ tailWord_3157125).sum := by decide
  have hdescent : baseEnd_3157125 < baseStart_3157125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157157 : List Nat := [1, 3, 1, 2, 1, 5, 2, 3, 1, 3]
def baseStart_3157157 : Nat := 118140960795 + 3157157 * 2 ^ 59
def prefixEnd_3157157 : Nat := 4983230072969 + 3 ^ 40 * 3157157 * 2
def baseEnd_3157157 : Nat := 1080759361804672894945337

theorem tailTrace_3157157 : CollatzResearch.WordTrace tailWord_3157157 prefixEnd_3157157 1080759361804672894945337 := by
  unfold tailWord_3157157
  simp only [CollatzResearch.WordTrace]
  refine ⟨115150975823166863332845725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76767317215444575555230483 115150975823166863332845725)
  ·
    refine ⟨43181615933687573749817147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115150975823166863332845725 43181615933687573749817147)
    ·
      refine ⟨64772423900531360624725721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43181615933687573749817147 64772423900531360624725721)
      ·
        refine ⟨48579317925398520468544291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64772423900531360624725721 48579317925398520468544291)
        ·
          refine ⟨72868976888097780702816437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48579317925398520468544291 72868976888097780702816437)
          ·
            refine ⟨6831466583259166940889041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72868976888097780702816437 6831466583259166940889041)
            ·
              refine ⟨5123599937444375205666781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6831466583259166940889041 5123599937444375205666781)
              ·
                refine ⟨1921349976541640702125043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5123599937444375205666781 1921349976541640702125043)
                ·
                  refine ⟨2882024964812461053187565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1921349976541640702125043 2882024964812461053187565)
                  ·
                    refine ⟨1080759361804672894945337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2882024964812461053187565 1080759361804672894945337)
                    ·
                      rfl

theorem cell22_3157157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_3157157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157157 prefixEnd_3157157 := by exact prefixLift 3157157
  have htrace : WordTrace (prefixWord ++ tailWord_3157157) baseStart_3157157 baseEnd_3157157 := by
    simpa [prefixWord, tailWord_3157157, baseEnd_3157157] using wordTrace_append hprefix tailTrace_3157157
  have hstable : (prefixWord ++ tailWord_3157157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157157).length < 2 ^ (prefixWord ++ tailWord_3157157).sum := by decide
  have hdescent : baseEnd_3157157 < baseStart_3157157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157170 : List Nat := [3, 2, 1, 1, 1, 6, 1, 2, 5]
def baseStart_3157170 : Nat := 118140960795 + 3157170 * 2 ^ 59
def prefixEnd_3157170 : Nat := 4983230072969 + 3 ^ 40 * 3157170 * 2
def baseEnd_3157170 : Nat := 360254603990115064790099

theorem tailTrace_3157170 : CollatzResearch.WordTrace tailWord_3157170 prefixEnd_3157170 360254603990115064790099 := by
  unfold tailWord_3157170
  simp only [CollatzResearch.WordTrace]
  refine ⟨28787862493029941638267241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76767633314746511035379309 28787862493029941638267241)
  ·
    refine ⟨21590896869772456228700431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28787862493029941638267241 21590896869772456228700431)
    ·
      refine ⟨32386345304658684343050647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21590896869772456228700431 32386345304658684343050647)
      ·
        refine ⟨48579517956988026514575971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32386345304658684343050647 48579517956988026514575971)
        ·
          refine ⟨72869276935482039771863957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48579517956988026514575971 72869276935482039771863957)
          ·
            refine ⟨3415747356350720614306123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72869276935482039771863957 3415747356350720614306123)
            ·
              refine ⟨5123621034526080921459185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3415747356350720614306123 5123621034526080921459185)
              ·
                refine ⟨3842715775894560691094389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5123621034526080921459185 3842715775894560691094389)
                ·
                  refine ⟨360254603990115064790099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3842715775894560691094389 360254603990115064790099)
                  ·
                    rfl

theorem cell22_3157170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_3157170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157170 prefixEnd_3157170 := by exact prefixLift 3157170
  have htrace : WordTrace (prefixWord ++ tailWord_3157170) baseStart_3157170 baseEnd_3157170 := by
    simpa [prefixWord, tailWord_3157170, baseEnd_3157170] using wordTrace_append hprefix tailTrace_3157170
  have hstable : (prefixWord ++ tailWord_3157170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157170).length < 2 ^ (prefixWord ++ tailWord_3157170).sum := by decide
  have hdescent : baseEnd_3157170 < baseStart_3157170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157185 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3157185 : Nat := 118140960795 + 3157185 * 2 ^ 59
def prefixEnd_3157185 : Nat := 4983230072969 + 3 ^ 40 * 3157185 * 2
def baseEnd_3157185 : Nat := 1080768946776890155245251

theorem tailTrace_3157185 : CollatzResearch.WordTrace tailWord_3157185 prefixEnd_3157185 1080768946776890155245251 := by
  unfold tailWord_3157185
  simp only [CollatzResearch.WordTrace]
  refine ⟨115151997067065424114865009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76767998044710282743243339 115151997067065424114865009)
  ·
    refine ⟨86363997800299068086148757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115151997067065424114865009 86363997800299068086148757)
    ·
      refine ⟨4048312396889018816538223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86363997800299068086148757 4048312396889018816538223)
      ·
        refine ⟨6072468595333528224807335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4048312396889018816538223 6072468595333528224807335)
        ·
          refine ⟨9108702893000292337211003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6072468595333528224807335 9108702893000292337211003)
          ·
            refine ⟨13663054339500438505816505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9108702893000292337211003 13663054339500438505816505)
            ·
              refine ⟨10247290754625328879362379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13663054339500438505816505 10247290754625328879362379)
              ·
                refine ⟨15370936131937993319043569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10247290754625328879362379 15370936131937993319043569)
                ·
                  refine ⟨11528202098953494989282677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15370936131937993319043569 11528202098953494989282677)
                  ·
                    refine ⟨1080768946776890155245251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11528202098953494989282677 1080768946776890155245251)
                    ·
                      rfl

theorem cell22_3157185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3157185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157185 prefixEnd_3157185 := by exact prefixLift 3157185
  have htrace : WordTrace (prefixWord ++ tailWord_3157185) baseStart_3157185 baseEnd_3157185 := by
    simpa [prefixWord, tailWord_3157185, baseEnd_3157185] using wordTrace_append hprefix tailTrace_3157185
  have hstable : (prefixWord ++ tailWord_3157185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157185).length < 2 ^ (prefixWord ++ tailWord_3157185).sum := by decide
  have hdescent : baseEnd_3157185 < baseStart_3157185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157211 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 5, 6]
def baseStart_3157211 : Nat := 118140960795 + 3157211 * 2 ^ 59
def prefixEnd_3157211 : Nat := 4983230072969 + 3 ^ 40 * 3157211 * 2
def baseEnd_3157211 : Nat := 1080777847108234754095171

theorem tailTrace_3157211 : CollatzResearch.WordTrace tailWord_3157211 prefixEnd_3157211 1080777847108234754095171 := by
  unfold tailWord_3157211
  simp only [CollatzResearch.WordTrace]
  refine ⟨115152945364971230555311487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76768630243314153703540991 115152945364971230555311487)
  ·
    refine ⟨172729418047456845832967231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115152945364971230555311487 172729418047456845832967231)
    ·
      refine ⟨259094127071185268749450847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172729418047456845832967231 259094127071185268749450847)
      ·
        refine ⟨388641190606777903124176271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259094127071185268749450847 388641190606777903124176271)
        ·
          refine ⟨582961785910166854686264407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388641190606777903124176271 582961785910166854686264407)
          ·
            refine ⟨874442678865250282029396611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582961785910166854686264407 874442678865250282029396611)
            ·
              refine ⟨1311664018297875423044094917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874442678865250282029396611 1311664018297875423044094917)
              ·
                refine ⟨245937003430851641820767797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1311664018297875423044094917 245937003430851641820767797)
                ·
                  refine ⟨23056594071642341420696981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 245937003430851641820767797 23056594071642341420696981)
                  ·
                    refine ⟨1080777847108234754095171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23056594071642341420696981 1080777847108234754095171)
                    ·
                      rfl

theorem cell22_3157211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 6].length) (baseStart_3157211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157211 prefixEnd_3157211 := by exact prefixLift 3157211
  have htrace : WordTrace (prefixWord ++ tailWord_3157211) baseStart_3157211 baseEnd_3157211 := by
    simpa [prefixWord, tailWord_3157211, baseEnd_3157211] using wordTrace_append hprefix tailTrace_3157211
  have hstable : (prefixWord ++ tailWord_3157211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157211).length < 2 ^ (prefixWord ++ tailWord_3157211).sum := by decide
  have hdescent : baseEnd_3157211 < baseStart_3157211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157215 : List Nat := [1, 1, 2, 3, 2, 1, 5, 3, 4]
def baseStart_3157215 : Nat := 118140960795 + 3157215 * 2 ^ 59
def prefixEnd_3157215 : Nat := 4983230072969 + 3 ^ 40 * 3157215 * 2
def baseEnd_3157215 : Nat := 360259738796660025665053

theorem tailTrace_3157215 : CollatzResearch.WordTrace tailWord_3157215 prefixEnd_3157215 360259738796660025665053 := by
  unfold tailWord_3157215
  simp only [CollatzResearch.WordTrace]
  refine ⟨115153091256956739238457099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76768727504637826158971399 115153091256956739238457099)
  ·
    refine ⟨172729636885435108857685649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115153091256956739238457099 172729636885435108857685649)
    ·
      refine ⟨129547227664076331643264237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172729636885435108857685649 129547227664076331643264237)
      ·
        refine ⟨48580210374028624366224089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129547227664076331643264237 48580210374028624366224089)
        ·
          refine ⟨36435157780521468274668067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48580210374028624366224089 36435157780521468274668067)
          ·
            refine ⟨54652736670782202412002101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36435157780521468274668067 54652736670782202412002101)
            ·
              refine ⟨5123694062885831476125197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54652736670782202412002101 5123694062885831476125197)
              ·
                refine ⟨1921385273582186803546949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5123694062885831476125197 1921385273582186803546949)
                ·
                  refine ⟨360259738796660025665053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1921385273582186803546949 360259738796660025665053)
                  ·
                    rfl

theorem cell22_3157215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 4].length) (baseStart_3157215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157215 prefixEnd_3157215 := by exact prefixLift 3157215
  have htrace : WordTrace (prefixWord ++ tailWord_3157215) baseStart_3157215 baseEnd_3157215 := by
    simpa [prefixWord, tailWord_3157215, baseEnd_3157215] using wordTrace_append hprefix tailTrace_3157215
  have hstable : (prefixWord ++ tailWord_3157215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157215).length < 2 ^ (prefixWord ++ tailWord_3157215).sum := by decide
  have hdescent : baseEnd_3157215 < baseStart_3157215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157228 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_3157228 : Nat := 118140960795 + 3157228 * 2 ^ 59
def prefixEnd_3157228 : Nat := 4983230072969 + 3 ^ 40 * 3157228 * 2
def baseEnd_3157228 : Nat := 1080783666555652376420119

theorem tailTrace_3157228 : CollatzResearch.WordTrace tailWord_3157228 prefixEnd_3157228 1080783666555652376420119 := by
  unfold tailWord_3157228
  simp only [CollatzResearch.WordTrace]
  refine ⟨57576782702954821229340169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76769043603939761639120225 57576782702954821229340169)
  ·
    refine ⟨43182587027216115922005127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57576782702954821229340169 43182587027216115922005127)
    ·
      refine ⟨64773880540824173883007691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43182587027216115922005127 64773880540824173883007691)
      ·
        refine ⟨97160820811236260824511537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64773880540824173883007691 97160820811236260824511537)
        ·
          refine ⟨72870615608427195618383653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97160820811236260824511537 72870615608427195618383653)
          ·
            refine ⟨13663240426580099178446935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72870615608427195618383653 13663240426580099178446935)
            ·
              refine ⟨20494860639870148767670403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13663240426580099178446935 20494860639870148767670403)
              ·
                refine ⟨30742290959805223151505605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20494860639870148767670403 30742290959805223151505605)
                ·
                  refine ⟨5764179554963479340907301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30742290959805223151505605 5764179554963479340907301)
                  ·
                    refine ⟨1080783666555652376420119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5764179554963479340907301 1080783666555652376420119)
                    ·
                      rfl

theorem cell22_3157228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_3157228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157228 prefixEnd_3157228 := by exact prefixLift 3157228
  have htrace : WordTrace (prefixWord ++ tailWord_3157228) baseStart_3157228 baseEnd_3157228 := by
    simpa [prefixWord, tailWord_3157228, baseEnd_3157228] using wordTrace_append hprefix tailTrace_3157228
  have hstable : (prefixWord ++ tailWord_3157228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157228).length < 2 ^ (prefixWord ++ tailWord_3157228).sum := by decide
  have hdescent : baseEnd_3157228 < baseStart_3157228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157230 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_3157230 : Nat := 118140960795 + 3157230 * 2 ^ 59
def prefixEnd_3157230 : Nat := 4983230072969 + 3 ^ 40 * 3157230 * 2
def baseEnd_3157230 : Nat := 1080784351196525037870113

theorem tailTrace_3157230 : CollatzResearch.WordTrace tailWord_3157230 prefixEnd_3157230 1080784351196525037870113 := by
  unfold tailWord_3157230
  simp only [CollatzResearch.WordTrace]
  refine ⟨14394204793987799600031643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76769092234601597866835429 14394204793987799600031643)
  ·
    refine ⟨21591307190981699400047465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14394204793987799600031643 21591307190981699400047465)
    ·
      refine ⟨16193480393236274550035599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21591307190981699400047465 16193480393236274550035599)
      ·
        refine ⟨24290220589854411825053399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16193480393236274550035599 24290220589854411825053399)
        ·
          refine ⟨36435330884781617737580099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24290220589854411825053399 36435330884781617737580099)
          ·
            refine ⟨54652996327172426606370149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36435330884781617737580099 54652996327172426606370149)
            ·
              refine ⟨10247436811344829988694403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54652996327172426606370149 10247436811344829988694403)
              ·
                refine ⟨15371155217017244983041605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10247436811344829988694403 15371155217017244983041605)
                ·
                  refine ⟨2882091603190733434320301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15371155217017244983041605 2882091603190733434320301)
                  ·
                    refine ⟨1080784351196525037870113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2882091603190733434320301 1080784351196525037870113)
                    ·
                      rfl

theorem cell22_3157230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_3157230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157230 prefixEnd_3157230 := by exact prefixLift 3157230
  have htrace : WordTrace (prefixWord ++ tailWord_3157230) baseStart_3157230 baseEnd_3157230 := by
    simpa [prefixWord, tailWord_3157230, baseEnd_3157230] using wordTrace_append hprefix tailTrace_3157230
  have hstable : (prefixWord ++ tailWord_3157230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157230).length < 2 ^ (prefixWord ++ tailWord_3157230).sum := by decide
  have hdescent : baseEnd_3157230 < baseStart_3157230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157247 : List Nat := [1, 1, 2, 2, 1, 5, 4, 1, 2, 3]
def baseStart_3157247 : Nat := 118140960795 + 3157247 * 2 ^ 59
def prefixEnd_3157247 : Nat := 4983230072969 + 3 ^ 40 * 3157247 * 2
def baseEnd_3157247 : Nat := 1080790170643942660195061

theorem tailTrace_3157247 : CollatzResearch.WordTrace tailWord_3157247 prefixEnd_3157247 1080790170643942660195061 := by
  unfold tailWord_3157247
  simp only [CollatzResearch.WordTrace]
  refine ⟨115154258392840808703621995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76769505595227205802414663 115154258392840808703621995)
  ·
    refine ⟨172731387589261213055432993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115154258392840808703621995 172731387589261213055432993)
    ·
      refine ⟨129548540691945909791574745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172731387589261213055432993 129548540691945909791574745)
      ·
        refine ⟨97161405518959432343681059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129548540691945909791574745 97161405518959432343681059)
        ·
          refine ⟨145742108278439148515521589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97161405518959432343681059 145742108278439148515521589)
          ·
            refine ⟨13663322651103670173330149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145742108278439148515521589 13663322651103670173330149)
            ·
              refine ⟨2561872997081938157499403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13663322651103670173330149 2561872997081938157499403)
              ·
                refine ⟨3842809495622907236249105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2561872997081938157499403 3842809495622907236249105)
                ·
                  refine ⟨2882107121717180427186829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3842809495622907236249105 2882107121717180427186829)
                  ·
                    refine ⟨1080790170643942660195061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2882107121717180427186829 1080790170643942660195061)
                    ·
                      rfl

theorem cell22_3157247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 2, 3].length) (baseStart_3157247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157247 prefixEnd_3157247 := by exact prefixLift 3157247
  have htrace : WordTrace (prefixWord ++ tailWord_3157247) baseStart_3157247 baseEnd_3157247 := by
    simpa [prefixWord, tailWord_3157247, baseEnd_3157247] using wordTrace_append hprefix tailTrace_3157247
  have hstable : (prefixWord ++ tailWord_3157247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157247).length < 2 ^ (prefixWord ++ tailWord_3157247).sum := by decide
  have hdescent : baseEnd_3157247 < baseStart_3157247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157290 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3157290 : Nat := 118140960795 + 3157290 * 2 ^ 59
def prefixEnd_3157290 : Nat := 4983230072969 + 3 ^ 40 * 3157290 * 2
def baseEnd_3157290 : Nat := 1080804890422704881369929

theorem tailTrace_3157290 : CollatzResearch.WordTrace tailWord_3157290 prefixEnd_3157290 1080804890422704881369929 := by
  unfold tailWord_3157290
  simp only [CollatzResearch.WordTrace]
  refine ⟨28788956682921256761859331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76770551154456684698291549 28788956682921256761859331)
  ·
    refine ⟨43183435024381885142788997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28788956682921256761859331 43183435024381885142788997)
    ·
      refine ⟨8096894067071603464272937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43183435024381885142788997 8096894067071603464272937)
      ·
        refine ⟨6072670550303702598204703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8096894067071603464272937 6072670550303702598204703)
        ·
          refine ⟨9109005825455553897307055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6072670550303702598204703 9109005825455553897307055)
          ·
            refine ⟨13663508738183330845960583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9109005825455553897307055 13663508738183330845960583)
            ·
              refine ⟨20495263107274996268940875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13663508738183330845960583 20495263107274996268940875)
              ·
                refine ⟨30742894660912494403411313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20495263107274996268940875 30742894660912494403411313)
                ·
                  refine ⟨23057170995684370802558485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30742894660912494403411313 23057170995684370802558485)
                  ·
                    refine ⟨1080804890422704881369929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23057170995684370802558485 1080804890422704881369929)
                    ·
                      rfl

theorem cell22_3157290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3157290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157290 prefixEnd_3157290 := by exact prefixLift 3157290
  have htrace : WordTrace (prefixWord ++ tailWord_3157290) baseStart_3157290 baseEnd_3157290 := by
    simpa [prefixWord, tailWord_3157290, baseEnd_3157290] using wordTrace_append hprefix tailTrace_3157290
  have hstable : (prefixWord ++ tailWord_3157290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157290).length < 2 ^ (prefixWord ++ tailWord_3157290).sum := by decide
  have hdescent : baseEnd_3157290 < baseStart_3157290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157309 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_3157309 : Nat := 118140960795 + 3157309 * 2 ^ 59
def prefixEnd_3157309 : Nat := 4983230072969 + 3 ^ 40 * 3157309 * 2
def baseEnd_3157309 : Nat := 1080811394510995165144871

theorem tailTrace_3157309 : CollatzResearch.WordTrace tailWord_3157309 prefixEnd_3157309 1080811394510995165144871 := by
  unfold tailWord_3157309
  simp only [CollatzResearch.WordTrace]
  refine ⟨115156519718616193292378981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76771013145744128861585987 115156519718616193292378981)
  ·
    refine ⟨21591847447240536242321059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115156519718616193292378981 21591847447240536242321059)
    ·
      refine ⟨32387771170860804363481589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21591847447240536242321059 32387771170860804363481589)
      ·
        refine ⟨3036353547268200409076399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32387771170860804363481589 3036353547268200409076399)
        ·
          refine ⟨4554530320902300613614599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3036353547268200409076399 4554530320902300613614599)
          ·
            refine ⟨6831795481353450920421899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554530320902300613614599 6831795481353450920421899)
            ·
              refine ⟨10247693222030176380632849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6831795481353450920421899 10247693222030176380632849)
              ·
                refine ⟨7685769916522632285474637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10247693222030176380632849 7685769916522632285474637)
                ·
                  refine ⟨2882163718695987107052989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7685769916522632285474637 2882163718695987107052989)
                  ·
                    refine ⟨1080811394510995165144871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2882163718695987107052989 1080811394510995165144871)
                    ·
                      rfl

theorem cell22_3157309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_3157309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157309 prefixEnd_3157309 := by exact prefixLift 3157309
  have htrace : WordTrace (prefixWord ++ tailWord_3157309) baseStart_3157309 baseEnd_3157309 := by
    simpa [prefixWord, tailWord_3157309, baseEnd_3157309] using wordTrace_append hprefix tailTrace_3157309
  have hstable : (prefixWord ++ tailWord_3157309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157309).length < 2 ^ (prefixWord ++ tailWord_3157309).sum := by decide
  have hdescent : baseEnd_3157309 < baseStart_3157309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157380 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_3157380 : Nat := 118140960795 + 3157380 * 2 ^ 59
def prefixEnd_3157380 : Nat := 4983230072969 + 3 ^ 40 * 3157380 * 2
def baseEnd_3157380 : Nat := 1080835699261974646619653

theorem tailTrace_3157380 : CollatzResearch.WordTrace tailWord_3157380 prefixEnd_3157380 1080835699261974646619653 := by
  unfold tailWord_3157380
  simp only [CollatzResearch.WordTrace]
  refine ⟨57579554650679486209106797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76772739534239314945475729 57579554650679486209106797)
  ·
    refine ⟨21592332994004807328415049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57579554650679486209106797 21592332994004807328415049)
    ·
      refine ⟨16194249745503605496311287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21592332994004807328415049 16194249745503605496311287)
      ·
        refine ⟨24291374618255408244466931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16194249745503605496311287 24291374618255408244466931)
        ·
          refine ⟨36437061927383112366700397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24291374618255408244466931 36437061927383112366700397)
          ·
            refine ⟨13663898222768667137512649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36437061927383112366700397 13663898222768667137512649)
            ·
              refine ⟨10247923667076500353134487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13663898222768667137512649 10247923667076500353134487)
              ·
                refine ⟨15371885500614750529701731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10247923667076500353134487 15371885500614750529701731)
                ·
                  refine ⟨23057828250922125794552597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15371885500614750529701731 23057828250922125794552597)
                  ·
                    refine ⟨1080835699261974646619653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23057828250922125794552597 1080835699261974646619653)
                    ·
                      rfl

theorem cell22_3157380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_3157380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157380 prefixEnd_3157380 := by exact prefixLift 3157380
  have htrace : WordTrace (prefixWord ++ tailWord_3157380) baseStart_3157380 baseEnd_3157380 := by
    simpa [prefixWord, tailWord_3157380, baseEnd_3157380] using wordTrace_append hprefix tailTrace_3157380
  have hstable : (prefixWord ++ tailWord_3157380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157380).length < 2 ^ (prefixWord ++ tailWord_3157380).sum := by decide
  have hdescent : baseEnd_3157380 < baseStart_3157380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157384 : List Nat := [2, 1, 3, 3, 1, 4, 1, 3, 4]
def baseStart_3157384 : Nat := 118140960795 + 3157384 * 2 ^ 59
def prefixEnd_3157384 : Nat := 4983230072969 + 3 ^ 40 * 3157384 * 2
def baseEnd_3157384 : Nat := 360279022847906656506547

theorem tailTrace_3157384 : CollatzResearch.WordTrace tailWord_3157384 prefixEnd_3157384 360279022847906656506547 := by
  unfold tailWord_3157384
  simp only [CollatzResearch.WordTrace]
  refine ⟨57579627596672240550679603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76772836795562987400906137 57579627596672240550679603)
  ·
    refine ⟨86369441395008360826019405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57579627596672240550679603 86369441395008360826019405)
    ·
      refine ⟨32388540523128135309757277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86369441395008360826019405 32388540523128135309757277)
      ·
        refine ⟨12145702696173050741158979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32388540523128135309757277 12145702696173050741158979)
        ·
          refine ⟨18218554044259576111738469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12145702696173050741158979 18218554044259576111738469)
          ·
            refine ⟨3415978883298670520950963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18218554044259576111738469 3415978883298670520950963)
            ·
              refine ⟨5123968324948005781426445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3415978883298670520950963 5123968324948005781426445)
              ·
                refine ⟨1921488121855502168034917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5123968324948005781426445 1921488121855502168034917)
                ·
                  refine ⟨360279022847906656506547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1921488121855502168034917 360279022847906656506547)
                  ·
                    rfl

theorem cell22_3157384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 4].length) (baseStart_3157384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157384 prefixEnd_3157384 := by exact prefixLift 3157384
  have htrace : WordTrace (prefixWord ++ tailWord_3157384) baseStart_3157384 baseEnd_3157384 := by
    simpa [prefixWord, tailWord_3157384, baseEnd_3157384] using wordTrace_append hprefix tailTrace_3157384
  have hstable : (prefixWord ++ tailWord_3157384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157384).length < 2 ^ (prefixWord ++ tailWord_3157384).sum := by decide
  have hdescent : baseEnd_3157384 < baseStart_3157384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157393 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 1, 9]
def baseStart_3157393 : Nat := 118140960795 + 3157393 * 2 ^ 59
def prefixEnd_3157393 : Nat := 4983230072969 + 3 ^ 40 * 3157393 * 2
def baseEnd_3157393 : Nat := 1080840149427646946044613

theorem tailTrace_3157393 : CollatzResearch.WordTrace tailWord_3157393 prefixEnd_3157393 1080840149427646946044613 := by
  unfold tailWord_3157393
  simp only [CollatzResearch.WordTrace]
  refine ⟨115159583450311875638436833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76773055633541250425624555 115159583450311875638436833)
  ·
    refine ⟨86369687587733906728827625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115159583450311875638436833 86369687587733906728827625)
    ·
      refine ⟨64777265690800430046620719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86369687587733906728827625 64777265690800430046620719)
      ·
        refine ⟨97165898536200645069931079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64777265690800430046620719 97165898536200645069931079)
        ·
          refine ⟨145748847804300967604896619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97165898536200645069931079 145748847804300967604896619)
          ·
            refine ⟨218623271706451451407344929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145748847804300967604896619 218623271706451451407344929)
            ·
              refine ⟨163967453779838588555508697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218623271706451451407344929 163967453779838588555508697)
              ·
                refine ⟨122975590334878941416631523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163967453779838588555508697 122975590334878941416631523)
                ·
                  refine ⟨184463385502318412124947285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122975590334878941416631523 184463385502318412124947285)
                  ·
                    refine ⟨1080840149427646946044613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 184463385502318412124947285 1080840149427646946044613)
                    ·
                      rfl

theorem cell22_3157393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_3157393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157393 prefixEnd_3157393 := by exact prefixLift 3157393
  have htrace : WordTrace (prefixWord ++ tailWord_3157393) baseStart_3157393 baseEnd_3157393 := by
    simpa [prefixWord, tailWord_3157393, baseEnd_3157393] using wordTrace_append hprefix tailTrace_3157393
  have hstable : (prefixWord ++ tailWord_3157393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157393).length < 2 ^ (prefixWord ++ tailWord_3157393).sum := by decide
  have hdescent : baseEnd_3157393 < baseStart_3157393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157416 : List Nat := [2, 1, 6, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3157416 : Nat := 118140960795 + 3157416 * 2 ^ 59
def prefixEnd_3157416 : Nat := 4983230072969 + 3 ^ 40 * 3157416 * 2
def baseEnd_3157416 : Nat := 1080848022797682552719543

theorem tailTrace_3157416 : CollatzResearch.WordTrace tailWord_3157416 prefixEnd_3157416 1080848022797682552719543 := by
  unfold tailWord_3157416
  simp only [CollatzResearch.WordTrace]
  refine ⟨57580211164614275283262051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76773614886152367044349401 57580211164614275283262051)
  ·
    refine ⟨86370316746921412924893077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57580211164614275283262051 86370316746921412924893077)
    ·
      refine ⟨4048608597511941230854363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 86370316746921412924893077 4048608597511941230854363)
      ·
        refine ⟨6072912896267911846281545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4048608597511941230854363 6072912896267911846281545)
        ·
          refine ⟨4554684672200933884711159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6072912896267911846281545 4554684672200933884711159)
          ·
            refine ⟨6832027008301400827066739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554684672200933884711159 6832027008301400827066739)
            ·
              refine ⟨10248040512452101240600109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6832027008301400827066739 10248040512452101240600109)
              ·
                refine ⟨3843015192169537965225041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10248040512452101240600109 3843015192169537965225041)
                ·
                  refine ⟨2882261394127153473918781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3843015192169537965225041 2882261394127153473918781)
                  ·
                    refine ⟨1080848022797682552719543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2882261394127153473918781 1080848022797682552719543)
                    ·
                      rfl

theorem cell22_3157416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3157416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157416 prefixEnd_3157416 := by exact prefixLift 3157416
  have htrace : WordTrace (prefixWord ++ tailWord_3157416) baseStart_3157416 baseEnd_3157416 := by
    simpa [prefixWord, tailWord_3157416, baseEnd_3157416] using wordTrace_append hprefix tailTrace_3157416
  have hstable : (prefixWord ++ tailWord_3157416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157416).length < 2 ^ (prefixWord ++ tailWord_3157416).sum := by decide
  have hdescent : baseEnd_3157416 < baseStart_3157416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157530 : List Nat := [3, 1, 1, 3, 1, 1, 1, 11]
def baseStart_3157530 : Nat := 118140960795 + 3157530 * 2 ^ 59
def prefixEnd_3157530 : Nat := 4983230072969 + 3 ^ 40 * 3157530 * 2
def baseEnd_3157530 : Nat := 120098560814158250596577

theorem tailTrace_3157530 : CollatzResearch.WordTrace tailWord_3157530 prefixEnd_3157530 120098560814158250596577 := by
  unfold tailWord_3157530
  simp only [CollatzResearch.WordTrace]
  refine ⟨28791145062703887009043511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76776386833877032024116029 28791145062703887009043511)
  ·
    refine ⟨43186717594055830513565267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28791145062703887009043511 43186717594055830513565267)
    ·
      refine ⟨64780076391083745770347901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43186717594055830513565267 64780076391083745770347901)
      ·
        refine ⟨24292528646656404663880463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64780076391083745770347901 24292528646656404663880463)
        ·
          refine ⟨36438792969984606995820695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24292528646656404663880463 36438792969984606995820695)
          ·
            refine ⟨54658189454976910493731043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36438792969984606995820695 54658189454976910493731043)
            ·
              refine ⟨81987284182465365740596565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54658189454976910493731043 81987284182465365740596565)
              ·
                refine ⟨120098560814158250596577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 81987284182465365740596565 120098560814158250596577)
                ·
                  rfl

theorem cell22_3157530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_3157530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157530 prefixEnd_3157530 := by exact prefixLift 3157530
  have htrace : WordTrace (prefixWord ++ tailWord_3157530) baseStart_3157530 baseEnd_3157530 := by
    simpa [prefixWord, tailWord_3157530, baseEnd_3157530] using wordTrace_append hprefix tailTrace_3157530
  have hstable : (prefixWord ++ tailWord_3157530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157530).length < 2 ^ (prefixWord ++ tailWord_3157530).sum := by decide
  have hdescent : baseEnd_3157530 < baseStart_3157530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157564 : List Nat := [2, 2, 2, 2, 5, 1, 8]
def baseStart_3157564 : Nat := 118140960795 + 3157564 * 2 ^ 59
def prefixEnd_3157564 : Nat := 4983230072969 + 3 ^ 40 * 3157564 * 2
def baseEnd_3157564 : Nat := 40033284674898500000707

theorem tailTrace_3157564 : CollatzResearch.WordTrace tailWord_3157564 prefixEnd_3157564 40033284674898500000707 := by
  unfold tailWord_3157564
  simp only [CollatzResearch.WordTrace]
  refine ⟨57582910166346185921455873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76777213555128247895274497 57582910166346185921455873)
  ·
    refine ⟨43187182624759639441091905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57582910166346185921455873 43187182624759639441091905)
    ·
      refine ⟨32390386968569729580818929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43187182624759639441091905 32390386968569729580818929)
      ·
        refine ⟨24292790226427297185614197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32390386968569729580818929 24292790226427297185614197)
        ·
          refine ⟨2277449083727559111151331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24292790226427297185614197 2277449083727559111151331)
          ·
            refine ⟨3416173625591338666726997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2277449083727559111151331 3416173625591338666726997)
            ·
              refine ⟨40033284674898500000707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3416173625591338666726997 40033284674898500000707)
              ·
                rfl

theorem cell22_3157564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 8].length) (baseStart_3157564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157564 prefixEnd_3157564 := by exact prefixLift 3157564
  have htrace : WordTrace (prefixWord ++ tailWord_3157564) baseStart_3157564 baseEnd_3157564 := by
    simpa [prefixWord, tailWord_3157564, baseEnd_3157564] using wordTrace_append hprefix tailTrace_3157564
  have hstable : (prefixWord ++ tailWord_3157564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157564).length < 2 ^ (prefixWord ++ tailWord_3157564).sum := by decide
  have hdescent : baseEnd_3157564 < baseStart_3157564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157637 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 6]
def baseStart_3157637 : Nat := 118140960795 + 3157637 * 2 ^ 59
def prefixEnd_3157637 : Nat := 4983230072969 + 3 ^ 40 * 3157637 * 2
def baseEnd_3157637 : Nat := 360307891871370547647955

theorem tailTrace_3157637 : CollatzResearch.WordTrace tailWord_3157637 prefixEnd_3157637 360307891871370547647955 := by
  unfold tailWord_3157637
  simp only [CollatzResearch.WordTrace]
  refine ⟨115168482861427905310319165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76778988574285270206879443 115168482861427905310319165)
  ·
    refine ⟨43188181073035464491369687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115168482861427905310319165 43188181073035464491369687)
    ·
      refine ⟨64782271609553196737054531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43188181073035464491369687 64782271609553196737054531)
      ·
        refine ⟨97173407414329795105581797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64782271609553196737054531 97173407414329795105581797)
        ·
          refine ⟨18220013890186836582296587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97173407414329795105581797 18220013890186836582296587)
          ·
            refine ⟨27330020835280254873444881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18220013890186836582296587 27330020835280254873444881)
            ·
              refine ⟨20497515626460191155083661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27330020835280254873444881 20497515626460191155083661)
              ·
                refine ⟨7686568359922571683156373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20497515626460191155083661 7686568359922571683156373)
                ·
                  refine ⟨360307891871370547647955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7686568359922571683156373 360307891871370547647955)
                  ·
                    rfl

theorem cell22_3157637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_3157637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157637 prefixEnd_3157637 := by exact prefixLift 3157637
  have htrace : WordTrace (prefixWord ++ tailWord_3157637) baseStart_3157637 baseEnd_3157637 := by
    simpa [prefixWord, tailWord_3157637, baseEnd_3157637] using wordTrace_append hprefix tailTrace_3157637
  have hstable : (prefixWord ++ tailWord_3157637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157637).length < 2 ^ (prefixWord ++ tailWord_3157637).sum := by decide
  have hdescent : baseEnd_3157637 < baseStart_3157637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157667 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 1, 6]
def baseStart_3157667 : Nat := 118140960795 + 3157667 * 2 ^ 59
def prefixEnd_3157667 : Nat := 4983230072969 + 3 ^ 40 * 3157667 * 2
def baseEnd_3157667 : Nat := 1080933945227201564693773

theorem tailTrace_3157667 : CollatzResearch.WordTrace tailWord_3157667 prefixEnd_3157667 1080933945227201564693773 := by
  unfold tailWord_3157667
  simp only [CollatzResearch.WordTrace]
  refine ⟨115169577051319220433911255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76779718034212813622607503 115169577051319220433911255)
  ·
    refine ⟨172754365576978830650866883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115169577051319220433911255 172754365576978830650866883)
    ·
      refine ⟨259131548365468245976300325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172754365576978830650866883 259131548365468245976300325)
      ·
        refine ⟨48587165318525296120556311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259131548365468245976300325 48587165318525296120556311)
        ·
          refine ⟨72880747977787944180834467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48587165318525296120556311 72880747977787944180834467)
          ·
            refine ⟨109321121966681916271251701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72880747977787944180834467 109321121966681916271251701)
            ·
              refine ⟨10248855184376429650429847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109321121966681916271251701 10248855184376429650429847)
              ·
                refine ⟨15373282776564644475644771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10248855184376429650429847 15373282776564644475644771)
                ·
                  refine ⟨23059924164846966713467157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15373282776564644475644771 23059924164846966713467157)
                  ·
                    refine ⟨1080933945227201564693773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23059924164846966713467157 1080933945227201564693773)
                    ·
                      rfl

theorem cell22_3157667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 6].length) (baseStart_3157667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157667 prefixEnd_3157667 := by exact prefixLift 3157667
  have htrace : WordTrace (prefixWord ++ tailWord_3157667) baseStart_3157667 baseEnd_3157667 := by
    simpa [prefixWord, tailWord_3157667, baseEnd_3157667] using wordTrace_append hprefix tailTrace_3157667
  have hstable : (prefixWord ++ tailWord_3157667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157667).length < 2 ^ (prefixWord ++ tailWord_3157667).sum := by decide
  have hdescent : baseEnd_3157667 < baseStart_3157667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157716 : List Nat := [2, 4, 1, 3, 1, 1, 4, 6]
def baseStart_3157716 : Nat := 118140960795 + 3157716 * 2 ^ 59
def prefixEnd_3157716 : Nat := 4983230072969 + 3 ^ 40 * 3157716 * 2
def baseEnd_3157716 : Nat := 120105635436509085579847

theorem tailTrace_3157716 : CollatzResearch.WordTrace tailWord_3157716 prefixEnd_3157716 120105635436509085579847 := by
  unfold tailWord_3157716
  simp only [CollatzResearch.WordTrace]
  refine ⟨57585682114070850901222501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76780909485427801201630001 57585682114070850901222501)
  ·
    refine ⟨10797315396388284543979219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57585682114070850901222501 10797315396388284543979219)
    ·
      refine ⟨16195973094582426815968829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10797315396388284543979219 16195973094582426815968829)
      ·
        refine ⟨6073489910468410055988311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16195973094582426815968829 6073489910468410055988311)
        ·
          refine ⟨9110234865702615083982467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6073489910468410055988311 9110234865702615083982467)
          ·
            refine ⟨13665352298553922625973701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9110234865702615083982467 13665352298553922625973701)
            ·
              refine ⟨2562253555978860492370069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13665352298553922625973701 2562253555978860492370069)
              ·
                refine ⟨120105635436509085579847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2562253555978860492370069 120105635436509085579847)
                ·
                  rfl

theorem cell22_3157716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 6].length) (baseStart_3157716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157716 prefixEnd_3157716 := by exact prefixLift 3157716
  have htrace : WordTrace (prefixWord ++ tailWord_3157716) baseStart_3157716 baseEnd_3157716 := by
    simpa [prefixWord, tailWord_3157716, baseEnd_3157716] using wordTrace_append hprefix tailTrace_3157716
  have hstable : (prefixWord ++ tailWord_3157716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157716).length < 2 ^ (prefixWord ++ tailWord_3157716).sum := by decide
  have hdescent : baseEnd_3157716 < baseStart_3157716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157727 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 9]
def baseStart_3157727 : Nat := 118140960795 + 3157727 * 2 ^ 59
def prefixEnd_3157727 : Nat := 4983230072969 + 3 ^ 40 * 3157727 * 2
def baseEnd_3157727 : Nat := 360318161484460469397863

theorem tailTrace_3157727 : CollatzResearch.WordTrace tailWord_3157727 prefixEnd_3157727 360318161484460469397863 := by
  unfold tailWord_3157727
  simp only [CollatzResearch.WordTrace]
  refine ⟨115171765431101850681095435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76781176954067900454063623 115171765431101850681095435)
  ·
    refine ⟨172757648146652776021643153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115171765431101850681095435 172757648146652776021643153)
    ·
      refine ⟨129568236109989582016232365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172757648146652776021643153 129568236109989582016232365)
      ·
        refine ⟨48588088541246093256087137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129568236109989582016232365 48588088541246093256087137)
        ·
          refine ⟨36441066405934569942065353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48588088541246093256087137 36441066405934569942065353)
          ·
            refine ⟨27330799804450927456549015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36441066405934569942065353 27330799804450927456549015)
            ·
              refine ⟨40996199706676391184823523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27330799804450927456549015 40996199706676391184823523)
              ·
                refine ⟨61494299560014586777235285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40996199706676391184823523 61494299560014586777235285)
                ·
                  refine ⟨360318161484460469397863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61494299560014586777235285 360318161484460469397863)
                  ·
                    rfl

theorem cell22_3157727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 9].length) (baseStart_3157727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157727 prefixEnd_3157727 := by exact prefixLift 3157727
  have htrace : WordTrace (prefixWord ++ tailWord_3157727) baseStart_3157727 baseEnd_3157727 := by
    simpa [prefixWord, tailWord_3157727, baseEnd_3157727] using wordTrace_append hprefix tailTrace_3157727
  have hstable : (prefixWord ++ tailWord_3157727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157727).length < 2 ^ (prefixWord ++ tailWord_3157727).sum := by decide
  have hdescent : baseEnd_3157727 < baseStart_3157727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157761 : List Nat := [1, 2, 4, 1, 1, 1, 6, 1, 5]
def baseStart_3157761 : Nat := 118140960795 + 3157761 * 2 ^ 59
def prefixEnd_3157761 : Nat := 4983230072969 + 3 ^ 40 * 3157761 * 2
def baseEnd_3157761 : Nat := 360322041116072217614495

theorem tailTrace_3157761 : CollatzResearch.WordTrace tailWord_3157761 prefixEnd_3157761 360322041116072217614495 := by
  unfold tailWord_3157761
  simp only [CollatzResearch.WordTrace]
  refine ⟨115173005512978674487833137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76782003675319116325222091 115173005512978674487833137)
  ·
    refine ⟨86379754134734005865874853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115173005512978674487833137 86379754134734005865874853)
    ·
      refine ⟨16196203900262626099851535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86379754134734005865874853 16196203900262626099851535)
      ·
        refine ⟨24294305850393939149777303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16196203900262626099851535 24294305850393939149777303)
        ·
          refine ⟨36441458775590908724665955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24294305850393939149777303 36441458775590908724665955)
          ·
            refine ⟨54662188163386363086998933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36441458775590908724665955 54662188163386363086998933)
            ·
              refine ⟨2562290070158735769703075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54662188163386363086998933 2562290070158735769703075)
              ·
                refine ⟨3843435105238103654554613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562290070158735769703075 3843435105238103654554613)
                ·
                  refine ⟨360322041116072217614495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3843435105238103654554613 360322041116072217614495)
                  ·
                    rfl

theorem cell22_3157761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 5].length) (baseStart_3157761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157761 prefixEnd_3157761 := by exact prefixLift 3157761
  have htrace : WordTrace (prefixWord ++ tailWord_3157761) baseStart_3157761 baseEnd_3157761 := by
    simpa [prefixWord, tailWord_3157761, baseEnd_3157761] using wordTrace_append hprefix tailTrace_3157761
  have hstable : (prefixWord ++ tailWord_3157761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157761).length < 2 ^ (prefixWord ++ tailWord_3157761).sum := by decide
  have hdescent : baseEnd_3157761 < baseStart_3157761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157821 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_3157821 : Nat := 118140960795 + 3157821 * 2 ^ 59
def prefixEnd_3157821 : Nat := 4983230072969 + 3 ^ 40 * 3157821 * 2
def baseEnd_3157821 : Nat := 1080986662574396496343301

theorem tailTrace_3157821 : CollatzResearch.WordTrace tailWord_3157821 prefixEnd_3157821 1080986662574396496343301 := by
  unfold tailWord_3157821
  simp only [CollatzResearch.WordTrace]
  refine ⟨115175193892761304735017317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76783462595174203156678211 115175193892761304735017317)
  ·
    refine ⟨21595348854892744637815747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115175193892761304735017317 21595348854892744637815747)
    ·
      refine ⟨32393023282339116956723621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21595348854892744637815747 32393023282339116956723621)
      ·
        refine ⟨6073691865438584429385679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32393023282339116956723621 6073691865438584429385679)
        ·
          refine ⟨9110537798157876644078519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6073691865438584429385679 9110537798157876644078519)
          ·
            refine ⟨13665806697236814966117779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9110537798157876644078519 13665806697236814966117779)
            ·
              refine ⟨20498710045855222449176669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13665806697236814966117779 20498710045855222449176669)
              ·
                refine ⟨7687016267195708418441251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20498710045855222449176669 7687016267195708418441251)
                ·
                  refine ⟨11530524400793562627661877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7687016267195708418441251 11530524400793562627661877)
                  ·
                    refine ⟨1080986662574396496343301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11530524400793562627661877 1080986662574396496343301)
                    ·
                      rfl

theorem cell22_3157821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_3157821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157821 prefixEnd_3157821 := by exact prefixLift 3157821
  have htrace : WordTrace (prefixWord ++ tailWord_3157821) baseStart_3157821 baseEnd_3157821 := by
    simpa [prefixWord, tailWord_3157821, baseEnd_3157821] using wordTrace_append hprefix tailTrace_3157821
  have hstable : (prefixWord ++ tailWord_3157821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157821).length < 2 ^ (prefixWord ++ tailWord_3157821).sum := by decide
  have hdescent : baseEnd_3157821 < baseStart_3157821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157836 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 1, 6]
def baseStart_3157836 : Nat := 118140960795 + 3157836 * 2 ^ 59
def prefixEnd_3157836 : Nat := 4983230072969 + 3 ^ 40 * 3157836 * 2
def baseEnd_3157836 : Nat := 1080991797380941457218255

theorem tailTrace_3157836 : CollatzResearch.WordTrace tailWord_3157836 prefixEnd_3157836 1080991797380941457218255 := by
  unfold tailWord_3157836
  simp only [CollatzResearch.WordTrace]
  refine ⟨57587870493853481148406681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76783827325137974864542241 57587870493853481148406681)
  ·
    refine ⟨43190902870390110861305011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57587870493853481148406681 43190902870390110861305011)
    ·
      refine ⟨64786354305585166291957517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43190902870390110861305011 64786354305585166291957517)
      ·
        refine ⟨24294882864594437359484069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64786354305585166291957517 24294882864594437359484069)
        ·
          refine ⟨4555290537111457004903263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24294882864594437359484069 4555290537111457004903263)
          ·
            refine ⟨6832935805667185507354895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4555290537111457004903263 6832935805667185507354895)
            ·
              refine ⟨10249403708500778261032343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6832935805667185507354895 10249403708500778261032343)
              ·
                refine ⟨15374105562751167391548515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10249403708500778261032343 15374105562751167391548515)
                ·
                  refine ⟨23061158344126751087322773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15374105562751167391548515 23061158344126751087322773)
                  ·
                    refine ⟨1080991797380941457218255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23061158344126751087322773 1080991797380941457218255)
                    ·
                      rfl

theorem cell22_3157836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_3157836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157836 prefixEnd_3157836 := by exact prefixLift 3157836
  have htrace : WordTrace (prefixWord ++ tailWord_3157836) baseStart_3157836 baseEnd_3157836 := by
    simpa [prefixWord, tailWord_3157836, baseEnd_3157836] using wordTrace_append hprefix tailTrace_3157836
  have hstable : (prefixWord ++ tailWord_3157836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157836).length < 2 ^ (prefixWord ++ tailWord_3157836).sum := by decide
  have hdescent : baseEnd_3157836 < baseStart_3157836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157917 : List Nat := [1, 4, 2, 1, 2, 3, 3, 2, 1, 3]
def baseStart_3157917 : Nat := 118140960795 + 3157917 * 2 ^ 59
def prefixEnd_3157917 : Nat := 4983230072969 + 3 ^ 40 * 3157917 * 2
def baseEnd_3157917 : Nat := 1081019525336284245943007

theorem tailTrace_3157917 : CollatzResearch.WordTrace tailWord_3157917 prefixEnd_3157917 1081019525336284245943007 := by
  unfold tailWord_3157917
  simp only [CollatzResearch.WordTrace]
  refine ⟨115178695300413513130512005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76785796866942342087008003 115178695300413513130512005)
  ·
    refine ⟨21596005368827533711971001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115178695300413513130512005 21596005368827533711971001)
    ·
      refine ⟨16197004026620650283978251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21596005368827533711971001 16197004026620650283978251)
      ·
        refine ⟨24295506039930975425967377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16197004026620650283978251 24295506039930975425967377)
        ·
          refine ⟨18221629529948231569475533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24295506039930975425967377 18221629529948231569475533)
          ·
            refine ⟨6833111073730586838553325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18221629529948231569475533 6833111073730586838553325)
            ·
              refine ⟨2562416652648970064457497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6833111073730586838553325 2562416652648970064457497)
              ·
                refine ⟨1921812489486727548343123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2562416652648970064457497 1921812489486727548343123)
                ·
                  refine ⟨2882718734230091322514685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1921812489486727548343123 2882718734230091322514685)
                  ·
                    refine ⟨1081019525336284245943007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2882718734230091322514685 1081019525336284245943007)
                    ·
                      rfl

theorem cell22_3157917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_3157917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157917 prefixEnd_3157917 := by exact prefixLift 3157917
  have htrace : WordTrace (prefixWord ++ tailWord_3157917) baseStart_3157917 baseEnd_3157917 := by
    simpa [prefixWord, tailWord_3157917, baseEnd_3157917] using wordTrace_append hprefix tailTrace_3157917
  have hstable : (prefixWord ++ tailWord_3157917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157917).length < 2 ^ (prefixWord ++ tailWord_3157917).sum := by decide
  have hdescent : baseEnd_3157917 < baseStart_3157917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157960 : List Nat := [2, 1, 3, 1, 4, 2, 3, 1, 1, 4]
def baseStart_3157960 : Nat := 118140960795 + 3157960 * 2 ^ 59
def prefixEnd_3157960 : Nat := 4983230072969 + 3 ^ 40 * 3157960 * 2
def baseEnd_3157960 : Nat := 1081034245115046467117875

theorem tailTrace_3157960 : CollatzResearch.WordTrace tailWord_3157960 prefixEnd_3157960 1081034245115046467117875 := by
  unfold tailWord_3157960
  simp only [CollatzResearch.WordTrace]
  refine ⟨57590131819628865737163667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76786842426171820982884889 57590131819628865737163667)
  ·
    refine ⟨86385197729443298605745501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57590131819628865737163667 86385197729443298605745501)
    ·
      refine ⟨32394449148541236977154563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86385197729443298605745501 32394449148541236977154563)
      ·
        refine ⟨48591673722811855465731845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32394449148541236977154563 48591673722811855465731845)
        ·
          refine ⟨9110938823027222899824721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48591673722811855465731845 9110938823027222899824721)
          ·
            refine ⟨6833204117270417174868541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9110938823027222899824721 6833204117270417174868541)
            ·
              refine ⟨2562451543976406440575703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6833204117270417174868541 2562451543976406440575703)
              ·
                refine ⟨3843677315964609660863555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562451543976406440575703 3843677315964609660863555)
                ·
                  refine ⟨5765515973946914491295333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3843677315964609660863555 5765515973946914491295333)
                  ·
                    refine ⟨1081034245115046467117875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5765515973946914491295333 1081034245115046467117875)
                    ·
                      rfl

theorem cell22_3157960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_3157960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3157960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3157960 prefixEnd_3157960 := by exact prefixLift 3157960
  have htrace : WordTrace (prefixWord ++ tailWord_3157960) baseStart_3157960 baseEnd_3157960 := by
    simpa [prefixWord, tailWord_3157960, baseEnd_3157960] using wordTrace_append hprefix tailTrace_3157960
  have hstable : (prefixWord ++ tailWord_3157960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157960).length < 2 ^ (prefixWord ++ tailWord_3157960).sum := by decide
  have hdescent : baseEnd_3157960 < baseStart_3157960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158035 : List Nat := [1, 1, 1, 2, 1, 4, 4, 4, 1, 3]
def baseStart_3158035 : Nat := 118140960795 + 3158035 * 2 ^ 59
def prefixEnd_3158035 : Nat := 4983230072969 + 3 ^ 40 * 3158035 * 2
def baseEnd_3158035 : Nat := 1081059919147771271492645

theorem tailTrace_3158035 : CollatzResearch.WordTrace tailWord_3158035 prefixEnd_3158035 1081059919147771271492645 := by
  unfold tailWord_3158035
  simp only [CollatzResearch.WordTrace]
  refine ⟨115182999113986019283307559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76788666075990679522205039 115182999113986019283307559)
  ·
    refine ⟨172774498670979028924961339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115182999113986019283307559 172774498670979028924961339)
    ·
      refine ⟨259161748006468543387442009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172774498670979028924961339 259161748006468543387442009)
      ·
        refine ⟨194371311004851407540581507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259161748006468543387442009 194371311004851407540581507)
        ·
          refine ⟨291556966507277111310872261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194371311004851407540581507 291556966507277111310872261)
          ·
            refine ⟨54666931220114458370788549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291556966507277111310872261 54666931220114458370788549)
            ·
              refine ⟨10250049603771460944522853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54666931220114458370788549 10250049603771460944522853)
              ·
                refine ⟨1921884300707148927098035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10250049603771460944522853 1921884300707148927098035)
                ·
                  refine ⟨2882826451060723390647053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1921884300707148927098035 2882826451060723390647053)
                  ·
                    refine ⟨1081059919147771271492645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2882826451060723390647053 1081059919147771271492645)
                    ·
                      rfl

theorem cell22_3158035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 1, 3].length) (baseStart_3158035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158035 prefixEnd_3158035 := by exact prefixLift 3158035
  have htrace : WordTrace (prefixWord ++ tailWord_3158035) baseStart_3158035 baseEnd_3158035 := by
    simpa [prefixWord, tailWord_3158035, baseEnd_3158035] using wordTrace_append hprefix tailTrace_3158035
  have hstable : (prefixWord ++ tailWord_3158035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158035).length < 2 ^ (prefixWord ++ tailWord_3158035).sum := by decide
  have hdescent : baseEnd_3158035 < baseStart_3158035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158086 : List Nat := [6, 1, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_3158086 : Nat := 118140960795 + 3158086 * 2 ^ 59
def prefixEnd_3158086 : Nat := 4983230072969 + 3 ^ 40 * 3158086 * 2
def baseEnd_3158086 : Nat := 1081077377490024138467489

theorem tailTrace_3158086 : CollatzResearch.WordTrace tailWord_3158086 prefixEnd_3158086 1081077377490024138467489 := by
  unfold tailWord_3158086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3599526851150039218544191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76789906157867503328942741 3599526851150039218544191)
  ·
    refine ⟨5399290276725058827816287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3599526851150039218544191 5399290276725058827816287)
    ·
      refine ⟨8098935415087588241724431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5399290276725058827816287 8098935415087588241724431)
      ·
        refine ⟨12148403122631382362586647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8098935415087588241724431 12148403122631382362586647)
        ·
          refine ⟨18222604683947073543879971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12148403122631382362586647 18222604683947073543879971)
          ·
            refine ⟨27333907025920610315819957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18222604683947073543879971 27333907025920610315819957)
            ·
              refine ⟨2562553783680057217108121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27333907025920610315819957 2562553783680057217108121)
              ·
                refine ⟨1921915337760042912831091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2562553783680057217108121 1921915337760042912831091)
                ·
                  refine ⟨2882873006640064369246637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1921915337760042912831091 2882873006640064369246637)
                  ·
                    refine ⟨1081077377490024138467489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2882873006640064369246637 1081077377490024138467489)
                    ·
                      rfl

theorem cell22_3158086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_3158086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158086 prefixEnd_3158086 := by exact prefixLift 3158086
  have htrace : WordTrace (prefixWord ++ tailWord_3158086) baseStart_3158086 baseEnd_3158086 := by
    simpa [prefixWord, tailWord_3158086, baseEnd_3158086] using wordTrace_append hprefix tailTrace_3158086
  have hstable : (prefixWord ++ tailWord_3158086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158086).length < 2 ^ (prefixWord ++ tailWord_3158086).sum := by decide
  have hdescent : baseEnd_3158086 < baseStart_3158086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158091 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 3, 5]
def baseStart_3158091 : Nat := 118140960795 + 3158091 * 2 ^ 59
def prefixEnd_3158091 : Nat := 4983230072969 + 3 ^ 40 * 3158091 * 2
def baseEnd_3158091 : Nat := 1081079089092205792092473

theorem tailTrace_3158091 : CollatzResearch.WordTrace tailWord_3158091 prefixEnd_3158091 1081079089092205792092473 := by
  unfold tailWord_3158091
  simp only [CollatzResearch.WordTrace]
  refine ⟨115185041601783140847346127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76790027734522093898230751 115185041601783140847346127)
  ·
    refine ⟨172777562402674711271019191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115185041601783140847346127 172777562402674711271019191)
    ·
      refine ⟨259166343604012066906528787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172777562402674711271019191 259166343604012066906528787)
      ·
        refine ⟨388749515406018100359793181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259166343604012066906528787 388749515406018100359793181)
        ·
          refine ⟨145781068277256787634922443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388749515406018100359793181 145781068277256787634922443)
          ·
            refine ⟨218671602415885181452383665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145781068277256787634922443 218671602415885181452383665)
            ·
              refine ⟨164003701811913886089287749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218671602415885181452383665 164003701811913886089287749)
              ·
                refine ⟨30750694089733853641741453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164003701811913886089287749 30750694089733853641741453)
                ·
                  refine ⟨11531510283650195115653045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30750694089733853641741453 11531510283650195115653045)
                  ·
                    refine ⟨1081079089092205792092473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11531510283650195115653045 1081079089092205792092473)
                    ·
                      rfl

theorem cell22_3158091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 5].length) (baseStart_3158091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158091 prefixEnd_3158091 := by exact prefixLift 3158091
  have htrace : WordTrace (prefixWord ++ tailWord_3158091) baseStart_3158091 baseEnd_3158091 := by
    simpa [prefixWord, tailWord_3158091, baseEnd_3158091] using wordTrace_append hprefix tailTrace_3158091
  have hstable : (prefixWord ++ tailWord_3158091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158091).length < 2 ^ (prefixWord ++ tailWord_3158091).sum := by decide
  have hdescent : baseEnd_3158091 < baseStart_3158091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158121 : List Nat := [1, 2, 1, 1, 1, 5, 1, 10]
def baseStart_3158121 : Nat := 118140960795 + 3158121 * 2 ^ 59
def prefixEnd_3158121 : Nat := 4983230072969 + 3 ^ 40 * 3158121 * 2
def baseEnd_3158121 : Nat := 120121039856143968204709

theorem tailTrace_3158121 : CollatzResearch.WordTrace tailWord_3158121 prefixEnd_3158121 120121039856143968204709 := by
  unfold tailWord_3158121
  simp only [CollatzResearch.WordTrace]
  refine ⟨115186135791674455970938217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76790757194449637313958811 115186135791674455970938217)
  ·
    refine ⟨86389601843755841978203663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115186135791674455970938217 86389601843755841978203663)
    ·
      refine ⟨129584402765633762967305495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86389601843755841978203663 129584402765633762967305495)
      ·
        refine ⟨194376604148450644450958243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129584402765633762967305495 194376604148450644450958243)
        ·
          refine ⟨291564906222675966676437365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194376604148450644450958243 291564906222675966676437365)
          ·
            refine ⟨27334209958375871875916003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 291564906222675966676437365 27334209958375871875916003)
            ·
              refine ⟨41001314937563807813874005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27334209958375871875916003 41001314937563807813874005)
              ·
                refine ⟨120121039856143968204709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41001314937563807813874005 120121039856143968204709)
                ·
                  rfl

theorem cell22_3158121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 10].length) (baseStart_3158121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158121 prefixEnd_3158121 := by exact prefixLift 3158121
  have htrace : WordTrace (prefixWord ++ tailWord_3158121) baseStart_3158121 baseEnd_3158121 := by
    simpa [prefixWord, tailWord_3158121, baseEnd_3158121] using wordTrace_append hprefix tailTrace_3158121
  have hstable : (prefixWord ++ tailWord_3158121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158121).length < 2 ^ (prefixWord ++ tailWord_3158121).sum := by decide
  have hdescent : baseEnd_3158121 < baseStart_3158121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158174 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_3158174 : Nat := 118140960795 + 3158174 * 2 ^ 59
def prefixEnd_3158174 : Nat := 4983230072969 + 3 ^ 40 * 3158174 * 2
def baseEnd_3158174 : Nat := 1081107501688421242267219

theorem tailTrace_3158174 : CollatzResearch.WordTrace tailWord_3158174 prefixEnd_3158174 1081107501688421242267219 := by
  unfold tailWord_3158174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14398508607560305752827197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76792045906988297348411717 14398508607560305752827197)
  ·
    refine ⟨5399440727835114657310199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14398508607560305752827197 5399440727835114657310199)
    ·
      refine ⟨8099161091752671985965299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5399440727835114657310199 8099161091752671985965299)
      ·
        refine ⟨12148741637629007978947949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8099161091752671985965299 12148741637629007978947949)
        ·
          refine ⟨4555778114110877992105481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12148741637629007978947949 4555778114110877992105481)
          ·
            refine ⟨3416833585583158494079111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4555778114110877992105481 3416833585583158494079111)
            ·
              refine ⟨5125250378374737741118667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3416833585583158494079111 5125250378374737741118667)
              ·
                refine ⟨7687875567562106611678001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5125250378374737741118667 7687875567562106611678001)
                ·
                  refine ⟨5765906675671579958758501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7687875567562106611678001 5765906675671579958758501)
                  ·
                    refine ⟨1081107501688421242267219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5765906675671579958758501 1081107501688421242267219)
                    ·
                      rfl

theorem cell22_3158174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_3158174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158174 prefixEnd_3158174 := by exact prefixLift 3158174
  have htrace : WordTrace (prefixWord ++ tailWord_3158174) baseStart_3158174 baseEnd_3158174 := by
    simpa [prefixWord, tailWord_3158174, baseEnd_3158174] using wordTrace_append hprefix tailTrace_3158174
  have hstable : (prefixWord ++ tailWord_3158174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158174).length < 2 ^ (prefixWord ++ tailWord_3158174).sum := by decide
  have hdescent : baseEnd_3158174 < baseStart_3158174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158213 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_3158213 : Nat := 118140960795 + 3158213 * 2 ^ 59
def prefixEnd_3158213 : Nat := 4983230072969 + 3 ^ 40 * 3158213 * 2
def baseEnd_3158213 : Nat := 1081120852185438140542099

theorem tailTrace_3158213 : CollatzResearch.WordTrace tailWord_3158213 prefixEnd_3158213 1081120852185438140542099 := by
  unfold tailWord_3158213
  simp only [CollatzResearch.WordTrace]
  refine ⟨115189491307341155683287293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76792994204894103788858195 115189491307341155683287293)
  ·
    refine ⟨43196059240252933381232735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115189491307341155683287293 43196059240252933381232735)
    ·
      refine ⟨64794088860379400071849103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43196059240252933381232735 64794088860379400071849103)
      ·
        refine ⟨97191133290569100107773655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64794088860379400071849103 97191133290569100107773655)
        ·
          refine ⟨145786699935853650161660483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97191133290569100107773655 145786699935853650161660483)
          ·
            refine ⟨218680049903780475242490725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145786699935853650161660483 218680049903780475242490725)
            ·
              refine ⟨41002509356958839107967011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218680049903780475242490725 41002509356958839107967011)
              ·
                refine ⟨61503764035438258661950517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41002509356958839107967011 61503764035438258661950517)
                ·
                  refine ⟨5765977878322336749557861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61503764035438258661950517 5765977878322336749557861)
                  ·
                    refine ⟨1081120852185438140542099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5765977878322336749557861 1081120852185438140542099)
                    ·
                      rfl

theorem cell22_3158213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_3158213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158213 prefixEnd_3158213 := by exact prefixLift 3158213
  have htrace : WordTrace (prefixWord ++ tailWord_3158213) baseStart_3158213 baseEnd_3158213 := by
    simpa [prefixWord, tailWord_3158213, baseEnd_3158213] using wordTrace_append hprefix tailTrace_3158213
  have hstable : (prefixWord ++ tailWord_3158213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158213).length < 2 ^ (prefixWord ++ tailWord_3158213).sum := by decide
  have hdescent : baseEnd_3158213 < baseStart_3158213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158247 : List Nat := [1, 1, 5, 3, 1, 1, 2, 3, 1, 4]
def baseStart_3158247 : Nat := 118140960795 + 3158247 * 2 ^ 59
def prefixEnd_3158247 : Nat := 4983230072969 + 3 ^ 40 * 3158247 * 2
def baseEnd_3158247 : Nat := 1081132491080273385191995

theorem tailTrace_3158247 : CollatzResearch.WordTrace tailWord_3158247 prefixEnd_3158247 1081132491080273385191995 := by
  unfold tailWord_3158247
  simp only [CollatzResearch.WordTrace]
  refine ⟨115190731389217979490024995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76793820926145319660016663 115190731389217979490024995)
  ·
    refine ⟨172786097083826969235037493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115190731389217979490024995 172786097083826969235037493)
    ·
      refine ⟨16198696601608778365784765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172786097083826969235037493 16198696601608778365784765)
      ·
        refine ⟨6074511225603291887169287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16198696601608778365784765 6074511225603291887169287)
        ·
          refine ⟨9111766838404937830753931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6074511225603291887169287 9111766838404937830753931)
          ·
            refine ⟨13667650257607406746130897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9111766838404937830753931 13667650257607406746130897)
            ·
              refine ⟨10250737693205555059598173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13667650257607406746130897 10250737693205555059598173)
              ·
                refine ⟨3844026634952083147349315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10250737693205555059598173 3844026634952083147349315)
                ·
                  refine ⟨5766039952428124721023973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3844026634952083147349315 5766039952428124721023973)
                  ·
                    refine ⟨1081132491080273385191995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5766039952428124721023973 1081132491080273385191995)
                    ·
                      rfl

theorem cell22_3158247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_3158247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158247 prefixEnd_3158247 := by exact prefixLift 3158247
  have htrace : WordTrace (prefixWord ++ tailWord_3158247) baseStart_3158247 baseEnd_3158247 := by
    simpa [prefixWord, tailWord_3158247, baseEnd_3158247] using wordTrace_append hprefix tailTrace_3158247
  have hstable : (prefixWord ++ tailWord_3158247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158247).length < 2 ^ (prefixWord ++ tailWord_3158247).sum := by decide
  have hdescent : baseEnd_3158247 < baseStart_3158247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158262 : List Nat := [5, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_3158262 : Nat := 118140960795 + 3158262 * 2 ^ 59
def prefixEnd_3158262 : Nat := 4983230072969 + 3 ^ 40 * 3158262 * 2
def baseEnd_3158262 : Nat := 360379208628939448688983

theorem tailTrace_3158262 : CollatzResearch.WordTrace tailWord_3158262 prefixEnd_3158262 360379208628939448688983 := by
  unfold tailWord_3158262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199454905260227315738815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76794185656109091367880693 7199454905260227315738815)
  ·
    refine ⟨10799182357890340973608223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7199454905260227315738815 10799182357890340973608223)
    ·
      refine ⟨16198773536835511460412335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10799182357890340973608223 16198773536835511460412335)
      ·
        refine ⟨24298160305253267190618503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16198773536835511460412335 24298160305253267190618503)
        ·
          refine ⟨36447240457879900785927755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24298160305253267190618503 36447240457879900785927755)
          ·
            refine ⟨54670860686819851178891633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36447240457879900785927755 54670860686819851178891633)
            ·
              refine ⟨41003145515114888384168725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54670860686819851178891633 41003145515114888384168725)
              ·
                refine ⟨1922022446021010393007909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41003145515114888384168725 1922022446021010393007909)
                ·
                  refine ⟨360379208628939448688983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1922022446021010393007909 360379208628939448688983)
                  ·
                    rfl

theorem cell22_3158262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_3158262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158262 prefixEnd_3158262 := by exact prefixLift 3158262
  have htrace : WordTrace (prefixWord ++ tailWord_3158262) baseStart_3158262 baseEnd_3158262 := by
    simpa [prefixWord, tailWord_3158262, baseEnd_3158262] using wordTrace_append hprefix tailTrace_3158262
  have hstable : (prefixWord ++ tailWord_3158262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158262).length < 2 ^ (prefixWord ++ tailWord_3158262).sum := by decide
  have hdescent : baseEnd_3158262 < baseStart_3158262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158335 : List Nat := [1, 1, 2, 2, 4, 1, 1, 5, 5]
def baseStart_3158335 : Nat := 118140960795 + 3158335 * 2 ^ 59
def prefixEnd_3158335 : Nat := 4983230072969 + 3 ^ 40 * 3158335 * 2
def baseEnd_3158335 : Nat := 360387538426223496330575

theorem tailTrace_3158335 : CollatzResearch.WordTrace tailWord_3158335 prefixEnd_3158335 360387538426223496330575 := by
  unfold tailWord_3158335
  simp only [CollatzResearch.WordTrace]
  refine ⟨115193941012899170519228459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76795960675266113679485639 115193941012899170519228459)
  ·
    refine ⟨172790911519348755778842689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115193941012899170519228459 172790911519348755778842689)
    ·
      refine ⟨129593183639511566834132017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172790911519348755778842689 129593183639511566834132017)
      ·
        refine ⟨97194887729633675125599013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129593183639511566834132017 97194887729633675125599013)
        ·
          refine ⟨18224041449306314086049815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97194887729633675125599013 18224041449306314086049815)
          ·
            refine ⟨27336062173959471129074723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18224041449306314086049815 27336062173959471129074723)
            ·
              refine ⟨41004093260939206693612085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27336062173959471129074723 41004093260939206693612085)
              ·
                refine ⟨3844133743213050627526133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41004093260939206693612085 3844133743213050627526133)
                ·
                  refine ⟨360387538426223496330575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3844133743213050627526133 360387538426223496330575)
                  ·
                    rfl

theorem cell22_3158335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 5].length) (baseStart_3158335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158335 prefixEnd_3158335 := by exact prefixLift 3158335
  have htrace : WordTrace (prefixWord ++ tailWord_3158335) baseStart_3158335 baseEnd_3158335 := by
    simpa [prefixWord, tailWord_3158335, baseEnd_3158335] using wordTrace_append hprefix tailTrace_3158335
  have hstable : (prefixWord ++ tailWord_3158335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158335).length < 2 ^ (prefixWord ++ tailWord_3158335).sum := by decide
  have hdescent : baseEnd_3158335 < baseStart_3158335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158356 : List Nat := [2, 4, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_3158356 : Nat := 118140960795 + 3158356 * 2 ^ 59
def prefixEnd_3158356 : Nat := 4983230072969 + 3 ^ 40 * 3158356 * 2
def baseEnd_3158356 : Nat := 1081169804007833434216661

theorem tailTrace_3158356 : CollatzResearch.WordTrace tailWord_3158356 prefixEnd_3158356 1081169804007833434216661 := by
  unfold tailWord_3158356
  simp only [CollatzResearch.WordTrace]
  refine ⟨57597353472911545552871461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76796471297215394070495281 57597353472911545552871461)
  ·
    refine ⟨10799503776170914791163399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57597353472911545552871461 10799503776170914791163399)
    ·
      refine ⟨16199255664256372186745099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10799503776170914791163399 16199255664256372186745099)
      ·
        refine ⟨24298883496384558280117649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16199255664256372186745099 24298883496384558280117649)
        ·
          refine ⟨18224162622288418710088237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24298883496384558280117649 18224162622288418710088237)
          ·
            refine ⟨6834060983358157016283089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18224162622288418710088237 6834060983358157016283089)
            ·
              refine ⟨5125545737518617762212317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6834060983358157016283089 5125545737518617762212317)
              ·
                refine ⟨1922079651569481660829619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5125545737518617762212317 1922079651569481660829619)
                ·
                  refine ⟨2883119477354222491244429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922079651569481660829619 2883119477354222491244429)
                  ·
                    refine ⟨1081169804007833434216661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2883119477354222491244429 1081169804007833434216661)
                    ·
                      rfl

theorem cell22_3158356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_3158356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158356 prefixEnd_3158356 := by exact prefixLift 3158356
  have htrace : WordTrace (prefixWord ++ tailWord_3158356) baseStart_3158356 baseEnd_3158356 := by
    simpa [prefixWord, tailWord_3158356, baseEnd_3158356] using wordTrace_append hprefix tailTrace_3158356
  have hstable : (prefixWord ++ tailWord_3158356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158356).length < 2 ^ (prefixWord ++ tailWord_3158356).sum := by decide
  have hdescent : baseEnd_3158356 < baseStart_3158356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158412 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 4, 3]
def baseStart_3158412 : Nat := 118140960795 + 3158412 * 2 ^ 59
def prefixEnd_3158412 : Nat := 4983230072969 + 3 ^ 40 * 3158412 * 2
def baseEnd_3158412 : Nat := 1081188973952267954816489

theorem tailTrace_3158412 : CollatzResearch.WordTrace tailWord_3158412 prefixEnd_3158412 1081188973952267954816489 := by
  unfold tailWord_3158412
  simp only [CollatzResearch.WordTrace]
  refine ⟨57598374716810106334890745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76797832955746808446520993 57598374716810106334890745)
  ·
    refine ⟨43198781037607579751168059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57598374716810106334890745 43198781037607579751168059)
    ·
      refine ⟨64798171556411369626752089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43198781037607579751168059 64798171556411369626752089)
      ·
        refine ⟨48598628667308527220064067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64798171556411369626752089 48598628667308527220064067)
        ·
          refine ⟨72897943000962790830096101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48598628667308527220064067 72897943000962790830096101)
          ·
            refine ⟨13668364312680523280643019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72897943000962790830096101 13668364312680523280643019)
            ·
              refine ⟨20502546469020784920964529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13668364312680523280643019 20502546469020784920964529)
              ·
                refine ⟨15376909851765588690723397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20502546469020784920964529 15376909851765588690723397)
                ·
                  refine ⟨2883170597206047879510637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15376909851765588690723397 2883170597206047879510637)
                  ·
                    refine ⟨1081188973952267954816489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2883170597206047879510637 1081188973952267954816489)
                    ·
                      rfl

theorem cell22_3158412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_3158412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158412 prefixEnd_3158412 := by exact prefixLift 3158412
  have htrace : WordTrace (prefixWord ++ tailWord_3158412) baseStart_3158412 baseEnd_3158412 := by
    simpa [prefixWord, tailWord_3158412, baseEnd_3158412] using wordTrace_append hprefix tailTrace_3158412
  have hstable : (prefixWord ++ tailWord_3158412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158412).length < 2 ^ (prefixWord ++ tailWord_3158412).sum := by decide
  have hdescent : baseEnd_3158412 < baseStart_3158412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158549 : List Nat := [1, 3, 2, 1, 3, 1, 1, 6, 4]
def baseStart_3158549 : Nat := 118140960795 + 3158549 * 2 ^ 59
def prefixEnd_3158549 : Nat := 4983230072969 + 3 ^ 40 * 3158549 * 2
def baseEnd_3158549 : Nat := 360411957284015088047023

theorem tailTrace_3158549 : CollatzResearch.WordTrace tailWord_3158549 prefixEnd_3158549 360411957284015088047023 := by
  unfold tailWord_3158549
  simp only [CollatzResearch.WordTrace]
  refine ⟨115201746234123885067518701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76801164156082590045012467 115201746234123885067518701)
  ·
    refine ⟨43200654837796456900319513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115201746234123885067518701 43200654837796456900319513)
    ·
      refine ⟨32400491128347342675239635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43200654837796456900319513 32400491128347342675239635)
      ·
        refine ⟨48600736692521014012859453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32400491128347342675239635 48600736692521014012859453)
        ·
          refine ⟨18225276259695380254822295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48600736692521014012859453 18225276259695380254822295)
          ·
            refine ⟨27337914389543070382233443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18225276259695380254822295 27337914389543070382233443)
            ·
              refine ⟨41006871584314605573350165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27337914389543070382233443 41006871584314605573350165)
              ·
                refine ⟨1922197105514747136250789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41006871584314605573350165 1922197105514747136250789)
                ·
                  refine ⟨360411957284015088047023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1922197105514747136250789 360411957284015088047023)
                  ·
                    rfl

theorem cell22_3158549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_3158549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158549 prefixEnd_3158549 := by exact prefixLift 3158549
  have htrace : WordTrace (prefixWord ++ tailWord_3158549) baseStart_3158549 baseEnd_3158549 := by
    simpa [prefixWord, tailWord_3158549, baseEnd_3158549] using wordTrace_append hprefix tailTrace_3158549
  have hstable : (prefixWord ++ tailWord_3158549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158549).length < 2 ^ (prefixWord ++ tailWord_3158549).sum := by decide
  have hdescent : baseEnd_3158549 < baseStart_3158549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158598 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_3158598 : Nat := 118140960795 + 3158598 * 2 ^ 59
def prefixEnd_3158598 : Nat := 4983230072969 + 3 ^ 40 * 3158598 * 2
def baseEnd_3158598 : Nat := 1081252645553425469665919

theorem tailTrace_3158598 : CollatzResearch.WordTrace tailWord_3158598 prefixEnd_3158598 1081252645553425469665919 := by
  unfold tailWord_3158598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3600110419092073951126639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76802355607297577624034965 3600110419092073951126639)
  ·
    refine ⟨5400165628638110926689959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3600110419092073951126639 5400165628638110926689959)
    ·
      refine ⟨8100248442957166390034939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5400165628638110926689959 8100248442957166390034939)
      ·
        refine ⟨12150372664435749585052409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8100248442957166390034939 12150372664435749585052409)
        ·
          refine ⟨9112779498326812188789307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12150372664435749585052409 9112779498326812188789307)
          ·
            refine ⟨13669169247490218283183961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9112779498326812188789307 13669169247490218283183961)
            ·
              refine ⟨10251876935617663712387971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13669169247490218283183961 10251876935617663712387971)
              ·
                refine ⟨15377815403426495568581957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10251876935617663712387971 15377815403426495568581957)
                ·
                  refine ⟨2883340388142467919109117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15377815403426495568581957 2883340388142467919109117)
                  ·
                    refine ⟨1081252645553425469665919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2883340388142467919109117 1081252645553425469665919)
                    ·
                      rfl

theorem cell22_3158598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_3158598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158598 prefixEnd_3158598 := by exact prefixLift 3158598
  have htrace : WordTrace (prefixWord ++ tailWord_3158598) baseStart_3158598 baseEnd_3158598 := by
    simpa [prefixWord, tailWord_3158598, baseEnd_3158598] using wordTrace_append hprefix tailTrace_3158598
  have hstable : (prefixWord ++ tailWord_3158598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158598).length < 2 ^ (prefixWord ++ tailWord_3158598).sum := by decide
  have hdescent : baseEnd_3158598 < baseStart_3158598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158660 : List Nat := [2, 3, 2, 1, 3, 1, 4, 2, 1, 3]
def baseStart_3158660 : Nat := 118140960795 + 3158660 * 2 ^ 59
def prefixEnd_3158660 : Nat := 4983230072969 + 3 ^ 40 * 3158660 * 2
def baseEnd_3158660 : Nat := 1081273869420477974615729

theorem tailTrace_3158660 : CollatzResearch.WordTrace tailWord_3158660 prefixEnd_3158660 1081273869420477974615729 := by
  unfold tailWord_3158660
  simp only [CollatzResearch.WordTrace]
  refine ⟨57602897368360875512404717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76803863157814500683206289 57602897368360875512404717)
  ·
    refine ⟨21601086513135328317151769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57602897368360875512404717 21601086513135328317151769)
    ·
      refine ⟨16200814884851496237863827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21601086513135328317151769 16200814884851496237863827)
      ·
        refine ⟨24301222327277244356795741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16200814884851496237863827 24301222327277244356795741)
        ·
          refine ⟨9112958372728966633798403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24301222327277244356795741 9112958372728966633798403)
          ·
            refine ⟨13669437559093449950697605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9112958372728966633798403 13669437559093449950697605)
            ·
              refine ⟨2563019542330021865755801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13669437559093449950697605 2563019542330021865755801)
              ·
                refine ⟨1922264656747516399316851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2563019542330021865755801 1922264656747516399316851)
                ·
                  refine ⟨2883396985121274598975277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922264656747516399316851 2883396985121274598975277)
                  ·
                    refine ⟨1081273869420477974615729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2883396985121274598975277 1081273869420477974615729)
                    ·
                      rfl

theorem cell22_3158660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_3158660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158660 prefixEnd_3158660 := by exact prefixLift 3158660
  have htrace : WordTrace (prefixWord ++ tailWord_3158660) baseStart_3158660 baseEnd_3158660 := by
    simpa [prefixWord, tailWord_3158660, baseEnd_3158660] using wordTrace_append hprefix tailTrace_3158660
  have hstable : (prefixWord ++ tailWord_3158660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158660).length < 2 ^ (prefixWord ++ tailWord_3158660).sum := by decide
  have hdescent : baseEnd_3158660 < baseStart_3158660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158684 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 8]
def baseStart_3158684 : Nat := 118140960795 + 3158684 * 2 ^ 59
def prefixEnd_3158684 : Nat := 4983230072969 + 3 ^ 40 * 3158684 * 2
def baseEnd_3158684 : Nat := 360427361703649970671885

theorem tailTrace_3158684 : CollatzResearch.WordTrace tailWord_3158684 prefixEnd_3158684 360427361703649970671885 := by
  unfold tailWord_3158684
  simp only [CollatzResearch.WordTrace]
  refine ⟨57603335044317401561841553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76804446725756535415788737 57603335044317401561841553)
  ·
    refine ⟨43202501283238051171381165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57603335044317401561841553 43202501283238051171381165)
    ·
      refine ⟨16200937981214269189267937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43202501283238051171381165 16200937981214269189267937)
      ·
        refine ⟨12150703485910701891950953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16200937981214269189267937 12150703485910701891950953)
        ·
          refine ⟨9113027614433026418963215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12150703485910701891950953 9113027614433026418963215)
          ·
            refine ⟨13669541421649539628444823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9113027614433026418963215 13669541421649539628444823)
            ·
              refine ⟨20504312132474309442667235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13669541421649539628444823 20504312132474309442667235)
              ·
                refine ⟨30756468198711464164000853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20504312132474309442667235 30756468198711464164000853)
                ·
                  refine ⟨360427361703649970671885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30756468198711464164000853 360427361703649970671885)
                  ·
                    rfl

theorem cell22_3158684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_3158684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158684 prefixEnd_3158684 := by exact prefixLift 3158684
  have htrace : WordTrace (prefixWord ++ tailWord_3158684) baseStart_3158684 baseEnd_3158684 := by
    simpa [prefixWord, tailWord_3158684, baseEnd_3158684] using wordTrace_append hprefix tailTrace_3158684
  have hstable : (prefixWord ++ tailWord_3158684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158684).length < 2 ^ (prefixWord ++ tailWord_3158684).sum := by decide
  have hdescent : baseEnd_3158684 < baseStart_3158684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158686 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3158686 : Nat := 118140960795 + 3158686 * 2 ^ 59
def prefixEnd_3158686 : Nat := 4983230072969 + 3 ^ 40 * 3158686 * 2
def baseEnd_3158686 : Nat := 1081282769751822573465649

theorem tailTrace_3158686 : CollatzResearch.WordTrace tailWord_3158686 prefixEnd_3158686 1081282769751822573465649 := by
  unfold tailWord_3158686
  simp only [CollatzResearch.WordTrace]
  refine ⟨14400842879328444683156989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76804495356418371643503941 14400842879328444683156989)
  ·
    refine ⟨5400316079748166756183871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14400842879328444683156989 5400316079748166756183871)
    ·
      refine ⟨8100474119622250134275807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5400316079748166756183871 8100474119622250134275807)
      ·
        refine ⟨12150711179433375201413711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8100474119622250134275807 12150711179433375201413711)
        ·
          refine ⟨18226066769150062802120567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12150711179433375201413711 18226066769150062802120567)
          ·
            refine ⟨27339100153725094203180851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18226066769150062802120567 27339100153725094203180851)
            ·
              refine ⟨41008650230587641304771277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27339100153725094203180851 41008650230587641304771277)
              ·
                refine ⟨15378243836470365489289229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41008650230587641304771277 15378243836470365489289229)
                ·
                  refine ⟨5766841438676387058483461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15378243836470365489289229 5766841438676387058483461)
                  ·
                    refine ⟨1081282769751822573465649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5766841438676387058483461 1081282769751822573465649)
                    ·
                      rfl

theorem cell22_3158686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3158686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3158686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3158686 prefixEnd_3158686 := by exact prefixLift 3158686
  have htrace : WordTrace (prefixWord ++ tailWord_3158686) baseStart_3158686 baseEnd_3158686 := by
    simpa [prefixWord, tailWord_3158686, baseEnd_3158686] using wordTrace_append hprefix tailTrace_3158686
  have hstable : (prefixWord ++ tailWord_3158686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158686).length < 2 ^ (prefixWord ++ tailWord_3158686).sum := by decide
  have hdescent : baseEnd_3158686 < baseStart_3158686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
