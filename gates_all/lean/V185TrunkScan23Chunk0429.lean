import V185TrunkScan23Chunk0428

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2536574 : List Nat := [4, 2, 4, 1, 2, 1, 9]
def baseStart_2536574 : Nat := 118140960795 + 2536574 * 2 ^ 59
def prefixEnd_2536574 : Nat := 4983230072969 + 3 ^ 40 * 2536574 * 2
def baseEnd_2536574 : Nat := 16080020712319307114315

theorem tailTrace_2536574 : CollatzResearch.WordTrace tailWord_2536574 prefixEnd_2536574 16080020712319307114315 := by
  unfold tailWord_2536574
  simp only [CollatzResearch.WordTrace]
  refine ⟨11564556789054135649314097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61677636208288723463008517 11564556789054135649314097)
  ·
    refine ⟨8673417591790601736985573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11564556789054135649314097 8673417591790601736985573)
    ·
      refine ⟨1626265798460737825684795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8673417591790601736985573 1626265798460737825684795)
      ·
        refine ⟨2439398697691106738527193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1626265798460737825684795 2439398697691106738527193)
        ·
          refine ⟨1829549023268330053895395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2439398697691106738527193 1829549023268330053895395)
          ·
            refine ⟨2744323534902495080843093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1829549023268330053895395 2744323534902495080843093)
            ·
              refine ⟨16080020712319307114315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2744323534902495080843093 16080020712319307114315)
              ·
                rfl

theorem cell23_2536574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 9].length) (baseStart_2536574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536574 prefixEnd_2536574 := by exact prefixLift 2536574
  have htrace : WordTrace (prefixWord ++ tailWord_2536574) baseStart_2536574 baseEnd_2536574 := by
    simpa [prefixWord, tailWord_2536574, baseEnd_2536574] using wordTrace_append hprefix tailTrace_2536574
  have hstable : (prefixWord ++ tailWord_2536574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536574).length < 2 ^ (prefixWord ++ tailWord_2536574).sum := by decide
  have hdescent : baseEnd_2536574 < baseStart_2536574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536576 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 5]
def baseStart_2536576 : Nat := 118140960795 + 2536576 * 2 ^ 59
def prefixEnd_2536576 : Nat := 4983230072969 + 3 ^ 40 * 2536576 * 2
def baseEnd_2536576 : Nat := 1302482704659172868434505

theorem tailTrace_2536576 : CollatzResearch.WordTrace tailWord_2536576 prefixEnd_2536576 1302482704659172868434505 := by
  unfold tailWord_2536576
  simp only [CollatzResearch.WordTrace]
  refine ⟨46258263629212919768042791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61677684838950559690723721 46258263629212919768042791)
  ·
    refine ⟨69387395443819379652064187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46258263629212919768042791 69387395443819379652064187)
    ·
      refine ⟨104081093165729069478096281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69387395443819379652064187 104081093165729069478096281)
      ·
        refine ⟨78060819874296802108572211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104081093165729069478096281 78060819874296802108572211)
        ·
          refine ⟨117091229811445203162858317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78060819874296802108572211 117091229811445203162858317)
          ·
            refine ⟨43909211179291951186071869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117091229811445203162858317 43909211179291951186071869)
            ·
              refine ⟨16465954192234481694776951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43909211179291951186071869 16465954192234481694776951)
              ·
                refine ⟨24698931288351722542165427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16465954192234481694776951 24698931288351722542165427)
                ·
                  refine ⟨37048396932527583813248141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24698931288351722542165427 37048396932527583813248141)
                  ·
                    refine ⟨13893148849697843929968053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37048396932527583813248141 13893148849697843929968053)
                    ·
                      refine ⟨1302482704659172868434505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13893148849697843929968053 1302482704659172868434505)
                      ·
                        rfl

theorem cell23_2536576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_2536576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536576 prefixEnd_2536576 := by exact prefixLift 2536576
  have htrace : WordTrace (prefixWord ++ tailWord_2536576) baseStart_2536576 baseEnd_2536576 := by
    simpa [prefixWord, tailWord_2536576, baseEnd_2536576] using wordTrace_append hprefix tailTrace_2536576
  have hstable : (prefixWord ++ tailWord_2536576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536576).length < 2 ^ (prefixWord ++ tailWord_2536576).sum := by decide
  have hdescent : baseEnd_2536576 < baseStart_2536576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536577 : List Nat := [1, 2, 4, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_2536577 : Nat := 118140960795 + 2536577 * 2 ^ 59
def prefixEnd_2536577 : Nat := 4983230072969 + 3 ^ 40 * 2536577 * 2
def baseEnd_2536577 : Nat := 1302483218139827364522001

theorem tailTrace_2536577 : CollatzResearch.WordTrace tailWord_2536577 prefixEnd_2536577 1302483218139827364522001 := by
  unfold tailWord_2536577
  simp only [CollatzResearch.WordTrace]
  refine ⟨92516563731422216706871985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61677709154281477804581323 92516563731422216706871985)
  ·
    refine ⟨69387422798566662530153989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92516563731422216706871985 69387422798566662530153989)
    ·
      refine ⟨13010141774731249224403873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69387422798566662530153989 13010141774731249224403873)
      ·
        refine ⟨9757606331048436918302905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13010141774731249224403873 9757606331048436918302905)
        ·
          refine ⟨7318204748286327688727179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9757606331048436918302905 7318204748286327688727179)
          ·
            refine ⟨10977307122429491533090769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7318204748286327688727179 10977307122429491533090769)
            ·
              refine ⟨8232980341822118649818077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10977307122429491533090769 8232980341822118649818077)
              ·
                refine ⟨3087367628183294493681779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8232980341822118649818077 3087367628183294493681779)
                ·
                  refine ⟨4631051442274941740522669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087367628183294493681779 4631051442274941740522669)
                  ·
                    refine ⟨1736644290853103152696001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4631051442274941740522669 1736644290853103152696001)
                    ·
                      refine ⟨1302483218139827364522001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736644290853103152696001 1302483218139827364522001)
                      ·
                        rfl

theorem cell23_2536577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_2536577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536577 prefixEnd_2536577 := by exact prefixLift 2536577
  have htrace : WordTrace (prefixWord ++ tailWord_2536577) baseStart_2536577 baseEnd_2536577 := by
    simpa [prefixWord, tailWord_2536577, baseEnd_2536577] using wordTrace_append hprefix tailTrace_2536577
  have hstable : (prefixWord ++ tailWord_2536577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536577).length < 2 ^ (prefixWord ++ tailWord_2536577).sum := by decide
  have hdescent : baseEnd_2536577 < baseStart_2536577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536641 : List Nat := [1, 2, 6, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_2536641 : Nat := 118140960795 + 2536641 * 2 ^ 59
def prefixEnd_2536641 : Nat := 4983230072969 + 3 ^ 40 * 2536641 * 2
def baseEnd_2536641 : Nat := 1302516080901715114121707

theorem tailTrace_2536641 : CollatzResearch.WordTrace tailWord_2536641 prefixEnd_2536641 1302516080901715114121707 := by
  unfold tailWord_2536641
  simp only [CollatzResearch.WordTrace]
  refine ⟨92518898003190355637201777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61679265335460237091467851 92518898003190355637201777)
  ·
    refine ⟨69389173502392766727901333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92518898003190355637201777 69389173502392766727901333)
    ·
      refine ⟨3252617507924660940370375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69389173502392766727901333 3252617507924660940370375)
      ·
        refine ⟨4878926261886991410555563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3252617507924660940370375 4878926261886991410555563)
        ·
          refine ⟨7318389392830487115833345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4878926261886991410555563 7318389392830487115833345)
          ·
            refine ⟨5488792044622865336875009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7318389392830487115833345 5488792044622865336875009)
            ·
              refine ⟨4116594033467149002656257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5488792044622865336875009 4116594033467149002656257)
              ·
                refine ⟨3087445525100361751992193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4116594033467149002656257 3087445525100361751992193)
                ·
                  refine ⟨2315584143825271313994145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3087445525100361751992193 2315584143825271313994145)
                  ·
                    refine ⟨1736688107868953485495609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2315584143825271313994145 1736688107868953485495609)
                    ·
                      refine ⟨1302516080901715114121707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736688107868953485495609 1302516080901715114121707)
                      ·
                        rfl

theorem cell23_2536641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_2536641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536641 prefixEnd_2536641 := by exact prefixLift 2536641
  have htrace : WordTrace (prefixWord ++ tailWord_2536641) baseStart_2536641 baseEnd_2536641 := by
    simpa [prefixWord, tailWord_2536641, baseEnd_2536641] using wordTrace_append hprefix tailTrace_2536641
  have hstable : (prefixWord ++ tailWord_2536641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536641).length < 2 ^ (prefixWord ++ tailWord_2536641).sum := by decide
  have hdescent : baseEnd_2536641 < baseStart_2536641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536650 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 2, 5, 2]
def baseStart_2536650 : Nat := 118140960795 + 2536650 * 2 ^ 59
def prefixEnd_2536650 : Nat := 4983230072969 + 3 ^ 40 * 2536650 * 2
def baseEnd_2536650 : Nat := 1302520702227605578909165

theorem tailTrace_2536650 : CollatzResearch.WordTrace tailWord_2536650 prefixEnd_2536650 1302520702227605578909165 := by
  unfold tailWord_2536650
  simp only [CollatzResearch.WordTrace]
  refine ⟨23129806565039437543569851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61679484173438500116186269 23129806565039437543569851)
  ·
    refine ⟨34694709847559156315354777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23129806565039437543569851 34694709847559156315354777)
    ·
      refine ⟨26021032385669367236516083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34694709847559156315354777 26021032385669367236516083)
      ·
        refine ⟨39031548578504050854774125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26021032385669367236516083 39031548578504050854774125)
        ·
          refine ⟨14636830716939019070540297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39031548578504050854774125 14636830716939019070540297)
          ·
            refine ⟨10977623037704264302905223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14636830716939019070540297 10977623037704264302905223)
            ·
              refine ⟨16466434556556396454357835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10977623037704264302905223 16466434556556396454357835)
              ·
                refine ⟨24699651834834594681536753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16466434556556396454357835 24699651834834594681536753)
                ·
                  refine ⟨18524738876125946011152565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24699651834834594681536753 18524738876125946011152565)
                  ·
                    refine ⟨1736694269636807438545553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18524738876125946011152565 1736694269636807438545553)
                    ·
                      refine ⟨1302520702227605578909165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736694269636807438545553 1302520702227605578909165)
                      ·
                        rfl

theorem cell23_2536650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_2536650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536650 prefixEnd_2536650 := by exact prefixLift 2536650
  have htrace : WordTrace (prefixWord ++ tailWord_2536650) baseStart_2536650 baseEnd_2536650 := by
    simpa [prefixWord, tailWord_2536650, baseEnd_2536650] using wordTrace_append hprefix tailTrace_2536650
  have hstable : (prefixWord ++ tailWord_2536650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536650).length < 2 ^ (prefixWord ++ tailWord_2536650).sum := by decide
  have hdescent : baseEnd_2536650 < baseStart_2536650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536663 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 4]
def baseStart_2536663 : Nat := 118140960795 + 2536663 * 2 ^ 59
def prefixEnd_2536663 : Nat := 4983230072969 + 3 ^ 40 * 2536663 * 2
def baseEnd_2536663 : Nat := 1302527377476114028046605

theorem tailTrace_2536663 : CollatzResearch.WordTrace tailWord_2536663 prefixEnd_2536663 1302527377476114028046605 := by
  unfold tailWord_2536663
  simp only [CollatzResearch.WordTrace]
  refine ⟨92519700409110653394502643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61679800272740435596335095 92519700409110653394502643)
  ·
    refine ⟨138779550613665980091753965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92519700409110653394502643 138779550613665980091753965)
    ·
      refine ⟨52042331480124742534407737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138779550613665980091753965 52042331480124742534407737)
      ·
        refine ⟨39031748610093556900805803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52042331480124742534407737 39031748610093556900805803)
        ·
          refine ⟨58547622915140335351208705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39031748610093556900805803 58547622915140335351208705)
          ·
            refine ⟨43910717186355251513406529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58547622915140335351208705 43910717186355251513406529)
            ·
              refine ⟨32933037889766438635054897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43910717186355251513406529 32933037889766438635054897)
              ·
                refine ⟨24699778417324828976291173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32933037889766438635054897 24699778417324828976291173)
                ·
                  refine ⟨4631208453248405433054595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24699778417324828976291173 4631208453248405433054595)
                  ·
                    refine ⟨6946812679872608149581893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4631208453248405433054595 6946812679872608149581893)
                    ·
                      refine ⟨1302527377476114028046605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6946812679872608149581893 1302527377476114028046605)
                      ·
                        rfl

theorem cell23_2536663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_2536663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536663 prefixEnd_2536663 := by exact prefixLift 2536663
  have htrace : WordTrace (prefixWord ++ tailWord_2536663) baseStart_2536663 baseEnd_2536663 := by
    simpa [prefixWord, tailWord_2536663, baseEnd_2536663] using wordTrace_append hprefix tailTrace_2536663
  have hstable : (prefixWord ++ tailWord_2536663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536663).length < 2 ^ (prefixWord ++ tailWord_2536663).sum := by decide
  have hdescent : baseEnd_2536663 < baseStart_2536663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536677 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 2, 5]
def baseStart_2536677 : Nat := 118140960795 + 2536677 * 2 ^ 59
def prefixEnd_2536677 : Nat := 4983230072969 + 3 ^ 40 * 2536677 * 2
def baseEnd_2536677 : Nat := 434178188735092324423847

theorem tailTrace_2536677 : CollatzResearch.WordTrace tailWord_2536677 prefixEnd_2536677 434178188735092324423847 := by
  unfold tailWord_2536677
  simp only [CollatzResearch.WordTrace]
  refine ⟨92520211031059933785512285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61680140687373289190341523 92520211031059933785512285)
  ·
    refine ⟨34695079136647475169567107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92520211031059933785512285 34695079136647475169567107)
    ·
      refine ⟨52042618704971212754350661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34695079136647475169567107 52042618704971212754350661)
      ·
        refine ⟨9757991007182102391440749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52042618704971212754350661 9757991007182102391440749)
        ·
          refine ⟨3659246627693288396790281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9757991007182102391440749 3659246627693288396790281)
          ·
            refine ⟨2744434970769966297592711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3659246627693288396790281 2744434970769966297592711)
            ·
              refine ⟨4116652456154949446389067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744434970769966297592711 4116652456154949446389067)
              ·
                refine ⟨6174978684232424169583601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4116652456154949446389067 6174978684232424169583601)
                ·
                  refine ⟨4631234013174318127187701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6174978684232424169583601 4631234013174318127187701)
                  ·
                    refine ⟨434178188735092324423847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4631234013174318127187701 434178188735092324423847)
                    ·
                      rfl

theorem cell23_2536677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_2536677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536677 prefixEnd_2536677 := by exact prefixLift 2536677
  have htrace : WordTrace (prefixWord ++ tailWord_2536677) baseStart_2536677 baseEnd_2536677 := by
    simpa [prefixWord, tailWord_2536677, baseEnd_2536677] using wordTrace_append hprefix tailTrace_2536677
  have hstable : (prefixWord ++ tailWord_2536677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536677).length < 2 ^ (prefixWord ++ tailWord_2536677).sum := by decide
  have hdescent : baseEnd_2536677 < baseStart_2536677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536680 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_2536680 : Nat := 118140960795 + 2536680 * 2 ^ 59
def prefixEnd_2536680 : Nat := 4983230072969 + 3 ^ 40 * 2536680 * 2
def baseEnd_2536680 : Nat := 1302536106647240461534027

theorem tailTrace_2536680 : CollatzResearch.WordTrace tailWord_2536680 prefixEnd_2536680 1302536106647240461534027 := by
  unfold tailWord_2536680
  simp only [CollatzResearch.WordTrace]
  refine ⟨46260160225024532648935747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61680213633366043531914329 46260160225024532648935747)
  ·
    refine ⟨69390240337536798973403621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46260160225024532648935747 69390240337536798973403621)
    ·
      refine ⟨13010670063288149807513179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69390240337536798973403621 13010670063288149807513179)
      ·
        refine ⟨19516005094932224711269769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13010670063288149807513179 19516005094932224711269769)
        ·
          refine ⟨14637003821199168533452327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19516005094932224711269769 14637003821199168533452327)
          ·
            refine ⟨21955505731798752800178491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14637003821199168533452327 21955505731798752800178491)
            ·
              refine ⟨32933258597698129200267737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21955505731798752800178491 32933258597698129200267737)
              ·
                refine ⟨24699943948273596900200803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32933258597698129200267737 24699943948273596900200803)
                ·
                  refine ⟨37049915922410395350301205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24699943948273596900200803 37049915922410395350301205)
                  ·
                    refine ⟨1736714808862987282045369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37049915922410395350301205 1736714808862987282045369)
                    ·
                      refine ⟨1302536106647240461534027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736714808862987282045369 1302536106647240461534027)
                      ·
                        rfl

theorem cell23_2536680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_2536680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536680 prefixEnd_2536680 := by exact prefixLift 2536680
  have htrace : WordTrace (prefixWord ++ tailWord_2536680) baseStart_2536680 baseEnd_2536680 := by
    simpa [prefixWord, tailWord_2536680, baseEnd_2536680] using wordTrace_append hprefix tailTrace_2536680
  have hstable : (prefixWord ++ tailWord_2536680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536680).length < 2 ^ (prefixWord ++ tailWord_2536680).sum := by decide
  have hdescent : baseEnd_2536680 < baseStart_2536680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536692 : List Nat := [2, 6, 1, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2536692 : Nat := 118140960795 + 2536692 * 2 ^ 59
def prefixEnd_2536692 : Nat := 4983230072969 + 3 ^ 40 * 2536692 * 2
def baseEnd_2536692 : Nat := 1302542268415094414583973

theorem tailTrace_2536692 : CollatzResearch.WordTrace tailWord_2536692 prefixEnd_2536692 1302542268415094414583973 := by
  unfold tailWord_2536692
  simp only [CollatzResearch.WordTrace]
  refine ⟨46260379063002795673654165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61680505417337060898205553 46260379063002795673654165)
  ·
    refine ⟨2168455268578256047202539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46260379063002795673654165 2168455268578256047202539)
    ·
      refine ⟨3252682902867384070803809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2168455268578256047202539 3252682902867384070803809)
      ·
        refine ⟨2439512177150538053102857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3252682902867384070803809 2439512177150538053102857)
        ·
          refine ⟨1829634132862903539827143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2439512177150538053102857 1829634132862903539827143)
          ·
            refine ⟨2744451199294355309740715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1829634132862903539827143 2744451199294355309740715)
            ·
              refine ⟨4116676798941532964611073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744451199294355309740715 4116676798941532964611073)
              ·
                refine ⟨3087507599206149723458305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4116676798941532964611073 3087507599206149723458305)
                ·
                  refine ⟨2315630699404612292593729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3087507599206149723458305 2315630699404612292593729)
                  ·
                    refine ⟨1736723024553459219445297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2315630699404612292593729 1736723024553459219445297)
                    ·
                      refine ⟨1302542268415094414583973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736723024553459219445297 1302542268415094414583973)
                      ·
                        rfl

theorem cell23_2536692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2536692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536692 prefixEnd_2536692 := by exact prefixLift 2536692
  have htrace : WordTrace (prefixWord ++ tailWord_2536692) baseStart_2536692 baseEnd_2536692 := by
    simpa [prefixWord, tailWord_2536692, baseEnd_2536692] using wordTrace_append hprefix tailTrace_2536692
  have hstable : (prefixWord ++ tailWord_2536692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536692).length < 2 ^ (prefixWord ++ tailWord_2536692).sum := by decide
  have hdescent : baseEnd_2536692 < baseStart_2536692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536703 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 8]
def baseStart_2536703 : Nat := 118140960795 + 2536703 * 2 ^ 59
def prefixEnd_2536703 : Nat := 4983230072969 + 3 ^ 40 * 2536703 * 2
def baseEnd_2536703 : Nat := 144727546300254874616269

theorem tailTrace_2536703 : CollatzResearch.WordTrace tailWord_2536703 prefixEnd_2536703 144727546300254874616269 := by
  unfold tailWord_2536703
  simp only [CollatzResearch.WordTrace]
  refine ⟨92521159328965740225958763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61680772885977160150639175 92521159328965740225958763)
  ·
    refine ⟨138781738993448610338938145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92521159328965740225958763 138781738993448610338938145)
    ·
      refine ⟨104086304245086457754203609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138781738993448610338938145 104086304245086457754203609)
      ·
        refine ⟨78064728183814843315652707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104086304245086457754203609 78064728183814843315652707)
        ·
          refine ⟨117097092275722264973479061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78064728183814843315652707 117097092275722264973479061)
          ·
            refine ⟨5488926200424481170631831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117097092275722264973479061 5488926200424481170631831)
            ·
              refine ⟨8233389300636721755947747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5488926200424481170631831 8233389300636721755947747)
              ·
                refine ⟨12350083950955082633921621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8233389300636721755947747 12350083950955082633921621)
                ·
                  refine ⟨144727546300254874616269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12350083950955082633921621 144727546300254874616269)
                  ·
                    rfl

theorem cell23_2536703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 8].length) (baseStart_2536703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536703 prefixEnd_2536703 := by exact prefixLift 2536703
  have htrace : WordTrace (prefixWord ++ tailWord_2536703) baseStart_2536703 baseEnd_2536703 := by
    simpa [prefixWord, tailWord_2536703, baseEnd_2536703] using wordTrace_append hprefix tailTrace_2536703
  have hstable : (prefixWord ++ tailWord_2536703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536703).length < 2 ^ (prefixWord ++ tailWord_2536703).sum := by decide
  have hdescent : baseEnd_2536703 < baseStart_2536703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536707 : List Nat := [1, 1, 1, 3, 2, 4, 2, 4, 1, 4]
def baseStart_2536707 : Nat := 118140960795 + 2536707 * 2 ^ 59
def prefixEnd_2536707 : Nat := 4983230072969 + 3 ^ 40 * 2536707 * 2
def baseEnd_2536707 : Nat := 434183323541637285298801

theorem tailTrace_2536707 : CollatzResearch.WordTrace tailWord_2536707 prefixEnd_2536707 434183323541637285298801 := by
  unfold tailWord_2536707
  simp only [CollatzResearch.WordTrace]
  refine ⟨92521305220951248909104375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61680870147300832606069583 92521305220951248909104375)
  ·
    refine ⟨138781957831426873363656563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92521305220951248909104375 138781957831426873363656563)
    ·
      refine ⟨208172936747140310045484845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138781957831426873363656563 208172936747140310045484845)
      ·
        refine ⟨78064851280177616267056817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208172936747140310045484845 78064851280177616267056817)
        ·
          refine ⟨58548638460133212200292613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78064851280177616267056817 58548638460133212200292613)
          ·
            refine ⟨10977869711274977287554865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58548638460133212200292613 10977869711274977287554865)
            ·
              refine ⟨8233402283456232965666149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10977869711274977287554865 8233402283456232965666149)
              ·
                refine ⟨1543762928148043681062403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8233402283456232965666149 1543762928148043681062403)
                ·
                  refine ⟨2315644392222065521593605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543762928148043681062403 2315644392222065521593605)
                  ·
                    refine ⟨434183323541637285298801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2315644392222065521593605 434183323541637285298801)
                    ·
                      rfl

theorem cell23_2536707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 1, 4].length) (baseStart_2536707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536707 prefixEnd_2536707 := by exact prefixLift 2536707
  have htrace : WordTrace (prefixWord ++ tailWord_2536707) baseStart_2536707 baseEnd_2536707 := by
    simpa [prefixWord, tailWord_2536707, baseEnd_2536707] using wordTrace_append hprefix tailTrace_2536707
  have hstable : (prefixWord ++ tailWord_2536707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536707).length < 2 ^ (prefixWord ++ tailWord_2536707).sum := by decide
  have hdescent : baseEnd_2536707 < baseStart_2536707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536757 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_2536757 : Nat := 118140960795 + 2536757 * 2 ^ 59
def prefixEnd_2536757 : Nat := 4983230072969 + 3 ^ 40 * 2536757 * 2
def baseEnd_2536757 : Nat := 1302575644657636660271173

theorem tailTrace_2536757 : CollatzResearch.WordTrace tailWord_2536757 prefixEnd_2536757 1302575644657636660271173 := by
  unfold tailWord_2536757
  simp only [CollatzResearch.WordTrace]
  refine ⟨92523128870770107448424525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61682085913846738298949683 92523128870770107448424525)
  ·
    refine ⟨34696173326538790293159197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92523128870770107448424525 34696173326538790293159197)
    ·
      refine ⟨13011064997452046359934699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34696173326538790293159197 13011064997452046359934699)
      ·
        refine ⟨19516597496178069539902049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13011064997452046359934699 19516597496178069539902049)
        ·
          refine ⟨14637448122133552154926537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19516597496178069539902049 14637448122133552154926537)
          ·
            refine ⟨10978086091600164116194903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14637448122133552154926537 10978086091600164116194903)
            ·
              refine ⟨16467129137400246174292355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10978086091600164116194903 16467129137400246174292355)
              ·
                refine ⟨24700693706100369261438533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16467129137400246174292355 24700693706100369261438533)
                ·
                  refine ⟨4631380069893819236519725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24700693706100369261438533 4631380069893819236519725)
                  ·
                    refine ⟨1736767526210182213694897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4631380069893819236519725 1736767526210182213694897)
                    ·
                      refine ⟨1302575644657636660271173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736767526210182213694897 1302575644657636660271173)
                      ·
                        rfl

theorem cell23_2536757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_2536757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536757 prefixEnd_2536757 := by exact prefixLift 2536757
  have htrace : WordTrace (prefixWord ++ tailWord_2536757) baseStart_2536757 baseEnd_2536757 := by
    simpa [prefixWord, tailWord_2536757, baseEnd_2536757] using wordTrace_append hprefix tailTrace_2536757
  have hstable : (prefixWord ++ tailWord_2536757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536757).length < 2 ^ (prefixWord ++ tailWord_2536757).sum := by decide
  have hdescent : baseEnd_2536757 < baseStart_2536757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536758 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_2536758 : Nat := 118140960795 + 2536758 * 2 ^ 59
def prefixEnd_2536758 : Nat := 4983230072969 + 3 ^ 40 * 2536758 * 2
def baseEnd_2536758 : Nat := 434192052712763718786223

theorem tailTrace_2536758 : CollatzResearch.WordTrace tailWord_2536758 prefixEnd_2536758 434192052712763718786223 := by
  unfold tailWord_2536758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5782697833985405288700683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61682110229177656412807285 5782697833985405288700683)
  ·
    refine ⟨8674046750978107933051025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5782697833985405288700683 8674046750978107933051025)
    ·
      refine ⟨6505535063233580949788269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8674046750978107933051025 6505535063233580949788269)
      ·
        refine ⟨2439575648712592856170601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6505535063233580949788269 2439575648712592856170601)
        ·
          refine ⟨1829681736534444642127951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2439575648712592856170601 1829681736534444642127951)
          ·
            refine ⟨2744522604801666963191927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1829681736534444642127951 2744522604801666963191927)
            ·
              refine ⟨4116783907202500444787891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744522604801666963191927 4116783907202500444787891)
              ·
                refine ⟨6175175860803750667181837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4116783907202500444787891 6175175860803750667181837)
                ·
                  refine ⟨2315690947801406500193189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6175175860803750667181837 2315690947801406500193189)
                  ·
                    refine ⟨434192052712763718786223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2315690947801406500193189 434192052712763718786223)
                    ·
                      rfl

theorem cell23_2536758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_2536758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536758 prefixEnd_2536758 := by exact prefixLift 2536758
  have htrace : WordTrace (prefixWord ++ tailWord_2536758) baseStart_2536758 baseEnd_2536758 := by
    simpa [prefixWord, tailWord_2536758, baseEnd_2536758] using wordTrace_append hprefix tailTrace_2536758
  have hstable : (prefixWord ++ tailWord_2536758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536758).length < 2 ^ (prefixWord ++ tailWord_2536758).sum := by decide
  have hdescent : baseEnd_2536758 < baseStart_2536758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536764 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 3, 1, 3]
def baseStart_2536764 : Nat := 118140960795 + 2536764 * 2 ^ 59
def prefixEnd_2536764 : Nat := 4983230072969 + 3 ^ 40 * 2536764 * 2
def baseEnd_2536764 : Nat := 1302579239022218132883641

theorem tailTrace_2536764 : CollatzResearch.WordTrace tailWord_2536764 prefixEnd_2536764 1302579239022218132883641 := by
  unfold tailWord_2536764
  simp only [CollatzResearch.WordTrace]
  refine ⟨46261692090872373821964673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61682256121163165095952897 46261692090872373821964673)
  ·
    refine ⟨34696269068154280366473505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46261692090872373821964673 34696269068154280366473505)
    ·
      refine ⟨26022201801115710274855129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34696269068154280366473505 26022201801115710274855129)
      ·
        refine ⟨19516651350836782706141347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26022201801115710274855129 19516651350836782706141347)
        ·
          refine ⟨29274977026255174059212021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19516651350836782706141347 29274977026255174059212021)
          ·
            refine ⟨2744529096211422568051127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29274977026255174059212021 2744529096211422568051127)
            ·
              refine ⟨4116793644317133852076691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744529096211422568051127 4116793644317133852076691)
              ·
                refine ⟨6175190466475700778115037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4116793644317133852076691 6175190466475700778115037)
                ·
                  refine ⟨2315696424928387791793139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6175190466475700778115037 2315696424928387791793139)
                  ·
                    refine ⟨3473544637392581687689709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2315696424928387791793139 3473544637392581687689709)
                    ·
                      refine ⟨1302579239022218132883641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3473544637392581687689709 1302579239022218132883641)
                      ·
                        rfl

theorem cell23_2536764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_2536764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536764 prefixEnd_2536764 := by exact prefixLift 2536764
  have htrace : WordTrace (prefixWord ++ tailWord_2536764) baseStart_2536764 baseEnd_2536764 := by
    simpa [prefixWord, tailWord_2536764, baseEnd_2536764] using wordTrace_append hprefix tailTrace_2536764
  have hstable : (prefixWord ++ tailWord_2536764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536764).length < 2 ^ (prefixWord ++ tailWord_2536764).sum := by decide
  have hdescent : baseEnd_2536764 < baseStart_2536764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536787 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 5, 2, 2]
def baseStart_2536787 : Nat := 118140960795 + 2536787 * 2 ^ 59
def prefixEnd_2536787 : Nat := 4983230072969 + 3 ^ 40 * 2536787 * 2
def baseEnd_2536787 : Nat := 1302591049077271542896035

theorem tailTrace_2536787 : CollatzResearch.WordTrace tailWord_2536787 prefixEnd_2536787 1302591049077271542896035 := by
  unfold tailWord_2536787
  simp only [CollatzResearch.WordTrace]
  refine ⟨92524223060661422572016615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61682815373774281714677743 92524223060661422572016615)
  ·
    refine ⟨138786334590992133858024923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92524223060661422572016615 138786334590992133858024923)
    ·
      refine ⟨208179501886488200787037385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138786334590992133858024923 208179501886488200787037385)
      ·
        refine ⟨156134626414866150590278039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208179501886488200787037385 156134626414866150590278039)
        ·
          refine ⟨234201939622299225885417059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156134626414866150590278039 234201939622299225885417059)
          ·
            refine ⟨351302909433448838828125589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234201939622299225885417059 351302909433448838828125589)
            ·
              refine ⟨16467323879692914320068387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 351302909433448838828125589 16467323879692914320068387)
              ·
                refine ⟨24700985819539371480102581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16467323879692914320068387 24700985819539371480102581)
                ·
                  refine ⟨2315717420581816076259617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24700985819539371480102581 2315717420581816076259617)
                  ·
                    refine ⟨1736788065436362057194713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2315717420581816076259617 1736788065436362057194713)
                    ·
                      refine ⟨1302591049077271542896035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736788065436362057194713 1302591049077271542896035)
                      ·
                        rfl

theorem cell23_2536787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 2, 2].length) (baseStart_2536787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536787 prefixEnd_2536787 := by exact prefixLift 2536787
  have htrace : WordTrace (prefixWord ++ tailWord_2536787) baseStart_2536787 baseEnd_2536787 := by
    simpa [prefixWord, tailWord_2536787, baseEnd_2536787] using wordTrace_append hprefix tailTrace_2536787
  have hstable : (prefixWord ++ tailWord_2536787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536787).length < 2 ^ (prefixWord ++ tailWord_2536787).sum := by decide
  have hdescent : baseEnd_2536787 < baseStart_2536787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536793 : List Nat := [1, 2, 1, 2, 2, 2, 4, 9]
def baseStart_2536793 : Nat := 118140960795 + 2536793 * 2 ^ 59
def prefixEnd_2536793 : Nat := 4983230072969 + 3 ^ 40 * 2536793 * 2
def baseEnd_2536793 : Nat := 48244227035599945163741

theorem tailTrace_2536793 : CollatzResearch.WordTrace tailWord_2536793 prefixEnd_2536793 48244227035599945163741 := by
  unfold tailWord_2536793
  simp only [CollatzResearch.WordTrace]
  refine ⟨92524441898639685596735033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61682961265759790397823355 92524441898639685596735033)
  ·
    refine ⟨69393331423979764197551275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92524441898639685596735033 69393331423979764197551275)
    ·
      refine ⟨104089997135969646296326913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69393331423979764197551275 104089997135969646296326913)
      ·
        refine ⟨78067497851977234722245185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104089997135969646296326913 78067497851977234722245185)
        ·
          refine ⟨58550623388982926041683889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78067497851977234722245185 58550623388982926041683889)
          ·
            refine ⟨43912967541737194531262917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58550623388982926041683889 43912967541737194531262917)
            ·
              refine ⟨8233681414075723974611797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43912967541737194531262917 8233681414075723974611797)
              ·
                refine ⟨48244227035599945163741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8233681414075723974611797 48244227035599945163741)
                ·
                  rfl

theorem cell23_2536793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 9].length) (baseStart_2536793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536793 prefixEnd_2536793 := by exact prefixLift 2536793
  have htrace : WordTrace (prefixWord ++ tailWord_2536793) baseStart_2536793 baseEnd_2536793 := by
    simpa [prefixWord, tailWord_2536793, baseEnd_2536793] using wordTrace_append hprefix tailTrace_2536793
  have hstable : (prefixWord ++ tailWord_2536793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536793).length < 2 ^ (prefixWord ++ tailWord_2536793).sum := by decide
  have hdescent : baseEnd_2536793 < baseStart_2536793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536800 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 4]
def baseStart_2536800 : Nat := 118140960795 + 2536800 * 2 ^ 59
def prefixEnd_2536800 : Nat := 4983230072969 + 3 ^ 40 * 2536800 * 2
def baseEnd_2536800 : Nat := 1302597724325779992033475

theorem tailTrace_2536800 : CollatzResearch.WordTrace tailWord_2536800 prefixEnd_2536800 1302597724325779992033475 := by
  unfold tailWord_2536800
  simp only [CollatzResearch.WordTrace]
  refine ⟨46262348604807162896119927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61683131473076217194826569 46262348604807162896119927)
  ·
    refine ⟨69393522907210744344179891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46262348604807162896119927 69393522907210744344179891)
    ·
      refine ⟨104090284360816116516269837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69393522907210744344179891 104090284360816116516269837)
      ·
        refine ⟨39033856635306043693601189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104090284360816116516269837 39033856635306043693601189)
        ·
          refine ⟨7318848119119883192550223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39033856635306043693601189 7318848119119883192550223)
          ·
            refine ⟨10978272178679824788825335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7318848119119883192550223 10978272178679824788825335)
            ·
              refine ⟨16467408268019737183238003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10978272178679824788825335 16467408268019737183238003)
              ·
                refine ⟨24701112402029605774857005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16467408268019737183238003 24701112402029605774857005)
                ·
                  refine ⟨9262917150761102165571377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24701112402029605774857005 9262917150761102165571377)
                  ·
                    refine ⟨6947187863070826624178533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9262917150761102165571377 6947187863070826624178533)
                    ·
                      refine ⟨1302597724325779992033475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6947187863070826624178533 1302597724325779992033475)
                      ·
                        rfl

theorem cell23_2536800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_2536800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536800 prefixEnd_2536800 := by exact prefixLift 2536800
  have htrace : WordTrace (prefixWord ++ tailWord_2536800) baseStart_2536800 baseEnd_2536800 := by
    simpa [prefixWord, tailWord_2536800, baseEnd_2536800] using wordTrace_append hprefix tailTrace_2536800
  have hstable : (prefixWord ++ tailWord_2536800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536800).length < 2 ^ (prefixWord ++ tailWord_2536800).sum := by decide
  have hdescent : baseEnd_2536800 < baseStart_2536800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536804 : List Nat := [2, 3, 1, 1, 3, 3, 3, 1, 1, 1, 4]
def baseStart_2536804 : Nat := 118140960795 + 2536804 * 2 ^ 59
def prefixEnd_2536804 : Nat := 4983230072969 + 3 ^ 40 * 2536804 * 2
def baseEnd_2536804 : Nat := 1302599778248397976383457

theorem tailTrace_2536804 : CollatzResearch.WordTrace tailWord_2536804 prefixEnd_2536804 1302599778248397976383457 := by
  unfold tailWord_2536804
  simp only [CollatzResearch.WordTrace]
  refine ⟨46262421550799917237692733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61683228734399889650256977 46262421550799917237692733)
  ·
    refine ⟨17348408081549968964134775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46262421550799917237692733 17348408081549968964134775)
    ·
      refine ⟨26022612122324953446202163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17348408081549968964134775 26022612122324953446202163)
      ·
        refine ⟨39033918183487430169303245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26022612122324953446202163 39033918183487430169303245)
        ·
          refine ⟨14637719318807786313488717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39033918183487430169303245 14637719318807786313488717)
          ·
            refine ⟨5489144744552919867558269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14637719318807786313488717 5489144744552919867558269)
            ·
              refine ⟨2058429279207344950334351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5489144744552919867558269 2058429279207344950334351)
              ·
                refine ⟨3087643918811017425501527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2058429279207344950334351 3087643918811017425501527)
                ·
                  refine ⟨4631465878216526138252291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087643918811017425501527 4631465878216526138252291)
                  ·
                    refine ⟨6947198817324789207378437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4631465878216526138252291 6947198817324789207378437)
                    ·
                      refine ⟨1302599778248397976383457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6947198817324789207378437 1302599778248397976383457)
                      ·
                        rfl

theorem cell23_2536804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_2536804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536804 prefixEnd_2536804 := by exact prefixLift 2536804
  have htrace : WordTrace (prefixWord ++ tailWord_2536804) baseStart_2536804 baseEnd_2536804 := by
    simpa [prefixWord, tailWord_2536804, baseEnd_2536804] using wordTrace_append hprefix tailTrace_2536804
  have hstable : (prefixWord ++ tailWord_2536804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536804).length < 2 ^ (prefixWord ++ tailWord_2536804).sum := by decide
  have hdescent : baseEnd_2536804 < baseStart_2536804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536810 : List Nat := [3, 1, 3, 3, 2, 11]
def baseStart_2536810 : Nat := 118140960795 + 2536810 * 2 ^ 59
def prefixEnd_2536810 : Nat := 4983230072969 + 3 ^ 40 * 2536810 * 2
def baseEnd_2536810 : Nat := 5360505593137139723903

theorem tailTrace_2536810 : CollatzResearch.WordTrace tailWord_2536810 prefixEnd_2536810 5360505593137139723903 := by
  unfold tailWord_2536810
  simp only [CollatzResearch.WordTrace]
  refine ⟨23131265484894524375025971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61683374626385398333402589 23131265484894524375025971)
  ·
    refine ⟨34696898227341786562538957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23131265484894524375025971 34696898227341786562538957)
    ·
      refine ⟨13011336835253169960952109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34696898227341786562538957 13011336835253169960952109)
      ·
        refine ⟨4879251313219938735357041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13011336835253169960952109 4879251313219938735357041)
        ·
          refine ⟨3659438484914954051517781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4879251313219938735357041 3659438484914954051517781)
          ·
            refine ⟨5360505593137139723903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3659438484914954051517781 5360505593137139723903)
            ·
              rfl

theorem cell23_2536810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 11].length) (baseStart_2536810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536810 prefixEnd_2536810 := by exact prefixLift 2536810
  have htrace : WordTrace (prefixWord ++ tailWord_2536810) baseStart_2536810 baseEnd_2536810 := by
    simpa [prefixWord, tailWord_2536810, baseEnd_2536810] using wordTrace_append hprefix tailTrace_2536810
  have hstable : (prefixWord ++ tailWord_2536810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536810).length < 2 ^ (prefixWord ++ tailWord_2536810).sum := by decide
  have hdescent : baseEnd_2536810 < baseStart_2536810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536823 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 1, 9]
def baseStart_2536823 : Nat := 118140960795 + 2536823 * 2 ^ 59
def prefixEnd_2536823 : Nat := 4983230072969 + 3 ^ 40 * 2536823 * 2
def baseEnd_2536823 : Nat := 434203178126944467348623

theorem tailTrace_2536823 : CollatzResearch.WordTrace tailWord_2536823 prefixEnd_2536823 434203178126944467348623 := by
  unfold tailWord_2536823
  simp only [CollatzResearch.WordTrace]
  refine ⟨92525536088531000720327123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61683690725687333813551415 92525536088531000720327123)
  ·
    refine ⟨138788304132796501080490685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92525536088531000720327123 138788304132796501080490685)
    ·
      refine ⟨52045614049798687905184007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138788304132796501080490685 52045614049798687905184007)
      ·
        refine ⟨78068421074698031857776011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52045614049798687905184007 78068421074698031857776011)
        ·
          refine ⟨117102631612047047786664017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78068421074698031857776011 117102631612047047786664017)
          ·
            refine ⟨87826973709035285839998013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117102631612047047786664017 87826973709035285839998013)
            ·
              refine ⟨32935115140888232189999255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87826973709035285839998013 32935115140888232189999255)
              ·
                refine ⟨49402672711332348284998883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32935115140888232189999255 49402672711332348284998883)
                ·
                  refine ⟨74104009066998522427498325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49402672711332348284998883 74104009066998522427498325)
                  ·
                    refine ⟨434203178126944467348623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 74104009066998522427498325 434203178126944467348623)
                    ·
                      rfl

theorem cell23_2536823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_2536823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536823 prefixEnd_2536823 := by exact prefixLift 2536823
  have htrace : WordTrace (prefixWord ++ tailWord_2536823) baseStart_2536823 baseEnd_2536823 := by
    simpa [prefixWord, tailWord_2536823, baseEnd_2536823] using wordTrace_append hprefix tailTrace_2536823
  have hstable : (prefixWord ++ tailWord_2536823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536823).length < 2 ^ (prefixWord ++ tailWord_2536823).sum := by decide
  have hdescent : baseEnd_2536823 < baseStart_2536823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536834 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_2536834 : Nat := 118140960795 + 2536834 * 2 ^ 59
def prefixEnd_2536834 : Nat := 4983230072969 + 3 ^ 40 * 2536834 * 2
def baseEnd_2536834 : Nat := 1302615182668032859008319

theorem tailTrace_2536834 : CollatzResearch.WordTrace tailWord_2536834 prefixEnd_2536834 1302615182668032859008319 := by
  unfold tailWord_2536834
  simp only [CollatzResearch.WordTrace]
  refine ⟨23131484322872787399744389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61683958194327433065985037 23131484322872787399744389)
  ·
    refine ⟨4337153310538647637452073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23131484322872787399744389 4337153310538647637452073)
    ·
      refine ⟨3252864982903985728089055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4337153310538647637452073 3252864982903985728089055)
      ·
        refine ⟨4879297474355978592133583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3252864982903985728089055 4879297474355978592133583)
        ·
          refine ⟨7318946211533967888200375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4879297474355978592133583 7318946211533967888200375)
          ·
            refine ⟨10978419317300951832300563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7318946211533967888200375 10978419317300951832300563)
            ·
              refine ⟨16467628975951427748450845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10978419317300951832300563 16467628975951427748450845)
              ·
                refine ⟨6175360865981785405669067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16467628975951427748450845 6175360865981785405669067)
                ·
                  refine ⟨9263041298972678108503601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6175360865981785405669067 9263041298972678108503601)
                  ·
                    refine ⟨6947280974229508581377701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9263041298972678108503601 6947280974229508581377701)
                    ·
                      refine ⟨1302615182668032859008319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6947280974229508581377701 1302615182668032859008319)
                      ·
                        rfl

theorem cell23_2536834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_2536834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536834 prefixEnd_2536834 := by exact prefixLift 2536834
  have htrace : WordTrace (prefixWord ++ tailWord_2536834) baseStart_2536834 baseEnd_2536834 := by
    simpa [prefixWord, tailWord_2536834, baseEnd_2536834] using wordTrace_append hprefix tailTrace_2536834
  have hstable : (prefixWord ++ tailWord_2536834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536834).length < 2 ^ (prefixWord ++ tailWord_2536834).sum := by decide
  have hdescent : baseEnd_2536834 < baseStart_2536834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536864 : List Nat := [2, 1, 1, 4, 1, 2, 3, 3, 1, 3, 2]
def baseStart_2536864 : Nat := 118140960795 + 2536864 * 2 ^ 59
def prefixEnd_2536864 : Nat := 4983230072969 + 3 ^ 40 * 2536864 * 2
def baseEnd_2536864 : Nat := 1302630587087667741633181

theorem tailTrace_2536864 : CollatzResearch.WordTrace tailWord_2536864 prefixEnd_2536864 1302630587087667741633181 := by
  unfold tailWord_2536864
  simp only [CollatzResearch.WordTrace]
  refine ⟨46263515740691232361284823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61684687654254976481713097 46263515740691232361284823)
  ·
    refine ⟨69395273611036848541927235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46263515740691232361284823 69395273611036848541927235)
    ·
      refine ⟨104092910416555272812890853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69395273611036848541927235 104092910416555272812890853)
      ·
        refine ⟨19517420703104113652417035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104092910416555272812890853 19517420703104113652417035)
        ·
          refine ⟨29276131054656170478625553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19517420703104113652417035 29276131054656170478625553)
          ·
            refine ⟨21957098290992127858969165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29276131054656170478625553 21957098290992127858969165)
            ·
              refine ⟨8233911859122047947113437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21957098290992127858969165 8233911859122047947113437)
              ·
                refine ⟨3087716947170767980167539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8233911859122047947113437 3087716947170767980167539)
                ·
                  refine ⟨4631575420756151970251309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3087716947170767980167539 4631575420756151970251309)
                  ·
                    refine ⟨1736840782783556988844241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4631575420756151970251309 1736840782783556988844241)
                    ·
                      refine ⟨1302630587087667741633181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1736840782783556988844241 1302630587087667741633181)
                      ·
                        rfl

theorem cell23_2536864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_2536864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536864 prefixEnd_2536864 := by exact prefixLift 2536864
  have htrace : WordTrace (prefixWord ++ tailWord_2536864) baseStart_2536864 baseEnd_2536864 := by
    simpa [prefixWord, tailWord_2536864, baseEnd_2536864] using wordTrace_append hprefix tailTrace_2536864
  have hstable : (prefixWord ++ tailWord_2536864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536864).length < 2 ^ (prefixWord ++ tailWord_2536864).sum := by decide
  have hdescent : baseEnd_2536864 < baseStart_2536864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2536880 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 3]
def baseStart_2536880 : Nat := 118140960795 + 2536880 * 2 ^ 59
def prefixEnd_2536880 : Nat := 4983230072969 + 3 ^ 40 * 2536880 * 2
def baseEnd_2536880 : Nat := 1302638802778139679033107

theorem tailTrace_2536880 : CollatzResearch.WordTrace tailWord_2536880 prefixEnd_2536880 1302638802778139679033107 := by
  unfold tailWord_2536880
  simp only [CollatzResearch.WordTrace]
  refine ⟨46263807524662249727576047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61685076699549666303434729 46263807524662249727576047)
  ·
    refine ⟨69395711286993374591364071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46263807524662249727576047 69395711286993374591364071)
    ·
      refine ⟨104093566930490061887046107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69395711286993374591364071 104093566930490061887046107)
      ·
        refine ⟨156140350395735092830569161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104093566930490061887046107 156140350395735092830569161)
        ·
          refine ⟨117105262796801319622926871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156140350395735092830569161 117105262796801319622926871)
          ·
            refine ⟨175657894195201979434390307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117105262796801319622926871 175657894195201979434390307)
            ·
              refine ⟨263486841292802969151585461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175657894195201979434390307 263486841292802969151585461)
              ·
                refine ⟨24701891371200278357961137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 263486841292802969151585461 24701891371200278357961137)
                ·
                  refine ⟨18526418528400208768470853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24701891371200278357961137 18526418528400208768470853)
                  ·
                    refine ⟨3473703474075039144088285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18526418528400208768470853 3473703474075039144088285)
                    ·
                      refine ⟨1302638802778139679033107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3473703474075039144088285 1302638802778139679033107)
                      ·
                        rfl

theorem cell23_2536880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 3].length) (baseStart_2536880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2536880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2536880 prefixEnd_2536880 := by exact prefixLift 2536880
  have htrace : WordTrace (prefixWord ++ tailWord_2536880) baseStart_2536880 baseEnd_2536880 := by
    simpa [prefixWord, tailWord_2536880, baseEnd_2536880] using wordTrace_append hprefix tailTrace_2536880
  have hstable : (prefixWord ++ tailWord_2536880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2536880).length < 2 ^ (prefixWord ++ tailWord_2536880).sum := by decide
  have hdescent : baseEnd_2536880 < baseStart_2536880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2536880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537034 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 5, 1, 3]
def baseStart_2537034 : Nat := 118140960795 + 2537034 * 2 ^ 59
def prefixEnd_2537034 : Nat := 4983230072969 + 3 ^ 40 * 2537034 * 2
def baseEnd_2537034 : Nat := 1302717878798932076507399

theorem tailTrace_2537034 : CollatzResearch.WordTrace tailWord_2537034 prefixEnd_2537034 1302717878798932076507399 := by
  unfold tailWord_2537034
  simp only [CollatzResearch.WordTrace]
  refine ⟨23133307972691645939064539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61688821260511055837505437 23133307972691645939064539)
  ·
    refine ⟨34699961959037468908596809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23133307972691645939064539 34699961959037468908596809)
    ·
      refine ⟨26024971469278101681447607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34699961959037468908596809 26024971469278101681447607)
      ·
        refine ⟨39037457203917152522171411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26024971469278101681447607 39037457203917152522171411)
        ·
          refine ⟨58556185805875728783257117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39037457203917152522171411 58556185805875728783257117)
          ·
            refine ⟨21958569677203398293721419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58556185805875728783257117 21958569677203398293721419)
            ·
              refine ⟨32937854515805097440582129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21958569677203398293721419 32937854515805097440582129)
              ·
                refine ⟨24703390886853823080436597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32937854515805097440582129 24703390886853823080436597)
                ·
                  refine ⟨2315942895642545913790931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24703390886853823080436597 2315942895642545913790931)
                  ·
                    refine ⟨3473914343463818870686397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2315942895642545913790931 3473914343463818870686397)
                    ·
                      refine ⟨1302717878798932076507399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3473914343463818870686397 1302717878798932076507399)
                      ·
                        rfl

theorem cell23_2537034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_2537034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537034 prefixEnd_2537034 := by exact prefixLift 2537034
  have htrace : WordTrace (prefixWord ++ tailWord_2537034) baseStart_2537034 baseEnd_2537034 := by
    simpa [prefixWord, tailWord_2537034, baseEnd_2537034] using wordTrace_append hprefix tailTrace_2537034
  have hstable : (prefixWord ++ tailWord_2537034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537034).length < 2 ^ (prefixWord ++ tailWord_2537034).sum := by decide
  have hdescent : baseEnd_2537034 < baseStart_2537034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537085 : List Nat := [1, 4, 1, 1, 4, 3, 1, 3, 1, 1, 3]
def baseStart_2537085 : Nat := 118140960795 + 2537085 * 2 ^ 59
def prefixEnd_2537085 : Nat := 4983230072969 + 3 ^ 40 * 2537085 * 2
def baseEnd_2537085 : Nat := 1302744066312311376969665

theorem tailTrace_2537085 : CollatzResearch.WordTrace tailWord_2537085 prefixEnd_2537085 1302744066312311376969665 := by
  unfold tailWord_2537085
  simp only [CollatzResearch.WordTrace]
  refine ⟨92535092013581819466364709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61690061342387879644243139 92535092013581819466364709)
  ·
    refine ⟨17350329752546591149943383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92535092013581819466364709 17350329752546591149943383)
    ·
      refine ⟨26025494628819886724915075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17350329752546591149943383 26025494628819886724915075)
      ·
        refine ⟨39038241943229830087372613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26025494628819886724915075 39038241943229830087372613)
        ·
          refine ⟨7319670364355593141382365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39038241943229830087372613 7319670364355593141382365)
          ·
            refine ⟨2744876386633347428018387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7319670364355593141382365 2744876386633347428018387)
            ·
              refine ⟨4117314579950021142027581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744876386633347428018387 4117314579950021142027581)
              ·
                refine ⟨1543992967481257928260343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4117314579950021142027581 1543992967481257928260343)
                ·
                  refine ⟨2315989451221886892390515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1543992967481257928260343 2315989451221886892390515)
                  ·
                    refine ⟨3473984176832830338585773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2315989451221886892390515 3473984176832830338585773)
                    ·
                      refine ⟨1302744066312311376969665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3473984176832830338585773 1302744066312311376969665)
                      ·
                        rfl

theorem cell23_2537085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_2537085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537085 prefixEnd_2537085 := by exact prefixLift 2537085
  have htrace : WordTrace (prefixWord ++ tailWord_2537085) baseStart_2537085 baseEnd_2537085 := by
    simpa [prefixWord, tailWord_2537085, baseEnd_2537085] using wordTrace_append hprefix tailTrace_2537085
  have hstable : (prefixWord ++ tailWord_2537085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537085).length < 2 ^ (prefixWord ++ tailWord_2537085).sum := by decide
  have hdescent : baseEnd_2537085 < baseStart_2537085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537107 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 3]
def baseStart_2537107 : Nat := 118140960795 + 2537107 * 2 ^ 59
def prefixEnd_2537107 : Nat := 4983230072969 + 3 ^ 40 * 2537107 * 2
def baseEnd_2537107 : Nat := 1302755362886710290894563

theorem tailTrace_2537107 : CollatzResearch.WordTrace tailWord_2537107 prefixEnd_2537107 1302755362886710290894563 := by
  unfold tailWord_2537107
  simp only [CollatzResearch.WordTrace]
  refine ⟨92535894419502117223665575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61690596279668078149110383 92535894419502117223665575)
  ·
    refine ⟨138803841629253175835498363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92535894419502117223665575 138803841629253175835498363)
    ·
      refine ⟨208205762443879763753247545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138803841629253175835498363 208205762443879763753247545)
      ·
        refine ⟨156154321832909822814935659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208205762443879763753247545 156154321832909822814935659)
        ·
          refine ⟨234231482749364734222403489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156154321832909822814935659 234231482749364734222403489)
          ·
            refine ⟨175673612062023550666802617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234231482749364734222403489 175673612062023550666802617)
            ·
              refine ⟨131755209046517663000101963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175673612062023550666802617 131755209046517663000101963)
              ·
                refine ⟨197632813569776494500152945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131755209046517663000101963 197632813569776494500152945)
                ·
                  refine ⟨148224610177332370875114709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 197632813569776494500152945 148224610177332370875114709)
                  ·
                    refine ⟨3474014301031227442385501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 148224610177332370875114709 3474014301031227442385501)
                    ·
                      refine ⟨1302755362886710290894563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3474014301031227442385501 1302755362886710290894563)
                      ·
                        rfl

theorem cell23_2537107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 3].length) (baseStart_2537107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537107 prefixEnd_2537107 := by exact prefixLift 2537107
  have htrace : WordTrace (prefixWord ++ tailWord_2537107) baseStart_2537107 baseEnd_2537107 := by
    simpa [prefixWord, tailWord_2537107, baseEnd_2537107] using wordTrace_append hprefix tailTrace_2537107
  have hstable : (prefixWord ++ tailWord_2537107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537107).length < 2 ^ (prefixWord ++ tailWord_2537107).sum := by decide
  have hdescent : baseEnd_2537107 < baseStart_2537107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537117 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_2537117 : Nat := 118140960795 + 2537117 * 2 ^ 59
def prefixEnd_2537117 : Nat := 4983230072969 + 3 ^ 40 * 2537117 * 2
def baseEnd_2537117 : Nat := 1302760497693255251769517

theorem tailTrace_2537117 : CollatzResearch.WordTrace tailWord_2537117 prefixEnd_2537117 1302760497693255251769517 := by
  unfold tailWord_2537117
  simp only [CollatzResearch.WordTrace]
  refine ⟨92536259149465888931529605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61690839432977259287686403 92536259149465888931529605)
  ·
    refine ⟨17350548590524854174661801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92536259149465888931529605 17350548590524854174661801)
    ·
      refine ⟨13012911442893640630996351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17350548590524854174661801 13012911442893640630996351)
      ·
        refine ⟨19519367164340460946494527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13012911442893640630996351 19519367164340460946494527)
        ·
          refine ⟨29279050746510691419741791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19519367164340460946494527 29279050746510691419741791)
          ·
            refine ⟨43918576119766037129612687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29279050746510691419741791 43918576119766037129612687)
            ·
              refine ⟨65877864179649055694419031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43918576119766037129612687 65877864179649055694419031)
              ·
                refine ⟨98816796269473583541628547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65877864179649055694419031 98816796269473583541628547)
                ·
                  refine ⟨148225194404210375312442821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98816796269473583541628547 148225194404210375312442821)
                  ·
                    refine ⟨27792223950789445371083029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148225194404210375312442821 27792223950789445371083029)
                    ·
                      refine ⟨1302760497693255251769517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27792223950789445371083029 1302760497693255251769517)
                      ·
                        rfl

theorem cell23_2537117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_2537117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537117 prefixEnd_2537117 := by exact prefixLift 2537117
  have htrace : WordTrace (prefixWord ++ tailWord_2537117) baseStart_2537117 baseEnd_2537117 := by
    simpa [prefixWord, tailWord_2537117, baseEnd_2537117] using wordTrace_append hprefix tailTrace_2537117
  have hstable : (prefixWord ++ tailWord_2537117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537117).length < 2 ^ (prefixWord ++ tailWord_2537117).sum := by decide
  have hdescent : baseEnd_2537117 < baseStart_2537117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537118 : List Nat := [4, 3, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_2537118 : Nat := 118140960795 + 2537118 * 2 ^ 59
def prefixEnd_2537118 : Nat := 4983230072969 + 3 ^ 40 * 2537118 * 2
def baseEnd_2537118 : Nat := 434253670391303249285671

theorem tailTrace_2537118 : CollatzResearch.WordTrace tailWord_2537118 prefixEnd_2537118 434253670391303249285671 := by
  unfold tailWord_2537118
  simp only [CollatzResearch.WordTrace]
  refine ⟨11567036952807783262789501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61690863748308177401544005 11567036952807783262789501)
  ·
    refine ⟨4337638857302918723546063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11567036952807783262789501 4337638857302918723546063)
    ·
      refine ⟨6506458285954378085319095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4337638857302918723546063 6506458285954378085319095)
      ·
        refine ⟨9759687428931567127978643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6506458285954378085319095 9759687428931567127978643)
        ·
          refine ⟨14639531143397350691967965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9759687428931567127978643 14639531143397350691967965)
          ·
            refine ⟨5489824178774006509487987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14639531143397350691967965 5489824178774006509487987)
            ·
              refine ⟨8234736268161009764231981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5489824178774006509487987 8234736268161009764231981)
              ·
                refine ⟨3088026100560378661586993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8234736268161009764231981 3088026100560378661586993)
                ·
                  refine ⟨2316019575420283996190245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3088026100560378661586993 2316019575420283996190245)
                  ·
                    refine ⟨434253670391303249285671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2316019575420283996190245 434253670391303249285671)
                    ·
                      rfl

theorem cell23_2537118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_2537118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537118 prefixEnd_2537118 := by exact prefixLift 2537118
  have htrace : WordTrace (prefixWord ++ tailWord_2537118) baseStart_2537118 baseEnd_2537118 := by
    simpa [prefixWord, tailWord_2537118, baseEnd_2537118] using wordTrace_append hprefix tailTrace_2537118
  have hstable : (prefixWord ++ tailWord_2537118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537118).length < 2 ^ (prefixWord ++ tailWord_2537118).sum := by decide
  have hdescent : baseEnd_2537118 < baseStart_2537118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537147 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 4]
def baseStart_2537147 : Nat := 118140960795 + 2537147 * 2 ^ 59
def prefixEnd_2537147 : Nat := 4983230072969 + 3 ^ 40 * 2537147 * 2
def baseEnd_2537147 : Nat := 1302775902112890134394379

theorem tailTrace_2537147 : CollatzResearch.WordTrace tailWord_2537147 prefixEnd_2537147 1302775902112890134394379 := by
  unfold tailWord_2537147
  simp only [CollatzResearch.WordTrace]
  refine ⟨92537353339357204055121695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61691568892904802703414463 92537353339357204055121695)
  ·
    refine ⟨138806030009035806082682543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92537353339357204055121695 138806030009035806082682543)
    ·
      refine ⟨208209045013553709124023815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138806030009035806082682543 208209045013553709124023815)
      ·
        refine ⟨312313567520330563686035723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208209045013553709124023815 312313567520330563686035723)
        ·
          refine ⟨468470351280495845529053585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312313567520330563686035723 468470351280495845529053585)
          ·
            refine ⟨351352763460371884146790189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468470351280495845529053585 351352763460371884146790189)
            ·
              refine ⟨131757286297639456555046321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 351352763460371884146790189 131757286297639456555046321)
              ·
                refine ⟨98817964723229592416284741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131757286297639456555046321 98817964723229592416284741)
                ·
                  refine ⟨18528368385605548578053389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98817964723229592416284741 18528368385605548578053389)
                  ·
                    refine ⟨6948138144602080716770021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18528368385605548578053389 6948138144602080716770021)
                    ·
                      refine ⟨1302775902112890134394379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6948138144602080716770021 1302775902112890134394379)
                      ·
                        rfl

theorem cell23_2537147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 4].length) (baseStart_2537147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537147 prefixEnd_2537147 := by exact prefixLift 2537147
  have htrace : WordTrace (prefixWord ++ tailWord_2537147) baseStart_2537147 baseEnd_2537147 := by
    simpa [prefixWord, tailWord_2537147, baseEnd_2537147] using wordTrace_append hprefix tailTrace_2537147
  have hstable : (prefixWord ++ tailWord_2537147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537147).length < 2 ^ (prefixWord ++ tailWord_2537147).sum := by decide
  have hdescent : baseEnd_2537147 < baseStart_2537147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537157 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 4, 6]
def baseStart_2537157 : Nat := 118140960795 + 2537157 * 2 ^ 59
def prefixEnd_2537157 : Nat := 4983230072969 + 3 ^ 40 * 2537157 * 2
def baseEnd_2537157 : Nat := 434260345639811698423111

theorem tailTrace_2537157 : CollatzResearch.WordTrace tailWord_2537157 prefixEnd_2537157 434260345639811698423111 := by
  unfold tailWord_2537157
  simp only [CollatzResearch.WordTrace]
  refine ⟨92537718069320975762985725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61691812046213983841990483 92537718069320975762985725)
  ·
    refine ⟨34701644275995365911119647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92537718069320975762985725 34701644275995365911119647)
    ·
      refine ⟨52052466413993048866679471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34701644275995365911119647 52052466413993048866679471)
      ·
        refine ⟨78078699620989573300019207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52052466413993048866679471 78078699620989573300019207)
        ·
          refine ⟨117118049431484359950028811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78078699620989573300019207 117118049431484359950028811)
          ·
            refine ⟨175677074147226539925043217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117118049431484359950028811 175677074147226539925043217)
            ·
              refine ⟨131757805610419904943782413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175677074147226539925043217 131757805610419904943782413)
              ·
                refine ⟨49409177103907464353918405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131757805610419904943782413 49409177103907464353918405)
                ·
                  refine ⟨9264220706982649566359701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49409177103907464353918405 9264220706982649566359701)
                  ·
                    refine ⟨434260345639811698423111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9264220706982649566359701 434260345639811698423111)
                    ·
                      rfl

theorem cell23_2537157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_2537157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537157 prefixEnd_2537157 := by exact prefixLift 2537157
  have htrace : WordTrace (prefixWord ++ tailWord_2537157) baseStart_2537157 baseEnd_2537157 := by
    simpa [prefixWord, tailWord_2537157, baseEnd_2537157] using wordTrace_append hprefix tailTrace_2537157
  have hstable : (prefixWord ++ tailWord_2537157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537157).length < 2 ^ (prefixWord ++ tailWord_2537157).sum := by decide
  have hdescent : baseEnd_2537157 < baseStart_2537157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537167 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 5]
def baseStart_2537167 : Nat := 118140960795 + 2537167 * 2 ^ 59
def prefixEnd_2537167 : Nat := 4983230072969 + 3 ^ 40 * 2537167 * 2
def baseEnd_2537167 : Nat := 1302786171725980056144287

theorem tailTrace_2537167 : CollatzResearch.WordTrace tailWord_2537167 prefixEnd_2537167 1302786171725980056144287 := by
  unfold tailWord_2537167
  simp only [CollatzResearch.WordTrace]
  refine ⟨92538082799284747470849755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61692055199523164980566503 92538082799284747470849755)
  ·
    refine ⟨138807124198927121206274633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92538082799284747470849755 138807124198927121206274633)
    ·
      refine ⟨104105343149195340904705975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138807124198927121206274633 104105343149195340904705975)
      ·
        refine ⟨156158014723793011357058963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104105343149195340904705975 156158014723793011357058963)
        ·
          refine ⟨234237022085689517035588445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156158014723793011357058963 234237022085689517035588445)
          ·
            refine ⟨87838883282133568888345667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234237022085689517035588445 87838883282133568888345667)
            ·
              refine ⟨131758324923200353332518501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87838883282133568888345667 131758324923200353332518501)
              ·
                refine ⟨24704685923100066249847219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131758324923200353332518501 24704685923100066249847219)
                ·
                  refine ⟨37057028884650099374770829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24704685923100066249847219 37057028884650099374770829)
                  ·
                    refine ⟨13896385831743787265539061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37057028884650099374770829 13896385831743787265539061)
                    ·
                      refine ⟨1302786171725980056144287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13896385831743787265539061 1302786171725980056144287)
                      ·
                        rfl

theorem cell23_2537167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_2537167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537167 prefixEnd_2537167 := by exact prefixLift 2537167
  have htrace : WordTrace (prefixWord ++ tailWord_2537167) baseStart_2537167 baseEnd_2537167 := by
    simpa [prefixWord, tailWord_2537167, baseEnd_2537167] using wordTrace_append hprefix tailTrace_2537167
  have hstable : (prefixWord ++ tailWord_2537167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537167).length < 2 ^ (prefixWord ++ tailWord_2537167).sum := by decide
  have hdescent : baseEnd_2537167 < baseStart_2537167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537198 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_2537198 : Nat := 118140960795 + 2537198 * 2 ^ 59
def prefixEnd_2537198 : Nat := 4983230072969 + 3 ^ 40 * 2537198 * 2
def baseEnd_2537198 : Nat := 1302802089626269434856645

theorem tailTrace_2537198 : CollatzResearch.WordTrace tailWord_2537198 prefixEnd_2537198 1302802089626269434856645 := by
  unfold tailWord_2537198
  simp only [CollatzResearch.WordTrace]
  refine ⟨11567401682771554970653531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61692808974781626510152165 11567401682771554970653531)
  ·
    refine ⟨17351102524157332455980297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11567401682771554970653531 17351102524157332455980297)
    ·
      refine ⟨13013326893117999341985223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17351102524157332455980297 13013326893117999341985223)
      ·
        refine ⟨19519990339676999012977835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13013326893117999341985223 19519990339676999012977835)
        ·
          refine ⟨29279985509515498519466753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19519990339676999012977835 29279985509515498519466753)
          ·
            refine ⟨21959989132136623889600065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29279985509515498519466753 21959989132136623889600065)
            ·
              refine ⟨16469991849102467917200049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21959989132136623889600065 16469991849102467917200049)
              ·
                refine ⟨12352493886826850937900037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16469991849102467917200049 12352493886826850937900037)
                ·
                  refine ⟨2316092603780034550856257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12352493886826850937900037 2316092603780034550856257)
                  ·
                    refine ⟨1737069452835025913142193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2316092603780034550856257 1737069452835025913142193)
                    ·
                      refine ⟨1302802089626269434856645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737069452835025913142193 1302802089626269434856645)
                      ·
                        rfl

theorem cell23_2537198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_2537198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537198 prefixEnd_2537198 := by exact prefixLift 2537198
  have htrace : WordTrace (prefixWord ++ tailWord_2537198) baseStart_2537198 baseEnd_2537198 := by
    simpa [prefixWord, tailWord_2537198, baseEnd_2537198] using wordTrace_append hprefix tailTrace_2537198
  have hstable : (prefixWord ++ tailWord_2537198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537198).length < 2 ^ (prefixWord ++ tailWord_2537198).sum := by decide
  have hdescent : baseEnd_2537198 < baseStart_2537198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537268 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_2537268 : Nat := 118140960795 + 2537268 * 2 ^ 59
def prefixEnd_2537268 : Nat := 4983230072969 + 3 ^ 40 * 2537268 * 2
def baseEnd_2537268 : Nat := 434279344424028053660441

theorem tailTrace_2537268 : CollatzResearch.WordTrace tailWord_2537268 prefixEnd_2537268 434279344424028053660441 := by
  unfold tailWord_2537268
  simp only [CollatzResearch.WordTrace]
  refine ⟨46270883285959420860138229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61694511047945894480184305 46270883285959420860138229)
  ·
    refine ⟨4337895308058695705637959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46270883285959420860138229 4337895308058695705637959)
    ·
      refine ⟨6506842962088043558456939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4337895308058695705637959 6506842962088043558456939)
      ·
        refine ⟨9760264443132065337685409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6506842962088043558456939 9760264443132065337685409)
        ·
          refine ⟨7320198332349049003264057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9760264443132065337685409 7320198332349049003264057)
          ·
            refine ⟨5490148749261786752448043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7320198332349049003264057 5490148749261786752448043)
            ·
              refine ⟨8235223123892680128672065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5490148749261786752448043 8235223123892680128672065)
              ·
                refine ⟨6176417342919510096504049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8235223123892680128672065 6176417342919510096504049)
                ·
                  refine ⟨4632313007189632572378037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6176417342919510096504049 4632313007189632572378037)
                  ·
                    refine ⟨434279344424028053660441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4632313007189632572378037 434279344424028053660441)
                    ·
                      rfl

theorem cell23_2537268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_2537268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537268 prefixEnd_2537268 := by exact prefixLift 2537268
  have htrace : WordTrace (prefixWord ++ tailWord_2537268) baseStart_2537268 baseEnd_2537268 := by
    simpa [prefixWord, tailWord_2537268, baseEnd_2537268] using wordTrace_append hprefix tailTrace_2537268
  have hstable : (prefixWord ++ tailWord_2537268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537268).length < 2 ^ (prefixWord ++ tailWord_2537268).sum := by decide
  have hdescent : baseEnd_2537268 < baseStart_2537268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537271 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 2, 4, 2]
def baseStart_2537271 : Nat := 118140960795 + 2537271 * 2 ^ 59
def prefixEnd_2537271 : Nat := 4983230072969 + 3 ^ 40 * 2537271 * 2
def baseEnd_2537271 : Nat := 1302839573714047649243809

theorem tailTrace_2537271 : CollatzResearch.WordTrace tailWord_2537271 prefixEnd_2537271 1302839573714047649243809 := by
  unfold tailWord_2537271
  simp only [CollatzResearch.WordTrace]
  refine ⟨92541875990907973232635667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61694583993938648821757111 92541875990907973232635667)
  ·
    refine ⟨138812813986361959848953501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92541875990907973232635667 138812813986361959848953501)
    ·
      refine ⟨52054805244885734943357563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138812813986361959848953501 52054805244885734943357563)
      ·
        refine ⟨78082207867328602415036345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52054805244885734943357563 78082207867328602415036345)
        ·
          refine ⟨58561655900496451811277259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78082207867328602415036345 58561655900496451811277259)
          ·
            refine ⟨87842483850744677716915889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58561655900496451811277259 87842483850744677716915889)
            ·
              refine ⟨65881862888058508287686917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87842483850744677716915889 65881862888058508287686917)
              ·
                refine ⟨12352849291510970303941297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65881862888058508287686917 12352849291510970303941297)
                ·
                  refine ⟨9264636968633227727955973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12352849291510970303941297 9264636968633227727955973)
                  ·
                    refine ⟨1737119431618730198991745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9264636968633227727955973 1737119431618730198991745)
                    ·
                      refine ⟨1302839573714047649243809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737119431618730198991745 1302839573714047649243809)
                      ·
                        rfl

theorem cell23_2537271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 4, 2].length) (baseStart_2537271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537271 prefixEnd_2537271 := by exact prefixLift 2537271
  have htrace : WordTrace (prefixWord ++ tailWord_2537271) baseStart_2537271 baseEnd_2537271 := by
    simpa [prefixWord, tailWord_2537271, baseEnd_2537271] using wordTrace_append hprefix tailTrace_2537271
  have hstable : (prefixWord ++ tailWord_2537271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537271).length < 2 ^ (prefixWord ++ tailWord_2537271).sum := by decide
  have hdescent : baseEnd_2537271 < baseStart_2537271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537331 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 3, 5, 2]
def baseStart_2537331 : Nat := 118140960795 + 2537331 * 2 ^ 59
def prefixEnd_2537331 : Nat := 4983230072969 + 3 ^ 40 * 2537331 * 2
def baseEnd_2537331 : Nat := 1302870382553317414493533

theorem tailTrace_2537331 : CollatzResearch.WordTrace tailWord_2537331 prefixEnd_2537331 1302870382553317414493533 := by
  unfold tailWord_2537331
  simp only [CollatzResearch.WordTrace]
  refine ⟨92544064370690603479819847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61696042913793735653213231 92544064370690603479819847)
  ·
    refine ⟨138816096556035905219729771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92544064370690603479819847 138816096556035905219729771)
    ·
      refine ⟨208224144834053857829594657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138816096556035905219729771 208224144834053857829594657)
      ·
        refine ⟨156168108625540393372195993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208224144834053857829594657 156168108625540393372195993)
        ·
          refine ⟨117126081469155295029146995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156168108625540393372195993 117126081469155295029146995)
          ·
            refine ⟨175689122203732942543720493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117126081469155295029146995 175689122203732942543720493)
            ·
              refine ⟨65883420826399853453895185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175689122203732942543720493 65883420826399853453895185)
              ·
                refine ⟨49412565619799890090421389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65883420826399853453895185 49412565619799890090421389)
                ·
                  refine ⟨18529712107424958783908021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49412565619799890090421389 18529712107424958783908021)
                  ·
                    refine ⟨1737160510071089885991377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18529712107424958783908021 1737160510071089885991377)
                    ·
                      refine ⟨1302870382553317414493533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737160510071089885991377 1302870382553317414493533)
                      ·
                        rfl

theorem cell23_2537331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 5, 2].length) (baseStart_2537331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537331 prefixEnd_2537331 := by exact prefixLift 2537331
  have htrace : WordTrace (prefixWord ++ tailWord_2537331) baseStart_2537331 baseEnd_2537331 := by
    simpa [prefixWord, tailWord_2537331, baseEnd_2537331] using wordTrace_append hprefix tailTrace_2537331
  have hstable : (prefixWord ++ tailWord_2537331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537331).length < 2 ^ (prefixWord ++ tailWord_2537331).sum := by decide
  have hdescent : baseEnd_2537331 < baseStart_2537331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537348 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_2537348 : Nat := 118140960795 + 2537348 * 2 ^ 59
def prefixEnd_2537348 : Nat := 4983230072969 + 3 ^ 40 * 2537348 * 2
def baseEnd_2537348 : Nat := 1302879111724443847980955

theorem tailTrace_2537348 : CollatzResearch.WordTrace tailWord_2537348 prefixEnd_2537348 1302879111724443847980955 := by
  unfold tailWord_2537348
  simp only [CollatzResearch.WordTrace]
  refine ⟨46272342205814507691594349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61696456274419343588792465 46272342205814507691594349)
  ·
    refine ⟨17352128327180440384347881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46272342205814507691594349 17352128327180440384347881)
    ·
      refine ⟨13014096245385330288260911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17352128327180440384347881 13014096245385330288260911)
      ·
        refine ⟨19521144368077995432391367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13014096245385330288260911 19521144368077995432391367)
        ·
          refine ⟨29281716552116993148587051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19521144368077995432391367 29281716552116993148587051)
          ·
            refine ⟨43922574828175489722880577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29281716552116993148587051 43922574828175489722880577)
            ·
              refine ⟨32941931121131617292160433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43922574828175489722880577 32941931121131617292160433)
              ·
                refine ⟨24706448340848712969120325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32941931121131617292160433 24706448340848712969120325)
                ·
                  refine ⟨4632459063909133681710061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24706448340848712969120325 4632459063909133681710061)
                  ·
                    refine ⟨1737172148965925130641273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4632459063909133681710061 1737172148965925130641273)
                    ·
                      refine ⟨1302879111724443847980955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737172148965925130641273 1302879111724443847980955)
                      ·
                        rfl

theorem cell23_2537348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_2537348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537348 prefixEnd_2537348 := by exact prefixLift 2537348
  have htrace : WordTrace (prefixWord ++ tailWord_2537348) baseStart_2537348 baseEnd_2537348 := by
    simpa [prefixWord, tailWord_2537348, baseEnd_2537348] using wordTrace_append hprefix tailTrace_2537348
  have hstable : (prefixWord ++ tailWord_2537348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537348).length < 2 ^ (prefixWord ++ tailWord_2537348).sum := by decide
  have hdescent : baseEnd_2537348 < baseStart_2537348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537361 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 4]
def baseStart_2537361 : Nat := 118140960795 + 2537361 * 2 ^ 59
def prefixEnd_2537361 : Nat := 4983230072969 + 3 ^ 40 * 2537361 * 2
def baseEnd_2537361 : Nat := 1302885786972952297118395

theorem tailTrace_2537361 : CollatzResearch.WordTrace tailWord_2537361 prefixEnd_2537361 1302885786972952297118395 := by
  unfold tailWord_2537361
  simp only [CollatzResearch.WordTrace]
  refine ⟨92545158560581918603411937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61696772373721279068941291 92545158560581918603411937)
  ·
    refine ⟨69408868920436438952558953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92545158560581918603411937 69408868920436438952558953)
    ·
      refine ⟨52056651690327329214419215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69408868920436438952558953 52056651690327329214419215)
      ·
        refine ⟨78084977535490993821628823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52056651690327329214419215 78084977535490993821628823)
        ·
          refine ⟨117127466303236490732443235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78084977535490993821628823 117127466303236490732443235)
          ·
            refine ⟨175691199454854736098664853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117127466303236490732443235 175691199454854736098664853)
            ·
              refine ⟨8235524974446315754624915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 175691199454854736098664853 8235524974446315754624915)
              ·
                refine ⟨12353287461669473631937373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8235524974446315754624915 12353287461669473631937373)
                ·
                  refine ⟨4632482798126052611976515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12353287461669473631937373 4632482798126052611976515)
                  ·
                    refine ⟨6948724197189078917964773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4632482798126052611976515 6948724197189078917964773)
                    ·
                      refine ⟨1302885786972952297118395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6948724197189078917964773 1302885786972952297118395)
                      ·
                        rfl

theorem cell23_2537361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_2537361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537361 prefixEnd_2537361 := by exact prefixLift 2537361
  have htrace : WordTrace (prefixWord ++ tailWord_2537361) baseStart_2537361 baseEnd_2537361 := by
    simpa [prefixWord, tailWord_2537361, baseEnd_2537361] using wordTrace_append hprefix tailTrace_2537361
  have hstable : (prefixWord ++ tailWord_2537361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537361).length < 2 ^ (prefixWord ++ tailWord_2537361).sum := by decide
  have hdescent : baseEnd_2537361 < baseStart_2537361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537366 : List Nat := [5, 3, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_2537366 : Nat := 118140960795 + 2537366 * 2 ^ 59
def prefixEnd_2537366 : Nat := 4983230072969 + 3 ^ 40 * 2537366 * 2
def baseEnd_2537366 : Nat := 434296118125408259185291

theorem tailTrace_2537366 : CollatzResearch.WordTrace tailWord_2537366 prefixEnd_2537366 434296118125408259185291 := by
  unfold tailWord_2537366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784083807847737778583997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61696893950375869638229301 5784083807847737778583997)
  ·
    refine ⟨2169031427942901666968999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5784083807847737778583997 2169031427942901666968999)
    ·
      refine ⟨3253547141914352500453499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2169031427942901666968999 3253547141914352500453499)
      ·
        refine ⟨4880320712871528750680249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3253547141914352500453499 4880320712871528750680249)
        ·
          refine ⟨3660240534653646563010187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4880320712871528750680249 3660240534653646563010187)
          ·
            refine ⟨5490360801980469844515281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3660240534653646563010187 5490360801980469844515281)
            ·
              refine ⟨4117770601485352383386461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5490360801980469844515281 4117770601485352383386461)
              ·
                refine ⟨1544163975557007143769923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4117770601485352383386461 1544163975557007143769923)
                ·
                  refine ⟨2316245963335510715654885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544163975557007143769923 2316245963335510715654885)
                  ·
                    refine ⟨434296118125408259185291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2316245963335510715654885 434296118125408259185291)
                    ·
                      rfl

theorem cell23_2537366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_2537366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537366 prefixEnd_2537366 := by exact prefixLift 2537366
  have htrace : WordTrace (prefixWord ++ tailWord_2537366) baseStart_2537366 baseEnd_2537366 := by
    simpa [prefixWord, tailWord_2537366, baseEnd_2537366] using wordTrace_append hprefix tailTrace_2537366
  have hstable : (prefixWord ++ tailWord_2537366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537366).length < 2 ^ (prefixWord ++ tailWord_2537366).sum := by decide
  have hdescent : baseEnd_2537366 < baseStart_2537366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537372 : List Nat := [2, 2, 3, 3, 1, 1, 1, 5, 1, 1, 3]
def baseStart_2537372 : Nat := 118140960795 + 2537372 * 2 ^ 59
def prefixEnd_2537372 : Nat := 4983230072969 + 3 ^ 40 * 2537372 * 2
def baseEnd_2537372 : Nat := 1302891435260151754080845

theorem tailTrace_2537372 : CollatzResearch.WordTrace tailWord_2537372 prefixEnd_2537372 1302891435260151754080845 := by
  unfold tailWord_2537372
  simp only [CollatzResearch.WordTrace]
  refine ⟨46272779881771033741031185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61697039842361378321374913 46272779881771033741031185)
  ·
    refine ⟨34704584911328275305773389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46272779881771033741031185 34704584911328275305773389)
    ·
      refine ⟨13014219341748103239665021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34704584911328275305773389 13014219341748103239665021)
      ·
        refine ⟨4880332253155538714874383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13014219341748103239665021 4880332253155538714874383)
        ·
          refine ⟨7320498379733308072311575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4880332253155538714874383 7320498379733308072311575)
          ·
            refine ⟨10980747569599962108467363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7320498379733308072311575 10980747569599962108467363)
            ·
              refine ⟨16471121354399943162701045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10980747569599962108467363 16471121354399943162701045)
              ·
                refine ⟨1544167626974994671503223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16471121354399943162701045 1544167626974994671503223)
                ·
                  refine ⟨2316251440462492007254835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544167626974994671503223 2316251440462492007254835)
                  ·
                    refine ⟨3474377160693738010882253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2316251440462492007254835 3474377160693738010882253)
                    ·
                      refine ⟨1302891435260151754080845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3474377160693738010882253 1302891435260151754080845)
                      ·
                        rfl

theorem cell23_2537372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_2537372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537372 prefixEnd_2537372 := by exact prefixLift 2537372
  have htrace : WordTrace (prefixWord ++ tailWord_2537372) baseStart_2537372 baseEnd_2537372 := by
    simpa [prefixWord, tailWord_2537372, baseEnd_2537372] using wordTrace_append hprefix tailTrace_2537372
  have hstable : (prefixWord ++ tailWord_2537372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537372).length < 2 ^ (prefixWord ++ tailWord_2537372).sum := by decide
  have hdescent : baseEnd_2537372 < baseStart_2537372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537395 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 3, 2, 2]
def baseStart_2537395 : Nat := 118140960795 + 2537395 * 2 ^ 59
def prefixEnd_2537395 : Nat := 4983230072969 + 3 ^ 40 * 2537395 * 2
def baseEnd_2537395 : Nat := 1302903245315205164093239

theorem tailTrace_2537395 : CollatzResearch.WordTrace tailWord_2537395 prefixEnd_2537395 1302903245315205164093239 := by
  unfold tailWord_2537395
  simp only [CollatzResearch.WordTrace]
  refine ⟨92546398642458742410149639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61697599094972494940099759 92546398642458742410149639)
  ·
    refine ⟨138819597963688113615224459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92546398642458742410149639 138819597963688113615224459)
    ·
      refine ⟨208229396945532170422836689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138819597963688113615224459 208229396945532170422836689)
      ·
        refine ⟨156172047709149127817127517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208229396945532170422836689 156172047709149127817127517)
        ·
          refine ⟨58564517890930922931422819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156172047709149127817127517 58564517890930922931422819)
          ·
            refine ⟨87846776836396384397134229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58564517890930922931422819 87846776836396384397134229)
            ·
              refine ⟨4117817664206080518615667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87846776836396384397134229 4117817664206080518615667)
              ·
                refine ⟨6176726496309120777923501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4117817664206080518615667 6176726496309120777923501)
                ·
                  refine ⟨2316272436115920291721313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6176726496309120777923501 2316272436115920291721313)
                  ·
                    refine ⟨1737204327086940218790985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2316272436115920291721313 1737204327086940218790985)
                    ·
                      refine ⟨1302903245315205164093239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737204327086940218790985 1302903245315205164093239)
                      ·
                        rfl

theorem cell23_2537395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 2, 2].length) (baseStart_2537395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537395 prefixEnd_2537395 := by exact prefixLift 2537395
  have htrace : WordTrace (prefixWord ++ tailWord_2537395) baseStart_2537395 baseEnd_2537395 := by
    simpa [prefixWord, tailWord_2537395, baseEnd_2537395] using wordTrace_append hprefix tailTrace_2537395
  have hstable : (prefixWord ++ tailWord_2537395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537395).length < 2 ^ (prefixWord ++ tailWord_2537395).sum := by decide
  have hdescent : baseEnd_2537395 < baseStart_2537395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537428 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_2537428 : Nat := 118140960795 + 2537428 * 2 ^ 59
def prefixEnd_2537428 : Nat := 4983230072969 + 3 ^ 40 * 2537428 * 2
def baseEnd_2537428 : Nat := 1302920190176803534980587

theorem tailTrace_2537428 : CollatzResearch.WordTrace tailWord_2537428 prefixEnd_2537428 1302920190176803534980587 := by
  unfold tailWord_2537428
  simp only [CollatzResearch.WordTrace]
  refine ⟨46273801125669594523050469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61698401500892792697400625 46273801125669594523050469)
  ·
    refine ⟨8676337711063048973071963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46273801125669594523050469 8676337711063048973071963)
    ·
      refine ⟨13014506566594573459607945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8676337711063048973071963 13014506566594573459607945)
      ·
        refine ⟨9760879924945930094705959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13014506566594573459607945 9760879924945930094705959)
        ·
          refine ⟨14641319887418895142058939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9760879924945930094705959 14641319887418895142058939)
          ·
            refine ⟨21961979831128342713088409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14641319887418895142058939 21961979831128342713088409)
            ·
              refine ⟨16471484873346257034816307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21961979831128342713088409 16471484873346257034816307)
              ·
                refine ⟨24707227310019385552224461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16471484873346257034816307 24707227310019385552224461)
                ·
                  refine ⟨9265210241257269582084173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24707227310019385552224461 9265210241257269582084173)
                  ·
                    refine ⟨3474453840471476093281565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9265210241257269582084173 3474453840471476093281565)
                    ·
                      refine ⟨1302920190176803534980587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3474453840471476093281565 1302920190176803534980587)
                      ·
                        rfl

theorem cell23_2537428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_2537428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537428 prefixEnd_2537428 := by exact prefixLift 2537428
  have htrace : WordTrace (prefixWord ++ tailWord_2537428) baseStart_2537428 baseEnd_2537428 := by
    simpa [prefixWord, tailWord_2537428, baseEnd_2537428] using wordTrace_append hprefix tailTrace_2537428
  have hstable : (prefixWord ++ tailWord_2537428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537428).length < 2 ^ (prefixWord ++ tailWord_2537428).sum := by decide
  have hdescent : baseEnd_2537428 < baseStart_2537428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537429 : List Nat := [1, 3, 2, 3, 2, 1, 3, 3, 1, 2, 2]
def baseStart_2537429 : Nat := 118140960795 + 2537429 * 2 ^ 59
def prefixEnd_2537429 : Nat := 4983230072969 + 3 ^ 40 * 2537429 * 2
def baseEnd_2537429 : Nat := 1302920703657458031068083

theorem tailTrace_2537429 : CollatzResearch.WordTrace tailWord_2537429 prefixEnd_2537429 1302920703657458031068083 := by
  unfold tailWord_2537429
  simp only [CollatzResearch.WordTrace]
  refine ⟨92547638724335566216887341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61698425816223710811258227 92547638724335566216887341)
  ·
    refine ⟨34705364521625837331332753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92547638724335566216887341 34705364521625837331332753)
    ·
      refine ⟨26029023391219377998499565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34705364521625837331332753 26029023391219377998499565)
      ·
        refine ⟨9760883771707266749437337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26029023391219377998499565 9760883771707266749437337)
        ·
          refine ⟨7320662828780450062078003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9760883771707266749437337 7320662828780450062078003)
          ·
            refine ⟨10980994243170675093117005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7320662828780450062078003 10980994243170675093117005)
            ·
              refine ⟨4117872841189003159918877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10980994243170675093117005 4117872841189003159918877)
              ·
                refine ⟨1544202315445876184969579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4117872841189003159918877 1544202315445876184969579)
                ·
                  refine ⟨2316303473168814277454369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544202315445876184969579 2316303473168814277454369)
                  ·
                    refine ⟨1737227604876610708090777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2316303473168814277454369 1737227604876610708090777)
                    ·
                      refine ⟨1302920703657458031068083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737227604876610708090777 1302920703657458031068083)
                      ·
                        rfl

theorem cell23_2537429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_2537429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537429 prefixEnd_2537429 := by exact prefixLift 2537429
  have htrace : WordTrace (prefixWord ++ tailWord_2537429) baseStart_2537429 baseEnd_2537429 := by
    simpa [prefixWord, tailWord_2537429, baseEnd_2537429] using wordTrace_append hprefix tailTrace_2537429
  have hstable : (prefixWord ++ tailWord_2537429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537429).length < 2 ^ (prefixWord ++ tailWord_2537429).sum := by decide
  have hdescent : baseEnd_2537429 < baseStart_2537429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537481 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 6, 2, 4]
def baseStart_2537481 : Nat := 118140960795 + 2537481 * 2 ^ 59
def prefixEnd_2537481 : Nat := 4983230072969 + 3 ^ 40 * 2537481 * 2
def baseEnd_2537481 : Nat := 1302947404651491827617843

theorem tailTrace_2537481 : CollatzResearch.WordTrace tailWord_2537481 prefixEnd_2537481 1302947404651491827617843 := by
  unfold tailWord_2537481
  simp only [CollatzResearch.WordTrace]
  refine ⟨92549535320147179097780297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61699690213431452731853531 92549535320147179097780297)
  ·
    refine ⟨69412151490110384323335223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92549535320147179097780297 69412151490110384323335223)
    ·
      refine ⟨104118227235165576485002835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69412151490110384323335223 104118227235165576485002835)
      ·
        refine ⟨156177340852748364727504253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104118227235165576485002835 156177340852748364727504253)
        ·
          refine ⟨58566502819780636772814095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156177340852748364727504253 58566502819780636772814095)
          ·
            refine ⟨87849754229670955159221143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58566502819780636772814095 87849754229670955159221143)
            ·
              refine ⟨131774631344506432738831715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87849754229670955159221143 131774631344506432738831715)
              ·
                refine ⟨197661947016759649108247573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131774631344506432738831715 197661947016759649108247573)
                ·
                  refine ⟨9265403766410608551949105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 197661947016759649108247573 9265403766410608551949105)
                  ·
                    refine ⟨6949052824807956413961829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9265403766410608551949105 6949052824807956413961829)
                    ·
                      refine ⟨1302947404651491827617843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6949052824807956413961829 1302947404651491827617843)
                      ·
                        rfl

theorem cell23_2537481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_2537481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537481 prefixEnd_2537481 := by exact prefixLift 2537481
  have htrace : WordTrace (prefixWord ++ tailWord_2537481) baseStart_2537481 baseEnd_2537481 := by
    simpa [prefixWord, tailWord_2537481, baseEnd_2537481] using wordTrace_append hprefix tailTrace_2537481
  have hstable : (prefixWord ++ tailWord_2537481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537481).length < 2 ^ (prefixWord ++ tailWord_2537481).sum := by decide
  have hdescent : baseEnd_2537481 < baseStart_2537481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537575 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_2537575 : Nat := 118140960795 + 2537575 * 2 ^ 59
def prefixEnd_2537575 : Nat := 4983230072969 + 3 ^ 40 * 2537575 * 2
def baseEnd_2537575 : Nat := 1302995671833014459842411

theorem tailTrace_2537575 : CollatzResearch.WordTrace tailWord_2537575 prefixEnd_2537575 1302995671833014459842411 := by
  unfold tailWord_2537575
  simp only [CollatzResearch.WordTrace]
  refine ⟨92552963781806633151702179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61701975854537755434468119 92552963781806633151702179)
  ·
    refine ⟨138829445672709949727553269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92552963781806633151702179 138829445672709949727553269)
    ·
      refine ⟨13015260531816557786958119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138829445672709949727553269 13015260531816557786958119)
      ·
        refine ⟨19522890797724836680437179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13015260531816557786958119 19522890797724836680437179)
        ·
          refine ⟨29284336196587255020655769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19522890797724836680437179 29284336196587255020655769)
          ·
            refine ⟨21963252147440441265491827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29284336196587255020655769 21963252147440441265491827)
            ·
              refine ⟨32944878221160661898237741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21963252147440441265491827 32944878221160661898237741)
              ·
                refine ⟨12354329332935248211839153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32944878221160661898237741 12354329332935248211839153)
                ·
                  refine ⟨9265746999701436158879365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12354329332935248211839153 9265746999701436158879365)
                  ·
                    refine ⟨1737327562444019279789881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9265746999701436158879365 1737327562444019279789881)
                    ·
                      refine ⟨1302995671833014459842411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737327562444019279789881 1302995671833014459842411)
                      ·
                        rfl

theorem cell23_2537575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_2537575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537575 prefixEnd_2537575 := by exact prefixLift 2537575
  have htrace : WordTrace (prefixWord ++ tailWord_2537575) baseStart_2537575 baseEnd_2537575 := by
    simpa [prefixWord, tailWord_2537575, baseEnd_2537575] using wordTrace_append hprefix tailTrace_2537575
  have hstable : (prefixWord ++ tailWord_2537575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537575).length < 2 ^ (prefixWord ++ tailWord_2537575).sum := by decide
  have hdescent : baseEnd_2537575 < baseStart_2537575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537632 : List Nat := [2, 1, 1, 4, 2, 4, 2, 1, 6]
def baseStart_2537632 : Nat := 118140960795 + 2537632 * 2 ^ 59
def prefixEnd_2537632 : Nat := 4983230072969 + 3 ^ 40 * 2537632 * 2
def baseEnd_2537632 : Nat := 144780548914480081869961

theorem tailTrace_2537632 : CollatzResearch.WordTrace tailWord_2537632 prefixEnd_2537632 144780548914480081869961 := by
  unfold tailWord_2537632
  simp only [CollatzResearch.WordTrace]
  refine ⟨46277521371300065943263575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61703361828400087924351433 46277521371300065943263575)
  ·
    refine ⟨69416282056950098914895363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46277521371300065943263575 69416282056950098914895363)
    ·
      refine ⟨104124423085425148372343045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69416282056950098914895363 104124423085425148372343045)
      ·
        refine ⟨19523329328517215319814321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104124423085425148372343045 19523329328517215319814321)
        ·
          refine ⟨14642496996387911489860741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19523329328517215319814321 14642496996387911489860741)
          ·
            refine ⟨2745468186822733404348889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14642496996387911489860741 2745468186822733404348889)
            ·
              refine ⟨2059101140117050053261667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2745468186822733404348889 2059101140117050053261667)
              ·
                refine ⟨3088651710175575079892501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059101140117050053261667 3088651710175575079892501)
                ·
                  refine ⟨144780548914480081869961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3088651710175575079892501 144780548914480081869961)
                  ·
                    rfl

theorem cell23_2537632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 6].length) (baseStart_2537632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537632 prefixEnd_2537632 := by exact prefixLift 2537632
  have htrace : WordTrace (prefixWord ++ tailWord_2537632) baseStart_2537632 baseEnd_2537632 := by
    simpa [prefixWord, tailWord_2537632, baseEnd_2537632] using wordTrace_append hprefix tailTrace_2537632
  have hstable : (prefixWord ++ tailWord_2537632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537632).length < 2 ^ (prefixWord ++ tailWord_2537632).sum := by decide
  have hdescent : baseEnd_2537632 < baseStart_2537632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537646 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2537646 : Nat := 118140960795 + 2537646 * 2 ^ 59
def prefixEnd_2537646 : Nat := 4983230072969 + 3 ^ 40 * 2537646 * 2
def baseEnd_2537646 : Nat := 1303032128959483682054585

theorem tailTrace_2537646 : CollatzResearch.WordTrace tailWord_2537646 prefixEnd_2537646 1303032128959483682054585 := by
  unfold tailWord_2537646
  simp only [CollatzResearch.WordTrace]
  refine ⟨11569444170568676534692099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61703702243032941518357861 11569444170568676534692099)
  ·
    refine ⟨17354166255853014802038149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11569444170568676534692099 17354166255853014802038149)
    ·
      refine ⟨3253906172972440275382153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17354166255853014802038149 3253906172972440275382153)
      ·
        refine ⟨2440429629729330206536615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3253906172972440275382153 2440429629729330206536615)
        ·
          refine ⟨3660644444593995309804923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2440429629729330206536615 3660644444593995309804923)
          ·
            refine ⟨5490966666890992964707385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3660644444593995309804923 5490966666890992964707385)
            ·
              refine ⟨4118225000168244723530539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5490966666890992964707385 4118225000168244723530539)
              ·
                refine ⟨6177337500252367085295809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4118225000168244723530539 6177337500252367085295809)
                ·
                  refine ⟨4633003125189275313971857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6177337500252367085295809 4633003125189275313971857)
                  ·
                    refine ⟨3474752343891956485478893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4633003125189275313971857 3474752343891956485478893)
                    ·
                      refine ⟨1303032128959483682054585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3474752343891956485478893 1303032128959483682054585)
                      ·
                        rfl

theorem cell23_2537646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2537646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537646 prefixEnd_2537646 := by exact prefixLift 2537646
  have htrace : WordTrace (prefixWord ++ tailWord_2537646) baseStart_2537646 baseEnd_2537646 := by
    simpa [prefixWord, tailWord_2537646, baseEnd_2537646] using wordTrace_append hprefix tailTrace_2537646
  have hstable : (prefixWord ++ tailWord_2537646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537646).length < 2 ^ (prefixWord ++ tailWord_2537646).sum := by decide
  have hdescent : baseEnd_2537646 < baseStart_2537646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537658 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 3, 6]
def baseStart_2537658 : Nat := 118140960795 + 2537658 * 2 ^ 59
def prefixEnd_2537658 : Nat := 4983230072969 + 3 ^ 40 * 2537658 * 2
def baseEnd_2537658 : Nat := 434346096909112545034843

theorem tailTrace_2537658 : CollatzResearch.WordTrace tailWord_2537658 prefixEnd_2537658 434346096909112545034843 := by
  unfold tailWord_2537658
  simp only [CollatzResearch.WordTrace]
  refine ⟨23138997760126484581743407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61703994027003958884649085 23138997760126484581743407)
  ·
    refine ⟨34708496640189726872615111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23138997760126484581743407 34708496640189726872615111)
    ·
      refine ⟨52062744960284590308922667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34708496640189726872615111 52062744960284590308922667)
      ·
        refine ⟨78094117440426885463384001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52062744960284590308922667 78094117440426885463384001)
        ·
          refine ⟨58570588080320164097538001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78094117440426885463384001 58570588080320164097538001)
          ·
            refine ⟨43927941060240123073153501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58570588080320164097538001 43927941060240123073153501)
            ·
              refine ⟨16472977897590046152432563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43927941060240123073153501 16472977897590046152432563)
              ·
                refine ⟨24709466846385069228648845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16472977897590046152432563 24709466846385069228648845)
                ·
                  refine ⟨9266050067394400960743317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24709466846385069228648845 9266050067394400960743317)
                  ·
                    refine ⟨434346096909112545034843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9266050067394400960743317 434346096909112545034843)
                    ·
                      rfl

theorem cell23_2537658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_2537658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537658 prefixEnd_2537658 := by exact prefixLift 2537658
  have htrace : WordTrace (prefixWord ++ tailWord_2537658) baseStart_2537658 baseEnd_2537658 := by
    simpa [prefixWord, tailWord_2537658, baseEnd_2537658] using wordTrace_append hprefix tailTrace_2537658
  have hstable : (prefixWord ++ tailWord_2537658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537658).length < 2 ^ (prefixWord ++ tailWord_2537658).sum := by decide
  have hdescent : baseEnd_2537658 < baseStart_2537658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537715 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 3]
def baseStart_2537715 : Nat := 118140960795 + 2537715 * 2 ^ 59
def prefixEnd_2537715 : Nat := 4983230072969 + 3 ^ 40 * 2537715 * 2
def baseEnd_2537715 : Nat := 1303067559124643912091767

theorem tailTrace_2537715 : CollatzResearch.WordTrace tailWord_2537715 prefixEnd_2537715 1303067559124643912091767 := by
  unfold tailWord_2537715
  simp only [CollatzResearch.WordTrace]
  refine ⟨92558070001299437061798599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61705380000866291374532399 92558070001299437061798599)
  ·
    refine ⟨138837105001949155592697899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92558070001299437061798599 138837105001949155592697899)
    ·
      refine ⟨208255657502923733389046849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138837105001949155592697899 208255657502923733389046849)
      ·
        refine ⟨156191743127192800041785137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208255657502923733389046849 156191743127192800041785137)
        ·
          refine ⟨117143807345394600031338853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156191743127192800041785137 117143807345394600031338853)
          ·
            refine ⟨21964463877261487505876035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117143807345394600031338853 21964463877261487505876035)
            ·
              refine ⟨32946695815892231258814053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21964463877261487505876035 32946695815892231258814053)
              ·
                refine ⟨6177505465479793361027635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32946695815892231258814053 6177505465479793361027635)
                ·
                  refine ⟨9266258198219690041541453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6177505465479793361027635 9266258198219690041541453)
                  ·
                    refine ⟨3474846824332383765578045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9266258198219690041541453 3474846824332383765578045)
                    ·
                      refine ⟨1303067559124643912091767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3474846824332383765578045 1303067559124643912091767)
                      ·
                        rfl

theorem cell23_2537715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 3].length) (baseStart_2537715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537715 prefixEnd_2537715 := by exact prefixLift 2537715
  have htrace : WordTrace (prefixWord ++ tailWord_2537715) baseStart_2537715 baseEnd_2537715 := by
    simpa [prefixWord, tailWord_2537715, baseEnd_2537715] using wordTrace_append hprefix tailTrace_2537715
  have hstable : (prefixWord ++ tailWord_2537715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537715).length < 2 ^ (prefixWord ++ tailWord_2537715).sum := by decide
  have hdescent : baseEnd_2537715 < baseStart_2537715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537759 : List Nat := [1, 1, 2, 4, 3, 1, 1, 4, 1, 3, 2]
def baseStart_2537759 : Nat := 118140960795 + 2537759 * 2 ^ 59
def prefixEnd_2537759 : Nat := 4983230072969 + 3 ^ 40 * 2537759 * 2
def baseEnd_2537759 : Nat := 1303090152273441739941565

theorem tailTrace_2537759 : CollatzResearch.WordTrace tailWord_2537759 prefixEnd_2537759 1303090152273441739941565 := by
  unfold tailWord_2537759
  simp only [CollatzResearch.WordTrace]
  refine ⟨92559674813140032576400331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61706449875426688384266887 92559674813140032576400331)
  ·
    refine ⟨138839512219710048864600497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92559674813140032576400331 138839512219710048864600497)
    ·
      refine ⟨104129634164782536648450373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138839512219710048864600497 104129634164782536648450373)
      ·
        refine ⟨19524306405896725621584445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104129634164782536648450373 19524306405896725621584445)
        ·
          refine ⟨7321614902211272108094167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19524306405896725621584445 7321614902211272108094167)
          ·
            refine ⟨10982422353316908162141251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7321614902211272108094167 10982422353316908162141251)
            ·
              refine ⟨16473633529975362243211877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10982422353316908162141251 16473633529975362243211877)
              ·
                refine ⟨3088806286870380420602227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16473633529975362243211877 3088806286870380420602227)
                ·
                  refine ⟨4633209430305570630903341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3088806286870380420602227 4633209430305570630903341)
                  ·
                    refine ⟨1737453536364588986588753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4633209430305570630903341 1737453536364588986588753)
                    ·
                      refine ⟨1303090152273441739941565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737453536364588986588753 1303090152273441739941565)
                      ·
                        rfl

theorem cell23_2537759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_2537759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537759 prefixEnd_2537759 := by exact prefixLift 2537759
  have htrace : WordTrace (prefixWord ++ tailWord_2537759) baseStart_2537759 baseEnd_2537759 := by
    simpa [prefixWord, tailWord_2537759, baseEnd_2537759] using wordTrace_append hprefix tailTrace_2537759
  have hstable : (prefixWord ++ tailWord_2537759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537759).length < 2 ^ (prefixWord ++ tailWord_2537759).sum := by decide
  have hdescent : baseEnd_2537759 < baseStart_2537759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537772 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 1, 4, 2]
def baseStart_2537772 : Nat := 118140960795 + 2537772 * 2 ^ 59
def prefixEnd_2537772 : Nat := 4983230072969 + 3 ^ 40 * 2537772 * 2
def baseEnd_2537772 : Nat := 1303096827521950189079005

theorem tailTrace_2537772 : CollatzResearch.WordTrace tailWord_2537772 prefixEnd_2537772 1303096827521950189079005 := by
  unfold tailWord_2537772
  simp only [CollatzResearch.WordTrace]
  refine ⟨46280074481046467898311785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61706765974728623864415713 46280074481046467898311785)
  ·
    refine ⟨34710055860784850923733839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46280074481046467898311785 34710055860784850923733839)
    ·
      refine ⟨52065083791177276385600759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34710055860784850923733839 52065083791177276385600759)
      ·
        refine ⟨78097625686765914578401139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52065083791177276385600759 78097625686765914578401139)
        ·
          refine ⟨117146438530148871867601709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78097625686765914578401139 117146438530148871867601709)
          ·
            refine ⟨43929914448805826950350641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117146438530148871867601709 43929914448805826950350641)
            ·
              refine ⟨32947435836604370212762981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43929914448805826950350641 32947435836604370212762981)
              ·
                refine ⟨6177644219363319414893059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32947435836604370212762981 6177644219363319414893059)
                ·
                  refine ⟨9266466329044979122339589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6177644219363319414893059 9266466329044979122339589)
                  ·
                    refine ⟨1737462436695933585438673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9266466329044979122339589 1737462436695933585438673)
                    ·
                      refine ⟨1303096827521950189079005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737462436695933585438673 1303096827521950189079005)
                      ·
                        rfl

theorem cell23_2537772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 4, 2].length) (baseStart_2537772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537772 prefixEnd_2537772 := by exact prefixLift 2537772
  have htrace : WordTrace (prefixWord ++ tailWord_2537772) baseStart_2537772 baseEnd_2537772 := by
    simpa [prefixWord, tailWord_2537772, baseEnd_2537772] using wordTrace_append hprefix tailTrace_2537772
  have hstable : (prefixWord ++ tailWord_2537772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537772).length < 2 ^ (prefixWord ++ tailWord_2537772).sum := by decide
  have hdescent : baseEnd_2537772 < baseStart_2537772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537795 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 7]
def baseStart_2537795 : Nat := 118140960795 + 2537795 * 2 ^ 59
def prefixEnd_2537795 : Nat := 4983230072969 + 3 ^ 40 * 2537795 * 2
def baseEnd_2537795 : Nat := 144789848619667066565711

theorem tailTrace_2537795 : CollatzResearch.WordTrace tailWord_2537795 prefixEnd_2537795 144789848619667066565711 := by
  unfold tailWord_2537795
  simp only [CollatzResearch.WordTrace]
  refine ⟨92560987841009610724710839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61707325227339740483140559 92560987841009610724710839)
  ·
    refine ⟨138841481761514416087066259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92560987841009610724710839 138841481761514416087066259)
    ·
      refine ⟨208262222642271624130599389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138841481761514416087066259 208262222642271624130599389)
      ·
        refine ⟨78098333490851859048974771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208262222642271624130599389 78098333490851859048974771)
        ·
          refine ⟨117147500236277788573462157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78098333490851859048974771 117147500236277788573462157)
          ·
            refine ⟨43930312588604170715048309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117147500236277788573462157 43930312588604170715048309)
            ·
              refine ⟨4118466805181641004535779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43930312588604170715048309 4118466805181641004535779)
              ·
                refine ⟨6177700207772461506803669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4118466805181641004535779 6177700207772461506803669)
                ·
                  refine ⟨144789848619667066565711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6177700207772461506803669 144789848619667066565711)
                  ·
                    rfl

theorem cell23_2537795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 7].length) (baseStart_2537795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537795 prefixEnd_2537795 := by exact prefixLift 2537795
  have htrace : WordTrace (prefixWord ++ tailWord_2537795) baseStart_2537795 baseEnd_2537795 := by
    simpa [prefixWord, tailWord_2537795, baseEnd_2537795] using wordTrace_append hprefix tailTrace_2537795
  have hstable : (prefixWord ++ tailWord_2537795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537795).length < 2 ^ (prefixWord ++ tailWord_2537795).sum := by decide
  have hdescent : baseEnd_2537795 < baseStart_2537795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537842 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_2537842 : Nat := 118140960795 + 2537842 * 2 ^ 59
def prefixEnd_2537842 : Nat := 4983230072969 + 3 ^ 40 * 2537842 * 2
def baseEnd_2537842 : Nat := 434377590389254971734561

theorem tailTrace_2537842 : CollatzResearch.WordTrace tailWord_2537842 prefixEnd_2537842 434377590389254971734561 := by
  unfold tailWord_2537842
  simp only [CollatzResearch.WordTrace]
  refine ⟨23140675517959834437917945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61708468047892891834447853 23140675517959834437917945)
  ·
    refine ⟨17355506638469875828438459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23140675517959834437917945 17355506638469875828438459)
    ·
      refine ⟨26033259957704813742657689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17355506638469875828438459 26033259957704813742657689)
      ·
        refine ⟨19524944968278610306993267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26033259957704813742657689 19524944968278610306993267)
        ·
          refine ⟨29287417452417915460489901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19524944968278610306993267 29287417452417915460489901)
          ·
            refine ⟨10982781544656718297683713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29287417452417915460489901 10982781544656718297683713)
            ·
              refine ⟨8237086158492538723262785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10982781544656718297683713 8237086158492538723262785)
              ·
                refine ⟨6177814618869404042447089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8237086158492538723262785 6177814618869404042447089)
                ·
                  refine ⟨4633360964152053031835317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6177814618869404042447089 4633360964152053031835317)
                  ·
                    refine ⟨434377590389254971734561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4633360964152053031835317 434377590389254971734561)
                    ·
                      rfl

theorem cell23_2537842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_2537842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537842 prefixEnd_2537842 := by exact prefixLift 2537842
  have htrace : WordTrace (prefixWord ++ tailWord_2537842) baseStart_2537842 baseEnd_2537842 := by
    simpa [prefixWord, tailWord_2537842, baseEnd_2537842] using wordTrace_append hprefix tailTrace_2537842
  have hstable : (prefixWord ++ tailWord_2537842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537842).length < 2 ^ (prefixWord ++ tailWord_2537842).sum := by decide
  have hdescent : baseEnd_2537842 < baseStart_2537842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537876 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_2537876 : Nat := 118140960795 + 2537876 * 2 ^ 59
def prefixEnd_2537876 : Nat := 4983230072969 + 3 ^ 40 * 2537876 * 2
def baseEnd_2537876 : Nat := 434383409836672594059509

theorem tailTrace_2537876 : CollatzResearch.WordTrace tailWord_2537876 prefixEnd_2537876 434383409836672594059509 := by
  unfold tailWord_2537876
  simp only [CollatzResearch.WordTrace]
  refine ⟨46281971076858080779204741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61709294769144107705606321 46281971076858080779204741)
  ·
    refine ⟨8677869576910890146100889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46281971076858080779204741 8677869576910890146100889)
    ·
      refine ⟨6508402182683167609575667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8677869576910890146100889 6508402182683167609575667)
      ·
        refine ⟨9762603274024751414363501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6508402182683167609575667 9762603274024751414363501)
        ·
          refine ⟨3660976227759281780386313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9762603274024751414363501 3660976227759281780386313)
          ·
            refine ⟨2745732170819461335289735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3660976227759281780386313 2745732170819461335289735)
            ·
              refine ⟨4118598256229192002934603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2745732170819461335289735 4118598256229192002934603)
              ·
                refine ⟨6177897384343788004401905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4118598256229192002934603 6177897384343788004401905)
                ·
                  refine ⟨4633423038257841003301429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6177897384343788004401905 4633423038257841003301429)
                  ·
                    refine ⟨434383409836672594059509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4633423038257841003301429 434383409836672594059509)
                    ·
                      rfl

theorem cell23_2537876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_2537876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537876 prefixEnd_2537876 := by exact prefixLift 2537876
  have htrace : WordTrace (prefixWord ++ tailWord_2537876) baseStart_2537876 baseEnd_2537876 := by
    simpa [prefixWord, tailWord_2537876, baseEnd_2537876] using wordTrace_append hprefix tailTrace_2537876
  have hstable : (prefixWord ++ tailWord_2537876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537876).length < 2 ^ (prefixWord ++ tailWord_2537876).sum := by decide
  have hdescent : baseEnd_2537876 < baseStart_2537876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537896 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_2537896 : Nat := 118140960795 + 2537896 * 2 ^ 59
def prefixEnd_2537896 : Nat := 4983230072969 + 3 ^ 40 * 2537896 * 2
def baseEnd_2537896 : Nat := 1303160499123107703928435

theorem tailTrace_2537896 : CollatzResearch.WordTrace tailWord_2537896 prefixEnd_2537896 1303160499123107703928435 := by
  unfold tailWord_2537896
  simp only [CollatzResearch.WordTrace]
  refine ⟨46282335806821852487068771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61709781075762469982758361 46282335806821852487068771)
  ·
    refine ⟨69423503710232778730603157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46282335806821852487068771 69423503710232778730603157)
    ·
      refine ⟨3254226736417161502997023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69423503710232778730603157 3254226736417161502997023)
      ·
        refine ⟨4881340104625742254495535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3254226736417161502997023 4881340104625742254495535)
        ·
          refine ⟨7322010156938613381743303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4881340104625742254495535 7322010156938613381743303)
          ·
            refine ⟨10983015235407920072614955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7322010156938613381743303 10983015235407920072614955)
            ·
              refine ⟨16474522853111880108922433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10983015235407920072614955 16474522853111880108922433)
              ·
                refine ⟨12355892139833910081691825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16474522853111880108922433 12355892139833910081691825)
                ·
                  refine ⟨9266919104875432561268869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12355892139833910081691825 9266919104875432561268869)
                  ·
                    refine ⟨1737547332164143605237913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9266919104875432561268869 1737547332164143605237913)
                    ·
                      refine ⟨1303160499123107703928435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737547332164143605237913 1303160499123107703928435)
                      ·
                        rfl

theorem cell23_2537896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_2537896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537896 prefixEnd_2537896 := by exact prefixLift 2537896
  have htrace : WordTrace (prefixWord ++ tailWord_2537896) baseStart_2537896 baseEnd_2537896 := by
    simpa [prefixWord, tailWord_2537896, baseEnd_2537896] using wordTrace_append hprefix tailTrace_2537896
  have hstable : (prefixWord ++ tailWord_2537896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537896).length < 2 ^ (prefixWord ++ tailWord_2537896).sum := by decide
  have hdescent : baseEnd_2537896 < baseStart_2537896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537929 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 3, 1, 3]
def baseStart_2537929 : Nat := 118140960795 + 2537929 * 2 ^ 59
def prefixEnd_2537929 : Nat := 4983230072969 + 3 ^ 40 * 2537929 * 2
def baseEnd_2537929 : Nat := 1303177443984706074815783

theorem tailTrace_2537929 : CollatzResearch.WordTrace tailWord_2537929 prefixEnd_2537929 1303177443984706074815783 := by
  unfold tailWord_2537929
  simp only [CollatzResearch.WordTrace]
  refine ⟨92565875222524151610088841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61710583481682767740059227 92565875222524151610088841)
  ·
    refine ⟨69424406416893113707566631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92565875222524151610088841 69424406416893113707566631)
    ·
      refine ⟨104136609625339670561349947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69424406416893113707566631 104136609625339670561349947)
      ·
        refine ⟨156204914438009505842024921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104136609625339670561349947 156204914438009505842024921)
        ·
          refine ⟨117153685828507129381518691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156204914438009505842024921 117153685828507129381518691)
          ·
            refine ⟨175730528742760694072278037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117153685828507129381518691 175730528742760694072278037)
            ·
              refine ⟨8237368534816907534638033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 175730528742760694072278037 8237368534816907534638033)
              ·
                refine ⟨6178026401112680650978525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8237368534816907534638033 6178026401112680650978525)
                ·
                  refine ⟨2316759900417255244116947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6178026401112680650978525 2316759900417255244116947)
                  ·
                    refine ⟨3475139850625882866175421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2316759900417255244116947 3475139850625882866175421)
                    ·
                      refine ⟨1303177443984706074815783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3475139850625882866175421 1303177443984706074815783)
                      ·
                        rfl

theorem cell23_2537929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 1, 3].length) (baseStart_2537929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537929 prefixEnd_2537929 := by exact prefixLift 2537929
  have htrace : WordTrace (prefixWord ++ tailWord_2537929) baseStart_2537929 baseEnd_2537929 := by
    simpa [prefixWord, tailWord_2537929, baseEnd_2537929] using wordTrace_append hprefix tailTrace_2537929
  have hstable : (prefixWord ++ tailWord_2537929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537929).length < 2 ^ (prefixWord ++ tailWord_2537929).sum := by decide
  have hdescent : baseEnd_2537929 < baseStart_2537929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537949 : List Nat := [1, 4, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_2537949 : Nat := 118140960795 + 2537949 * 2 ^ 59
def prefixEnd_2537949 : Nat := 4983230072969 + 3 ^ 40 * 2537949 * 2
def baseEnd_2537949 : Nat := 434395904532598665521897

theorem tailTrace_2537949 : CollatzResearch.WordTrace tailWord_2537949 prefixEnd_2537949 434395904532598665521897 := by
  unfold tailWord_2537949
  simp only [CollatzResearch.WordTrace]
  refine ⟨92566604682451695025816901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61711069788301130017211267 92566604682451695025816901)
  ·
    refine ⟨17356238377959692817340669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92566604682451695025816901 17356238377959692817340669)
    ·
      refine ⟨6508589391734884806502751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17356238377959692817340669 6508589391734884806502751)
      ·
        refine ⟨9762884087602327209754127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6508589391734884806502751 9762884087602327209754127)
        ·
          refine ⟨14644326131403490814631191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9762884087602327209754127 14644326131403490814631191)
          ·
            refine ⟨21966489197105236221946787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14644326131403490814631191 21966489197105236221946787)
            ·
              refine ⟨32949733795657854332920181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21966489197105236221946787 32949733795657854332920181)
              ·
                refine ⟨3089037543342923843711267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32949733795657854332920181 3089037543342923843711267)
                ·
                  refine ⟨4633556315014385765566901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3089037543342923843711267 4633556315014385765566901)
                  ·
                    refine ⟨434395904532598665521897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4633556315014385765566901 434395904532598665521897)
                    ·
                      rfl

theorem cell23_2537949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_2537949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537949 prefixEnd_2537949 := by exact prefixLift 2537949
  have htrace : WordTrace (prefixWord ++ tailWord_2537949) baseStart_2537949 baseEnd_2537949 := by
    simpa [prefixWord, tailWord_2537949, baseEnd_2537949] using wordTrace_append hprefix tailTrace_2537949
  have hstable : (prefixWord ++ tailWord_2537949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537949).length < 2 ^ (prefixWord ++ tailWord_2537949).sum := by decide
  have hdescent : baseEnd_2537949 < baseStart_2537949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2537963 : List Nat := [1, 1, 1, 1, 2, 3, 7, 2, 1, 1, 3]
def baseStart_2537963 : Nat := 118140960795 + 2537963 * 2 ^ 59
def prefixEnd_2537963 : Nat := 4983230072969 + 3 ^ 40 * 2537963 * 2
def baseEnd_2537963 : Nat := 1303194902326958941790627

theorem tailTrace_2537963 : CollatzResearch.WordTrace tailWord_2537963 prefixEnd_2537963 1303194902326958941790627 := by
  unfold tailWord_2537963
  simp only [CollatzResearch.WordTrace]
  refine ⟨92567115304400975416826543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61711410202933983611217695 92567115304400975416826543)
  ·
    refine ⟨138850672956601463125239815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92567115304400975416826543 138850672956601463125239815)
    ·
      refine ⟨208276009434902194687859723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138850672956601463125239815 208276009434902194687859723)
      ·
        refine ⟨312414014152353292031789585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208276009434902194687859723 312414014152353292031789585)
        ·
          refine ⟨234310510614264969023842189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312414014152353292031789585 234310510614264969023842189)
          ·
            refine ⟨87866441480349363383940821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234310510614264969023842189 87866441480349363383940821)
            ·
              refine ⟨2059369722195688204311113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 87866441480349363383940821 2059369722195688204311113)
              ·
                refine ⟨1544527291646766153233335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2059369722195688204311113 1544527291646766153233335)
                ·
                  refine ⟨2316790937470149229850003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544527291646766153233335 2316790937470149229850003)
                  ·
                    refine ⟨3475186406205223844775005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2316790937470149229850003 3475186406205223844775005)
                    ·
                      refine ⟨1303194902326958941790627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3475186406205223844775005 1303194902326958941790627)
                      ·
                        rfl

theorem cell23_2537963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 2, 1, 1, 3].length) (baseStart_2537963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2537963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2537963 prefixEnd_2537963 := by exact prefixLift 2537963
  have htrace : WordTrace (prefixWord ++ tailWord_2537963) baseStart_2537963 baseEnd_2537963 := by
    simpa [prefixWord, tailWord_2537963, baseEnd_2537963] using wordTrace_append hprefix tailTrace_2537963
  have hstable : (prefixWord ++ tailWord_2537963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2537963).length < 2 ^ (prefixWord ++ tailWord_2537963).sum := by decide
  have hdescent : baseEnd_2537963 < baseStart_2537963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2537963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538003 : List Nat := [1, 1, 1, 2, 1, 5, 2, 5, 1, 2, 2]
def baseStart_2538003 : Nat := 118140960795 + 2538003 * 2 ^ 59
def prefixEnd_2538003 : Nat := 4983230072969 + 3 ^ 40 * 2538003 * 2
def baseEnd_2538003 : Nat := 1303215441553138785290443

theorem tailTrace_2538003 : CollatzResearch.WordTrace tailWord_2538003 prefixEnd_2538003 1303215441553138785290443 := by
  unfold tailWord_2538003
  simp only [CollatzResearch.WordTrace]
  refine ⟨92568574224256062248282663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61712382816170708165521775 92568574224256062248282663)
  ·
    refine ⟨138852861336384093372423995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92568574224256062248282663 138852861336384093372423995)
    ·
      refine ⟨208279292004576140058635993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138852861336384093372423995 208279292004576140058635993)
      ·
        refine ⟨156209469003432105043976995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208279292004576140058635993 156209469003432105043976995)
        ·
          refine ⟨234314203505148157565965493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156209469003432105043976995 234314203505148157565965493)
          ·
            refine ⟨21966956578607639771809265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 234314203505148157565965493 21966956578607639771809265)
            ·
              refine ⟨16475217433955729828856949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21966956578607639771809265 16475217433955729828856949)
              ·
                refine ⟨1544551634433349671455339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16475217433955729828856949 1544551634433349671455339)
                ·
                  refine ⟨2316827451650024507183009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544551634433349671455339 2316827451650024507183009)
                  ·
                    refine ⟨1737620588737518380387257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2316827451650024507183009 1737620588737518380387257)
                    ·
                      refine ⟨1303215441553138785290443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737620588737518380387257 1303215441553138785290443)
                      ·
                        rfl

theorem cell23_2538003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 1, 2, 2].length) (baseStart_2538003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538003 prefixEnd_2538003 := by exact prefixLift 2538003
  have htrace : WordTrace (prefixWord ++ tailWord_2538003) baseStart_2538003 baseEnd_2538003 := by
    simpa [prefixWord, tailWord_2538003, baseEnd_2538003] using wordTrace_append hprefix tailTrace_2538003
  have hstable : (prefixWord ++ tailWord_2538003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538003).length < 2 ^ (prefixWord ++ tailWord_2538003).sum := by decide
  have hdescent : baseEnd_2538003 < baseStart_2538003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538054 : List Nat := [6, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_2538054 : Nat := 118140960795 + 2538054 * 2 ^ 59
def prefixEnd_2538054 : Nat := 4983230072969 + 3 ^ 40 * 2538054 * 2
def baseEnd_2538054 : Nat := 1303241629066518085752709

theorem tailTrace_2538054 : CollatzResearch.WordTrace tailWord_2538054 prefixEnd_2538054 1303241629066518085752709 := by
  unfold tailWord_2538054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2892826073345978061199663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61713622898047531972259477 2892826073345978061199663)
  ·
    refine ⟨4339239110018967091799495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2892826073345978061199663 4339239110018967091799495)
    ·
      refine ⟨6508858665028450637699243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4339239110018967091799495 6508858665028450637699243)
      ·
        refine ⟨9763287997542675956548865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6508858665028450637699243 9763287997542675956548865)
        ·
          refine ⟨7322465998157006967411649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9763287997542675956548865 7322465998157006967411649)
          ·
            refine ⟨5491849498617755225558737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7322465998157006967411649 5491849498617755225558737)
            ·
              refine ⟨4118887123963316419169053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5491849498617755225558737 4118887123963316419169053)
              ·
                refine ⟨1544582671486243657188395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4118887123963316419169053 1544582671486243657188395)
                ·
                  refine ⟨2316874007229365485782593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544582671486243657188395 2316874007229365485782593)
                  ·
                    refine ⟨1737655505422024114336945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2316874007229365485782593 1737655505422024114336945)
                    ·
                      refine ⟨1303241629066518085752709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737655505422024114336945 1303241629066518085752709)
                      ·
                        rfl

theorem cell23_2538054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_2538054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538054 prefixEnd_2538054 := by exact prefixLift 2538054
  have htrace : WordTrace (prefixWord ++ tailWord_2538054) baseStart_2538054 baseEnd_2538054 := by
    simpa [prefixWord, tailWord_2538054, baseEnd_2538054] using wordTrace_append hprefix tailTrace_2538054
  have hstable : (prefixWord ++ tailWord_2538054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538054).length < 2 ^ (prefixWord ++ tailWord_2538054).sum := by decide
  have hdescent : baseEnd_2538054 < baseStart_2538054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538063 : List Nat := [1, 1, 2, 1, 1, 2, 8, 1, 1, 3, 2]
def baseStart_2538063 : Nat := 118140960795 + 2538063 * 2 ^ 59
def prefixEnd_2538063 : Nat := 4983230072969 + 3 ^ 40 * 2538063 * 2
def baseEnd_2538063 : Nat := 1303246250392408550540167

theorem tailTrace_2538063 : CollatzResearch.WordTrace tailWord_2538063 prefixEnd_2538063 1303246250392408550540167 := by
  unfold tailWord_2538063
  simp only [CollatzResearch.WordTrace]
  refine ⟨92570762604038692495466843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61713841736025794996977895 92570762604038692495466843)
  ·
    refine ⟨138856143906058038743200265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92570762604038692495466843 138856143906058038743200265)
    ·
      refine ⟨104142107929543529057400199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138856143906058038743200265 104142107929543529057400199)
      ·
        refine ⟨156213161894315293586100299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104142107929543529057400199 156213161894315293586100299)
        ·
          refine ⟨234319742841472940379150449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156213161894315293586100299 234319742841472940379150449)
          ·
            refine ⟨175739807131104705284362837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234319742841472940379150449 175739807131104705284362837)
            ·
              refine ⟨2059450864817633265051127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 175739807131104705284362837 2059450864817633265051127)
              ·
                refine ⟨3089176297226449897576691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059450864817633265051127 3089176297226449897576691)
                ·
                  refine ⟨4633764445839674846365037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3089176297226449897576691 4633764445839674846365037)
                  ·
                    refine ⟨1737661667189878067386889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4633764445839674846365037 1737661667189878067386889)
                    ·
                      refine ⟨1303246250392408550540167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737661667189878067386889 1303246250392408550540167)
                      ·
                        rfl

theorem cell23_2538063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 1, 3, 2].length) (baseStart_2538063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538063 prefixEnd_2538063 := by exact prefixLift 2538063
  have htrace : WordTrace (prefixWord ++ tailWord_2538063) baseStart_2538063 baseEnd_2538063 := by
    simpa [prefixWord, tailWord_2538063, baseEnd_2538063] using wordTrace_append hprefix tailTrace_2538063
  have hstable : (prefixWord ++ tailWord_2538063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538063).length < 2 ^ (prefixWord ++ tailWord_2538063).sum := by decide
  have hdescent : baseEnd_2538063 < baseStart_2538063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538093 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_2538093 : Nat := 118140960795 + 2538093 * 2 ^ 59
def prefixEnd_2538093 : Nat := 4983230072969 + 3 ^ 40 * 2538093 * 2
def baseEnd_2538093 : Nat := 1303261654812043433165029

theorem tailTrace_2538093 : CollatzResearch.WordTrace tailWord_2538093 prefixEnd_2538093 1303261654812043433165029 := by
  unfold tailWord_2538093
  simp only [CollatzResearch.WordTrace]
  refine ⟨92571856793930007619058933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61714571195953338412705955 92571856793930007619058933)
  ·
    refine ⟨8678611574430938214286775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92571856793930007619058933 8678611574430938214286775)
    ·
      refine ⟨13017917361646407321430163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8678611574430938214286775 13017917361646407321430163)
      ·
        refine ⟨19526876042469610982145245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13017917361646407321430163 19526876042469610982145245)
        ·
          refine ⟨7322578515926104118304467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19526876042469610982145245 7322578515926104118304467)
          ·
            refine ⟨10983867773889156177456701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7322578515926104118304467 10983867773889156177456701)
            ·
              refine ⟨4118950415208433566546263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10983867773889156177456701 4118950415208433566546263)
              ·
                refine ⟨6178425622812650349819395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4118950415208433566546263 6178425622812650349819395)
                ·
                  refine ⟨9267638434218975524729093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6178425622812650349819395 9267638434218975524729093)
                  ·
                    refine ⟨1737682206416057910886705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9267638434218975524729093 1737682206416057910886705)
                    ·
                      refine ⟨1303261654812043433165029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737682206416057910886705 1303261654812043433165029)
                      ·
                        rfl

theorem cell23_2538093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_2538093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538093 prefixEnd_2538093 := by exact prefixLift 2538093
  have htrace : WordTrace (prefixWord ++ tailWord_2538093) baseStart_2538093 baseEnd_2538093 := by
    simpa [prefixWord, tailWord_2538093, baseEnd_2538093] using wordTrace_append hprefix tailTrace_2538093
  have hstable : (prefixWord ++ tailWord_2538093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538093).length < 2 ^ (prefixWord ++ tailWord_2538093).sum := by decide
  have hdescent : baseEnd_2538093 < baseStart_2538093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538136 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 2, 5, 2]
def baseStart_2538136 : Nat := 118140960795 + 2538136 * 2 ^ 59
def prefixEnd_2538136 : Nat := 4983230072969 + 3 ^ 40 * 2538136 * 2
def baseEnd_2538136 : Nat := 1303283734480186764927331

theorem tailTrace_2538136 : CollatzResearch.WordTrace tailWord_2538136 prefixEnd_2538136 1303283734480186764927331 := by
  unfold tailWord_2538136
  simp only [CollatzResearch.WordTrace]
  refine ⟨46286712566387112981437131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61715616755182817308582841 46286712566387112981437131)
  ·
    refine ⟨69430068849580669472155697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46286712566387112981437131 69430068849580669472155697)
    ·
      refine ⟨52072551637185502104116773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69430068849580669472155697 52072551637185502104116773)
      ·
        refine ⟨9763603431972281644521895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52072551637185502104116773 9763603431972281644521895)
        ·
          refine ⟨14645405147958422466782843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9763603431972281644521895 14645405147958422466782843)
          ·
            refine ⟨21968107721937633700174265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14645405147958422466782843 21968107721937633700174265)
            ·
              refine ⟨16476080791453225275130699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21968107721937633700174265 16476080791453225275130699)
              ·
                refine ⟨24714121187179837912696049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16476080791453225275130699 24714121187179837912696049)
                ·
                  refine ⟨18535590890384878434522037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24714121187179837912696049 18535590890384878434522037)
                  ·
                    refine ⟨1737711645973582353236441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18535590890384878434522037 1737711645973582353236441)
                    ·
                      refine ⟨1303283734480186764927331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737711645973582353236441 1303283734480186764927331)
                      ·
                        rfl

theorem cell23_2538136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_2538136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538136 prefixEnd_2538136 := by exact prefixLift 2538136
  have htrace : WordTrace (prefixWord ++ tailWord_2538136) baseStart_2538136 baseEnd_2538136 := by
    simpa [prefixWord, tailWord_2538136, baseEnd_2538136] using wordTrace_append hprefix tailTrace_2538136
  have hstable : (prefixWord ++ tailWord_2538136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538136).length < 2 ^ (prefixWord ++ tailWord_2538136).sum := by decide
  have hdescent : baseEnd_2538136 < baseStart_2538136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538144 : List Nat := [2, 1, 1, 4, 5, 1, 2, 1, 2, 2, 2]
def baseStart_2538144 : Nat := 118140960795 + 2538144 * 2 ^ 59
def prefixEnd_2538144 : Nat := 4983230072969 + 3 ^ 40 * 2538144 * 2
def baseEnd_2538144 : Nat := 1303287842325422733627295

theorem tailTrace_2538144 : CollatzResearch.WordTrace tailWord_2538144 prefixEnd_2538144 1303287842325422733627295 := by
  unfold tailWord_2538144
  simp only [CollatzResearch.WordTrace]
  refine ⟨46286858458372621664582743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61715811277830162219443657 46286858458372621664582743)
  ·
    refine ⟨69430287687558932496874115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46286858458372621664582743 69430287687558932496874115)
    ·
      refine ⟨104145431531338398745311173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69430287687558932496874115 104145431531338398745311173)
      ·
        refine ⟨19527268412125949764745845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104145431531338398745311173 19527268412125949764745845)
        ·
          refine ⟨1830681413636807790444923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19527268412125949764745845 1830681413636807790444923)
          ·
            refine ⟨2746022120455211685667385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1830681413636807790444923 2746022120455211685667385)
            ·
              refine ⟨2059516590341408764250539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2746022120455211685667385 2059516590341408764250539)
              ·
                refine ⟨3089274885512113146375809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059516590341408764250539 3089274885512113146375809)
                ·
                  refine ⟨2316956164134084859781857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3089274885512113146375809 2316956164134084859781857)
                  ·
                    refine ⟨1737717123100563644836393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2316956164134084859781857 1737717123100563644836393)
                    ·
                      refine ⟨1303287842325422733627295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737717123100563644836393 1303287842325422733627295)
                      ·
                        rfl

theorem cell23_2538144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_2538144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538144 prefixEnd_2538144 := by exact prefixLift 2538144
  have htrace : WordTrace (prefixWord ++ tailWord_2538144) baseStart_2538144 baseEnd_2538144 := by
    simpa [prefixWord, tailWord_2538144, baseEnd_2538144] using wordTrace_append hprefix tailTrace_2538144
  have hstable : (prefixWord ++ tailWord_2538144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538144).length < 2 ^ (prefixWord ++ tailWord_2538144).sum := by decide
  have hdescent : baseEnd_2538144 < baseStart_2538144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538149 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 6, 1, 4]
def baseStart_2538149 : Nat := 118140960795 + 2538149 * 2 ^ 59
def prefixEnd_2538149 : Nat := 4983230072969 + 3 ^ 40 * 2538149 * 2
def baseEnd_2538149 : Nat := 1303290409728695214064771

theorem tailTrace_2538149 : CollatzResearch.WordTrace tailWord_2538149 prefixEnd_2538149 1303290409728695214064771 := by
  unfold tailWord_2538149
  simp only [CollatzResearch.WordTrace]
  refine ⟨92573899281727129183097501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61715932854484752788731667 92573899281727129183097501)
  ·
    refine ⟨34715212230647673443661563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92573899281727129183097501 34715212230647673443661563)
    ·
      refine ⟨52072818345971510165492345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34715212230647673443661563 52072818345971510165492345)
      ·
        refine ⟨39054613759478632624119259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52072818345971510165492345 39054613759478632624119259)
        ·
          refine ⟨58581920639217948936178889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39054613759478632624119259 58581920639217948936178889)
          ·
            refine ⟨43936440479413461702134167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58581920639217948936178889 43936440479413461702134167)
            ·
              refine ⟨65904660719120192553201251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43936440479413461702134167 65904660719120192553201251)
              ·
                refine ⟨98856991078680288829801877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65904660719120192553201251 98856991078680288829801877)
                ·
                  refine ⟨4633921456813138538896963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98856991078680288829801877 4633921456813138538896963)
                  ·
                    refine ⟨6950882185219707808345445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4633921456813138538896963 6950882185219707808345445)
                    ·
                      refine ⟨1303290409728695214064771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6950882185219707808345445 1303290409728695214064771)
                      ·
                        rfl

theorem cell23_2538149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_2538149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538149 prefixEnd_2538149 := by exact prefixLift 2538149
  have htrace : WordTrace (prefixWord ++ tailWord_2538149) baseStart_2538149 baseEnd_2538149 := by
    simpa [prefixWord, tailWord_2538149, baseEnd_2538149] using wordTrace_append hprefix tailTrace_2538149
  have hstable : (prefixWord ++ tailWord_2538149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538149).length < 2 ^ (prefixWord ++ tailWord_2538149).sum := by decide
  have hdescent : baseEnd_2538149 < baseStart_2538149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538193 : List Nat := [1, 2, 2, 1, 2, 3, 3, 4, 1, 4]
def baseStart_2538193 : Nat := 118140960795 + 2538193 * 2 ^ 59
def prefixEnd_2538193 : Nat := 4983230072969 + 3 ^ 40 * 2538193 * 2
def baseEnd_2538193 : Nat := 434437667625831013971523

theorem tailTrace_2538193 : CollatzResearch.WordTrace tailWord_2538193 prefixEnd_2538193 434437667625831013971523 := by
  unfold tailWord_2538193
  simp only [CollatzResearch.WordTrace]
  refine ⟨92575504093567724697699233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61717002729045149798466155 92575504093567724697699233)
  ·
    refine ⟨69431628070175793523274425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92575504093567724697699233 69431628070175793523274425)
    ·
      refine ⟨52073721052631845142455819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69431628070175793523274425 52073721052631845142455819)
      ·
        refine ⟨78110581578947767713683729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52073721052631845142455819 78110581578947767713683729)
        ·
          refine ⟨58582936184210825785262797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78110581578947767713683729 58582936184210825785262797)
          ·
            refine ⟨21968601069079059669473549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58582936184210825785262797 21968601069079059669473549)
            ·
              refine ⟨8238225400904647376052581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21968601069079059669473549 8238225400904647376052581)
              ·
                refine ⟨1544667262669621383009859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8238225400904647376052581 1544667262669621383009859)
                ·
                  refine ⟨2317000894004432074514789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544667262669621383009859 2317000894004432074514789)
                  ·
                    refine ⟨434437667625831013971523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2317000894004432074514789 434437667625831013971523)
                    ·
                      rfl

theorem cell23_2538193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_2538193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538193 prefixEnd_2538193 := by exact prefixLift 2538193
  have htrace : WordTrace (prefixWord ++ tailWord_2538193) baseStart_2538193 baseEnd_2538193 := by
    simpa [prefixWord, tailWord_2538193, baseEnd_2538193] using wordTrace_append hprefix tailTrace_2538193
  have hstable : (prefixWord ++ tailWord_2538193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538193).length < 2 ^ (prefixWord ++ tailWord_2538193).sum := by decide
  have hdescent : baseEnd_2538193 < baseStart_2538193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538249 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 3, 6]
def baseStart_2538249 : Nat := 118140960795 + 2538249 * 2 ^ 59
def prefixEnd_2538249 : Nat := 4983230072969 + 3 ^ 40 * 2538249 * 2
def baseEnd_2538249 : Nat := 434447252598048274271437

theorem tailTrace_2538249 : CollatzResearch.WordTrace tailWord_2538249 prefixEnd_2538249 434447252598048274271437 := by
  unfold tailWord_2538249
  simp only [CollatzResearch.WordTrace]
  refine ⟨92577546581364846261737801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61718364387576564174491867 92577546581364846261737801)
  ·
    refine ⟨69433159936023634696303351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92577546581364846261737801 69433159936023634696303351)
    ·
      refine ⟨104149739904035452044455027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69433159936023634696303351 104149739904035452044455027)
      ·
        refine ⟨156224609856053178066682541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104149739904035452044455027 156224609856053178066682541)
        ·
          refine ⟨58584228696019941775005953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156224609856053178066682541 58584228696019941775005953)
          ·
            refine ⟨43938171522014956331254465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58584228696019941775005953 43938171522014956331254465)
            ·
              refine ⟨32953628641511217248440849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43938171522014956331254465 32953628641511217248440849)
              ·
                refine ⟨24715221481133412936330637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32953628641511217248440849 24715221481133412936330637)
                ·
                  refine ⟨9268208055425029851123989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24715221481133412936330637 9268208055425029851123989)
                  ·
                    refine ⟨434447252598048274271437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9268208055425029851123989 434447252598048274271437)
                    ·
                      rfl

theorem cell23_2538249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 6].length) (baseStart_2538249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538249 prefixEnd_2538249 := by exact prefixLift 2538249
  have htrace : WordTrace (prefixWord ++ tailWord_2538249) baseStart_2538249 baseEnd_2538249 := by
    simpa [prefixWord, tailWord_2538249, baseEnd_2538249] using wordTrace_append hprefix tailTrace_2538249
  have hstable : (prefixWord ++ tailWord_2538249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538249).length < 2 ^ (prefixWord ++ tailWord_2538249).sum := by decide
  have hdescent : baseEnd_2538249 < baseStart_2538249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538250 : List Nat := [3, 1, 2, 2, 1, 2, 1, 6, 1, 1, 3]
def baseStart_2538250 : Nat := 118140960795 + 2538250 * 2 ^ 59
def prefixEnd_2538250 : Nat := 4983230072969 + 3 ^ 40 * 2538250 * 2
def baseEnd_2538250 : Nat := 1303342271274799318901807

theorem tailTrace_2538250 : CollatzResearch.WordTrace tailWord_2538250 prefixEnd_2538250 1303342271274799318901807 := by
  unfold tailWord_2538250
  simp only [CollatzResearch.WordTrace]
  refine ⟨23144395763590305858131051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61718388702907482288349469 23144395763590305858131051)
  ·
    refine ⟨34716593645385458787196577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23144395763590305858131051 34716593645385458787196577)
    ·
      refine ⟨26037445234039094090397433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34716593645385458787196577 26037445234039094090397433)
      ·
        refine ⟨19528083925529320567798075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26037445234039094090397433 19528083925529320567798075)
        ·
          refine ⟨29292125888293980851697113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19528083925529320567798075 29292125888293980851697113)
          ·
            refine ⟨21969094416220485638772835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29292125888293980851697113 21969094416220485638772835)
            ·
              refine ⟨32953641624330728458159253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21969094416220485638772835 32953641624330728458159253)
              ·
                refine ⟨1544701951140502896476215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32953641624330728458159253 1544701951140502896476215)
                ·
                  refine ⟨2317052926710754344714323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544701951140502896476215 2317052926710754344714323)
                  ·
                    refine ⟨3475579390066131517071485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2317052926710754344714323 3475579390066131517071485)
                    ·
                      refine ⟨1303342271274799318901807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3475579390066131517071485 1303342271274799318901807)
                      ·
                        rfl

theorem cell23_2538250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_2538250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538250 prefixEnd_2538250 := by exact prefixLift 2538250
  have htrace : WordTrace (prefixWord ++ tailWord_2538250) baseStart_2538250 baseEnd_2538250 := by
    simpa [prefixWord, tailWord_2538250, baseEnd_2538250] using wordTrace_append hprefix tailTrace_2538250
  have hstable : (prefixWord ++ tailWord_2538250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538250).length < 2 ^ (prefixWord ++ tailWord_2538250).sum := by decide
  have hdescent : baseEnd_2538250 < baseStart_2538250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538273 : List Nat := [1, 2, 3, 2, 1, 2, 4, 2, 1, 1, 4]
def baseStart_2538273 : Nat := 118140960795 + 2538273 * 2 ^ 59
def prefixEnd_2538273 : Nat := 4983230072969 + 3 ^ 40 * 2538273 * 2
def baseEnd_2538273 : Nat := 1303354081329852728914201

theorem tailTrace_2538273 : CollatzResearch.WordTrace tailWord_2538273 prefixEnd_2538273 1303354081329852728914201 := by
  unfold tailWord_2538273
  simp only [CollatzResearch.WordTrace]
  refine ⟨92578421933277898360611473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61718947955518598907074315 92578421933277898360611473)
  ·
    refine ⟨69433816449958423770458605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92578421933277898360611473 69433816449958423770458605)
    ·
      refine ⟨26037681168734408913921977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69433816449958423770458605 26037681168734408913921977)
      ·
        refine ⟨19528260876550806685441483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26037681168734408913921977 19528260876550806685441483)
        ·
          refine ⟨29292391314826210028162225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19528260876550806685441483 29292391314826210028162225)
          ·
            refine ⟨21969293486119657521121669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29292391314826210028162225 21969293486119657521121669)
            ·
              refine ⟨4119242528647435785210313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21969293486119657521121669 4119242528647435785210313)
              ·
                refine ⟨3089431896485576838907735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4119242528647435785210313 3089431896485576838907735)
                ·
                  refine ⟨4634147844728365258361603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3089431896485576838907735 4634147844728365258361603)
                  ·
                    refine ⟨6951221767092547887542405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4634147844728365258361603 6951221767092547887542405)
                    ·
                      refine ⟨1303354081329852728914201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6951221767092547887542405 1303354081329852728914201)
                      ·
                        rfl

theorem cell23_2538273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_2538273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538273 prefixEnd_2538273 := by exact prefixLift 2538273
  have htrace : WordTrace (prefixWord ++ tailWord_2538273) baseStart_2538273 baseEnd_2538273 := by
    simpa [prefixWord, tailWord_2538273, baseEnd_2538273] using wordTrace_append hprefix tailTrace_2538273
  have hstable : (prefixWord ++ tailWord_2538273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538273).length < 2 ^ (prefixWord ++ tailWord_2538273).sum := by decide
  have hdescent : baseEnd_2538273 < baseStart_2538273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538293 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_2538293 : Nat := 118140960795 + 2538293 * 2 ^ 59
def prefixEnd_2538293 : Nat := 4983230072969 + 3 ^ 40 * 2538293 * 2
def baseEnd_2538293 : Nat := 1303364350942942650664109

theorem tailTrace_2538293 : CollatzResearch.WordTrace tailWord_2538293 prefixEnd_2538293 1303364350942942650664109 := by
  unfold tailWord_2538293
  simp only [CollatzResearch.WordTrace]
  refine ⟨92579151393205441776339533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61719434262136961184226355 92579151393205441776339533)
  ·
    refine ⟨34717181772452040666127325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92579151393205441776339533 34717181772452040666127325)
    ·
      refine ⟨13018943164669515249797747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34717181772452040666127325 13018943164669515249797747)
      ·
        refine ⟨19528414747004272874696621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13018943164669515249797747 19528414747004272874696621)
        ·
          refine ⟨7323155530126602328011233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19528414747004272874696621 7323155530126602328011233)
          ·
            refine ⟨5492366647594951746008425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7323155530126602328011233 5492366647594951746008425)
            ·
              refine ⟨4119274985696213809506319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5492366647594951746008425 4119274985696213809506319)
              ·
                refine ⟨6178912478544320714259479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4119274985696213809506319 6178912478544320714259479)
                ·
                  refine ⟨9268368717816481071389219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6178912478544320714259479 9268368717816481071389219)
                  ·
                    refine ⟨13902553076724721607083829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9268368717816481071389219 13902553076724721607083829)
                    ·
                      refine ⟨1303364350942942650664109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13902553076724721607083829 1303364350942942650664109)
                      ·
                        rfl

theorem cell23_2538293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_2538293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538293 prefixEnd_2538293 := by exact prefixLift 2538293
  have htrace : WordTrace (prefixWord ++ tailWord_2538293) baseStart_2538293 baseEnd_2538293 := by
    simpa [prefixWord, tailWord_2538293, baseEnd_2538293] using wordTrace_append hprefix tailTrace_2538293
  have hstable : (prefixWord ++ tailWord_2538293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538293).length < 2 ^ (prefixWord ++ tailWord_2538293).sum := by decide
  have hdescent : baseEnd_2538293 < baseStart_2538293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538317 : List Nat := [1, 6, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_2538317 : Nat := 118140960795 + 2538317 * 2 ^ 59
def prefixEnd_2538317 : Nat := 4983230072969 + 3 ^ 40 * 2538317 * 2
def baseEnd_2538317 : Nat := 434458891492883518921333

theorem tailTrace_2538317 : CollatzResearch.WordTrace tailWord_2538317 prefixEnd_2538317 434458891492883518921333 := by
  unfold tailWord_2538317
  simp only [CollatzResearch.WordTrace]
  refine ⟨92580026745118493875213205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61720017830078995916808803 92580026745118493875213205)
  ·
    refine ⟨4339688753677429400400619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92580026745118493875213205 4339688753677429400400619)
    ·
      refine ⟨6509533130516144100600929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4339688753677429400400619 6509533130516144100600929)
      ·
        refine ⟨4882149847887108075450697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6509533130516144100600929 4882149847887108075450697)
        ·
          refine ⟨3661612385915331056588023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4882149847887108075450697 3661612385915331056588023)
          ·
            refine ⟨5492418578872996584882035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3661612385915331056588023 5492418578872996584882035)
            ·
              refine ⟨8238627868309494877323053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5492418578872996584882035 8238627868309494877323053)
              ·
                refine ⟨3089485450616060578996145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8238627868309494877323053 3089485450616060578996145)
                ·
                  refine ⟨2317114087962045434247109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3089485450616060578996145 2317114087962045434247109)
                  ·
                    refine ⟨434458891492883518921333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2317114087962045434247109 434458891492883518921333)
                    ·
                      rfl

theorem cell23_2538317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_2538317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538317 prefixEnd_2538317 := by exact prefixLift 2538317
  have htrace : WordTrace (prefixWord ++ tailWord_2538317) baseStart_2538317 baseEnd_2538317 := by
    simpa [prefixWord, tailWord_2538317, baseEnd_2538317] using wordTrace_append hprefix tailTrace_2538317
  have hstable : (prefixWord ++ tailWord_2538317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538317).length < 2 ^ (prefixWord ++ tailWord_2538317).sum := by decide
  have hdescent : baseEnd_2538317 < baseStart_2538317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538357 : List Nat := [1, 3, 4, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2538357 : Nat := 118140960795 + 2538357 * 2 ^ 59
def prefixEnd_2538357 : Nat := 4983230072969 + 3 ^ 40 * 2538357 * 2
def baseEnd_2538357 : Nat := 1303397213704830400263815

theorem tailTrace_2538357 : CollatzResearch.WordTrace tailWord_2538357 prefixEnd_2538357 1303397213704830400263815 := by
  unfold tailWord_2538357
  simp only [CollatzResearch.WordTrace]
  refine ⟨92581485664973580706669325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61720990443315720471112883 92581485664973580706669325)
  ·
    refine ⟨34718057124365092765000997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92581485664973580706669325 34718057124365092765000997)
    ·
      refine ⟨6509635710818454893437687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34718057124365092765000997 6509635710818454893437687)
      ·
        refine ⟨9764453566227682340156531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6509635710818454893437687 9764453566227682340156531)
        ·
          refine ⟨14646680349341523510234797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9764453566227682340156531 14646680349341523510234797)
          ·
            refine ⟨5492505131003071316338049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14646680349341523510234797 5492505131003071316338049)
            ·
              refine ⟨4119378848252303487253537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5492505131003071316338049 4119378848252303487253537)
              ·
                refine ⟨3089534136189227615440153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4119378848252303487253537 3089534136189227615440153)
                ·
                  refine ⟨2317150602141920711580115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3089534136189227615440153 2317150602141920711580115)
                  ·
                    refine ⟨3475725903212881067370173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2317150602141920711580115 3475725903212881067370173)
                    ·
                      refine ⟨1303397213704830400263815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3475725903212881067370173 1303397213704830400263815)
                      ·
                        rfl

theorem cell23_2538357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2538357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538357 prefixEnd_2538357 := by exact prefixLift 2538357
  have htrace : WordTrace (prefixWord ++ tailWord_2538357) baseStart_2538357 baseEnd_2538357 := by
    simpa [prefixWord, tailWord_2538357, baseEnd_2538357] using wordTrace_append hprefix tailTrace_2538357
  have hstable : (prefixWord ++ tailWord_2538357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538357).length < 2 ^ (prefixWord ++ tailWord_2538357).sum := by decide
  have hdescent : baseEnd_2538357 < baseStart_2538357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538358 : List Nat := [5, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2]
def baseStart_2538358 : Nat := 118140960795 + 2538358 * 2 ^ 59
def prefixEnd_2538358 : Nat := 4983230072969 + 3 ^ 40 * 2538358 * 2
def baseEnd_2538358 : Nat := 1303397727185484896351311

theorem tailTrace_2538358 : CollatzResearch.WordTrace tailWord_2538358 prefixEnd_2538358 1303397727185484896351311 := by
  unfold tailWord_2538358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5786345133623122367340983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61721014758646638584970485 5786345133623122367340983)
  ·
    refine ⟨8679517700434683551011475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5786345133623122367340983 8679517700434683551011475)
    ·
      refine ⟨13019276550652025326517213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8679517700434683551011475 13019276550652025326517213)
      ·
        refine ⟨4882228706494509497443955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13019276550652025326517213 4882228706494509497443955)
        ·
          refine ⟨7323343059741764246165933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4882228706494509497443955 7323343059741764246165933)
          ·
            refine ⟨2746253647403161592312225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7323343059741764246165933 2746253647403161592312225)
            ·
              refine ⟨2059690235552371194234169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2746253647403161592312225 2059690235552371194234169)
              ·
                refine ⟨1544767676664278395675627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2059690235552371194234169 1544767676664278395675627)
                ·
                  refine ⟨2317151514996417593513441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544767676664278395675627 2317151514996417593513441)
                  ·
                    refine ⟨1737863636247313195135081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2317151514996417593513441 1737863636247313195135081)
                    ·
                      refine ⟨1303397727185484896351311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737863636247313195135081 1303397727185484896351311)
                      ·
                        rfl

theorem cell23_2538358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_2538358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538358 prefixEnd_2538358 := by exact prefixLift 2538358
  have htrace : WordTrace (prefixWord ++ tailWord_2538358) baseStart_2538358 baseEnd_2538358 := by
    simpa [prefixWord, tailWord_2538358, baseEnd_2538358] using wordTrace_append hprefix tailTrace_2538358
  have hstable : (prefixWord ++ tailWord_2538358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538358).length < 2 ^ (prefixWord ++ tailWord_2538358).sum := by decide
  have hdescent : baseEnd_2538358 < baseStart_2538358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538403 : List Nat := [1, 1, 1, 4, 1, 2, 3, 5, 5]
def baseStart_2538403 : Nat := 118140960795 + 2538403 * 2 ^ 59
def prefixEnd_2538403 : Nat := 4983230072969 + 3 ^ 40 * 2538403 * 2
def baseEnd_2538403 : Nat := 144824537090548580032067

theorem tailTrace_2538403 : CollatzResearch.WordTrace tailWord_2538403 prefixEnd_2538403 144824537090548580032067 := by
  unfold tailWord_2538403
  simp only [CollatzResearch.WordTrace]
  refine ⟨92583163422806930562843863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61722108948537953708562575 92583163422806930562843863)
  ·
    refine ⟨138874745134210395844265795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92583163422806930562843863 138874745134210395844265795)
    ·
      refine ⟨208312117701315593766398693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138874745134210395844265795 208312117701315593766398693)
      ·
        refine ⟨39058522068996673831199755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208312117701315593766398693 39058522068996673831199755)
        ·
          refine ⟨58587783103495010746799633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39058522068996673831199755 58587783103495010746799633)
          ·
            refine ⟨43940837327621258060099725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58587783103495010746799633 43940837327621258060099725)
            ·
              refine ⟨16477813997857971772537397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43940837327621258060099725 16477813997857971772537397)
              ·
                refine ⟨1544795062299184853675381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16477813997857971772537397 1544795062299184853675381)
                ·
                  refine ⟨144824537090548580032067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1544795062299184853675381 144824537090548580032067)
                  ·
                    rfl

theorem cell23_2538403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 5].length) (baseStart_2538403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538403 prefixEnd_2538403 := by exact prefixLift 2538403
  have htrace : WordTrace (prefixWord ++ tailWord_2538403) baseStart_2538403 baseEnd_2538403 := by
    simpa [prefixWord, tailWord_2538403, baseEnd_2538403] using wordTrace_append hprefix tailTrace_2538403
  have hstable : (prefixWord ++ tailWord_2538403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538403).length < 2 ^ (prefixWord ++ tailWord_2538403).sum := by decide
  have hdescent : baseEnd_2538403 < baseStart_2538403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538420 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 7]
def baseStart_2538420 : Nat := 118140960795 + 2538420 * 2 ^ 59
def prefixEnd_2538420 : Nat := 4983230072969 + 3 ^ 40 * 2538420 * 2
def baseEnd_2538420 : Nat := 144825506998451517086225

theorem tailTrace_2538420 : CollatzResearch.WordTrace tailWord_2538420 prefixEnd_2538420 144825506998451517086225 := by
  unfold tailWord_2538420
  simp only [CollatzResearch.WordTrace]
  refine ⟨46291891731872671233106357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61722522309163561644141809 46291891731872671233106357)
  ·
    refine ⟨4339864849863062928103721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46291891731872671233106357 4339864849863062928103721)
    ·
      refine ⟨3254898637397297196077791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4339864849863062928103721 3254898637397297196077791)
      ·
        refine ⟨4882347956095945794116687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3254898637397297196077791 4882347956095945794116687)
        ·
          refine ⟨7323521934143918691175031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4882347956095945794116687 7323521934143918691175031)
          ·
            refine ⟨10985282901215878036762547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7323521934143918691175031 10985282901215878036762547)
            ·
              refine ⟨16477924351823817055143821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10985282901215878036762547 16477924351823817055143821)
              ·
                refine ⟨6179221631933931395678933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16477924351823817055143821 6179221631933931395678933)
                ·
                  refine ⟨144825506998451517086225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6179221631933931395678933 144825506998451517086225)
                  ·
                    rfl

theorem cell23_2538420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_2538420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538420 prefixEnd_2538420 := by exact prefixLift 2538420
  have htrace : WordTrace (prefixWord ++ tailWord_2538420) baseStart_2538420 baseEnd_2538420 := by
    simpa [prefixWord, tailWord_2538420, baseEnd_2538420] using wordTrace_append hprefix tailTrace_2538420
  have hstable : (prefixWord ++ tailWord_2538420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538420).length < 2 ^ (prefixWord ++ tailWord_2538420).sum := by decide
  have hdescent : baseEnd_2538420 < baseStart_2538420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538423 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 1, 7, 2]
def baseStart_2538423 : Nat := 118140960795 + 2538423 * 2 ^ 59
def prefixEnd_2538423 : Nat := 4983230072969 + 3 ^ 40 * 2538423 * 2
def baseEnd_2538423 : Nat := 1303431103428027142038511

theorem tailTrace_2538423 : CollatzResearch.WordTrace tailWord_2538423 prefixEnd_2538423 1303431103428027142038511 := by
  unfold tailWord_2538423
  simp only [CollatzResearch.WordTrace]
  refine ⟨92583892882734473978571923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61722595255156315985714615 92583892882734473978571923)
  ·
    refine ⟨138875839324101710967857885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92583892882734473978571923 138875839324101710967857885)
    ·
      refine ⟨52078439746538141612946707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138875839324101710967857885 52078439746538141612946707)
      ·
        refine ⟨78117659619807212419420061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52078439746538141612946707 78117659619807212419420061)
        ·
          refine ⟨29294122357427704657282523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78117659619807212419420061 29294122357427704657282523)
          ·
            refine ⟨43941183536141556985923785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29294122357427704657282523 43941183536141556985923785)
            ·
              refine ⟨32955887652106167739442839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43941183536141556985923785 32955887652106167739442839)
              ·
                refine ⟨49433831478159251609164259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32955887652106167739442839 49433831478159251609164259)
                ·
                  refine ⟨74150747217238877413746389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49433831478159251609164259 74150747217238877413746389)
                  ·
                    refine ⟨1737908137904036189384681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 74150747217238877413746389 1737908137904036189384681)
                    ·
                      refine ⟨1303431103428027142038511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1737908137904036189384681 1303431103428027142038511)
                      ·
                        rfl

theorem cell23_2538423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 7, 2].length) (baseStart_2538423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538423 prefixEnd_2538423 := by exact prefixLift 2538423
  have htrace : WordTrace (prefixWord ++ tailWord_2538423) baseStart_2538423 baseEnd_2538423 := by
    simpa [prefixWord, tailWord_2538423, baseEnd_2538423] using wordTrace_append hprefix tailTrace_2538423
  have hstable : (prefixWord ++ tailWord_2538423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538423).length < 2 ^ (prefixWord ++ tailWord_2538423).sum := by decide
  have hdescent : baseEnd_2538423 < baseStart_2538423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538426 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_2538426 : Nat := 118140960795 + 2538426 * 2 ^ 59
def prefixEnd_2538426 : Nat := 4983230072969 + 3 ^ 40 * 2538426 * 2
def baseEnd_2538426 : Nat := 1303432643869990630300997

theorem tailTrace_2538426 : CollatzResearch.WordTrace tailWord_2538426 prefixEnd_2538426 1303432643869990630300997 := by
  unfold tailWord_2538426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23146000575430901372732783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61722668201149070327287421 23146000575430901372732783)
  ·
    refine ⟨34719000863146352059099175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23146000575430901372732783 34719000863146352059099175)
    ·
      refine ⟨52078501294719528088648763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34719000863146352059099175 52078501294719528088648763)
      ·
        refine ⟨78117751942079292132973145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52078501294719528088648763 78117751942079292132973145)
        ·
          refine ⟨58588313956559469099729859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78117751942079292132973145 58588313956559469099729859)
          ·
            refine ⟨87882470934839203649594789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58588313956559469099729859 87882470934839203649594789)
            ·
              refine ⟨16477963300282350684299023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87882470934839203649594789 16477963300282350684299023)
              ·
                refine ⟨24716944950423526026448535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16477963300282350684299023 24716944950423526026448535)
                ·
                  refine ⟨37075417425635289039672803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24716944950423526026448535 37075417425635289039672803)
                  ·
                    refine ⟨55613126138452933559509205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37075417425635289039672803 55613126138452933559509205)
                    ·
                      refine ⟨1303432643869990630300997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55613126138452933559509205 1303432643869990630300997)
                      ·
                        rfl

theorem cell23_2538426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_2538426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538426 prefixEnd_2538426 := by exact prefixLift 2538426
  have htrace : WordTrace (prefixWord ++ tailWord_2538426) baseStart_2538426 baseEnd_2538426 := by
    simpa [prefixWord, tailWord_2538426, baseEnd_2538426] using wordTrace_append hprefix tailTrace_2538426
  have hstable : (prefixWord ++ tailWord_2538426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538426).length < 2 ^ (prefixWord ++ tailWord_2538426).sum := by decide
  have hdescent : baseEnd_2538426 < baseStart_2538426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538454 : List Nat := [5, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_2538454 : Nat := 118140960795 + 2538454 * 2 ^ 59
def prefixEnd_2538454 : Nat := 4983230072969 + 3 ^ 40 * 2538454 * 2
def baseEnd_2538454 : Nat := 144827446814257391194541

theorem tailTrace_2538454 : CollatzResearch.WordTrace tailWord_2538454 prefixEnd_2538454 144827446814257391194541 := by
  unfold tailWord_2538454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5786563971601385392059401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61723349030414777515300277 5786563971601385392059401)
  ·
    refine ⟨4339922978701039044044551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5786563971601385392059401 4339922978701039044044551)
    ·
      refine ⟨6509884468051558566066827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4339922978701039044044551 6509884468051558566066827)
      ·
        refine ⟨9764826702077337849100241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6509884468051558566066827 9764826702077337849100241)
        ·
          refine ⟨7323620026558003386825181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9764826702077337849100241 7323620026558003386825181)
          ·
            refine ⟨2746357509959251270059443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7323620026558003386825181 2746357509959251270059443)
            ·
              refine ⟨4119536264938876905089165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746357509959251270059443 4119536264938876905089165)
              ·
                refine ⟨1544826099352078839408437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4119536264938876905089165 1544826099352078839408437)
                ·
                  refine ⟨144827446814257391194541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1544826099352078839408437 144827446814257391194541)
                  ·
                    rfl

theorem cell23_2538454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_2538454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538454 prefixEnd_2538454 := by exact prefixLift 2538454
  have htrace : WordTrace (prefixWord ++ tailWord_2538454) baseStart_2538454 baseEnd_2538454 := by
    simpa [prefixWord, tailWord_2538454, baseEnd_2538454] using wordTrace_append hprefix tailTrace_2538454
  have hstable : (prefixWord ++ tailWord_2538454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538454).length < 2 ^ (prefixWord ++ tailWord_2538454).sum := by decide
  have hdescent : baseEnd_2538454 < baseStart_2538454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538496 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 8]
def baseStart_2538496 : Nat := 118140960795 + 2538496 * 2 ^ 59
def prefixEnd_2538496 : Nat := 4983230072969 + 3 ^ 40 * 2538496 * 2
def baseEnd_2538496 : Nat := 1303468587515805356425675

theorem tailTrace_2538496 : CollatzResearch.WordTrace tailWord_2538496 prefixEnd_2538496 1303468587515805356425675 := by
  unfold tailWord_2538496
  simp only [CollatzResearch.WordTrace]
  refine ⟨46293277705735003722989671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61724370274313338297319561 46293277705735003722989671)
  ·
    refine ⟨69439916558602505584484507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46293277705735003722989671 69439916558602505584484507)
    ·
      refine ⟨104159874837903758376726761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69439916558602505584484507 104159874837903758376726761)
      ·
        refine ⟨78119906128427818782545071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104159874837903758376726761 78119906128427818782545071)
        ·
          refine ⟨117179859192641728173817607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78119906128427818782545071 117179859192641728173817607)
          ·
            refine ⟨175769788788962592260726411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117179859192641728173817607 175769788788962592260726411)
            ·
              refine ⟨263654683183443888391089617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175769788788962592260726411 263654683183443888391089617)
              ·
                refine ⟨197741012387582916293317213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263654683183443888391089617 197741012387582916293317213)
                ·
                  refine ⟨74152879645343593609993955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197741012387582916293317213 74152879645343593609993955)
                  ·
                    refine ⟨111229319468015390414990933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74152879645343593609993955 111229319468015390414990933)
                    ·
                      refine ⟨1303468587515805356425675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 111229319468015390414990933 1303468587515805356425675)
                      ·
                        rfl

theorem cell23_2538496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_2538496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538496 prefixEnd_2538496 := by exact prefixLift 2538496
  have htrace : WordTrace (prefixWord ++ tailWord_2538496) baseStart_2538496 baseEnd_2538496 := by
    simpa [prefixWord, tailWord_2538496, baseEnd_2538496] using wordTrace_append hprefix tailTrace_2538496
  have hstable : (prefixWord ++ tailWord_2538496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538496).length < 2 ^ (prefixWord ++ tailWord_2538496).sum := by decide
  have hdescent : baseEnd_2538496 < baseStart_2538496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538560 : List Nat := [2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 4]
def baseStart_2538560 : Nat := 118140960795 + 2538560 * 2 ^ 59
def prefixEnd_2538560 : Nat := 4983230072969 + 3 ^ 40 * 2538560 * 2
def baseEnd_2538560 : Nat := 1303501450277693106025381

theorem tailTrace_2538560 : CollatzResearch.WordTrace tailWord_2538560 prefixEnd_2538560 1303501450277693106025381 := by
  unfold tailWord_2538560
  simp only [CollatzResearch.WordTrace]
  refine ⟨46294444841619073188154567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61725926455492097584206089 46294444841619073188154567)
  ·
    refine ⟨69441667262428609782231851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46294444841619073188154567 69441667262428609782231851)
    ·
      refine ⟨104162500893642914673347777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69441667262428609782231851 104162500893642914673347777)
      ·
        refine ⟨78121875670232186005010833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104162500893642914673347777 78121875670232186005010833)
        ·
          refine ⟨58591406752674139503758125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78121875670232186005010833 58591406752674139503758125)
          ·
            refine ⟨21971777532252802313909297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58591406752674139503758125 21971777532252802313909297)
            ·
              refine ⟨16478833149189601735431973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21971777532252802313909297 16478833149189601735431973)
              ·
                refine ⟨3089781215473050325393495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16478833149189601735431973 3089781215473050325393495)
                ·
                  refine ⟨4634671823209575488090243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3089781215473050325393495 4634671823209575488090243)
                  ·
                    refine ⟨6952007734814363232135365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4634671823209575488090243 6952007734814363232135365)
                    ·
                      refine ⟨1303501450277693106025381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6952007734814363232135365 1303501450277693106025381)
                      ·
                        rfl

theorem cell23_2538560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_2538560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538560 prefixEnd_2538560 := by exact prefixLift 2538560
  have htrace : WordTrace (prefixWord ++ tailWord_2538560) baseStart_2538560 baseEnd_2538560 := by
    simpa [prefixWord, tailWord_2538560, baseEnd_2538560] using wordTrace_append hprefix tailTrace_2538560
  have hstable : (prefixWord ++ tailWord_2538560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538560).length < 2 ^ (prefixWord ++ tailWord_2538560).sum := by decide
  have hdescent : baseEnd_2538560 < baseStart_2538560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538577 : List Nat := [1, 2, 2, 1, 3, 1, 6, 1, 1, 1, 4]
def baseStart_2538577 : Nat := 118140960795 + 2538577 * 2 ^ 59
def prefixEnd_2538577 : Nat := 4983230072969 + 3 ^ 40 * 2538577 * 2
def baseEnd_2538577 : Nat := 1303510179448819539512803

theorem tailTrace_2538577 : CollatzResearch.WordTrace tailWord_2538577 prefixEnd_2538577 1303510179448819539512803 := by
  unfold tailWord_2538577
  simp only [CollatzResearch.WordTrace]
  refine ⟨92589509724176558279677985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61726339816117705519785323 92589509724176558279677985)
  ·
    refine ⟨69442132293132418709758489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92589509724176558279677985 69442132293132418709758489)
    ·
      refine ⟨52081599219849314032318867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69442132293132418709758489 52081599219849314032318867)
      ·
        refine ⟨78122398829773971048478301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52081599219849314032318867 78122398829773971048478301)
        ·
          refine ⟨29295899561165239143179363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78122398829773971048478301 29295899561165239143179363)
          ·
            refine ⟨43943849341747858714769045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29295899561165239143179363 43943849341747858714769045)
            ·
              refine ⟨2059867937894430877254799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43943849341747858714769045 2059867937894430877254799)
              ·
                refine ⟨3089801906841646315882199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059867937894430877254799 3089801906841646315882199)
                ·
                  refine ⟨4634702860262469473823299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3089801906841646315882199 4634702860262469473823299)
                  ·
                    refine ⟨6952054290393704210734949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4634702860262469473823299 6952054290393704210734949)
                    ·
                      refine ⟨1303510179448819539512803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6952054290393704210734949 1303510179448819539512803)
                      ·
                        rfl

theorem cell23_2538577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 1, 1, 4].length) (baseStart_2538577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538577 prefixEnd_2538577 := by exact prefixLift 2538577
  have htrace : WordTrace (prefixWord ++ tailWord_2538577) baseStart_2538577 baseEnd_2538577 := by
    simpa [prefixWord, tailWord_2538577, baseEnd_2538577] using wordTrace_append hprefix tailTrace_2538577
  have hstable : (prefixWord ++ tailWord_2538577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538577).length < 2 ^ (prefixWord ++ tailWord_2538577).sum := by decide
  have hdescent : baseEnd_2538577 < baseStart_2538577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538614 : List Nat := [5, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_2538614 : Nat := 118140960795 + 2538614 * 2 ^ 59
def prefixEnd_2538614 : Nat := 4983230072969 + 3 ^ 40 * 2538614 * 2
def baseEnd_2538614 : Nat := 1303529178233035894750133

theorem tailTrace_2538614 : CollatzResearch.WordTrace tailWord_2538614 prefixEnd_2538614 1303529178233035894750133 := by
  unfold tailWord_2538614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5786928701565157099923431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61727239483361675732516597 5786928701565157099923431)
  ·
    refine ⟨8680393052347735649885147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5786928701565157099923431 8680393052347735649885147)
    ·
      refine ⟨13020589578521603474827721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8680393052347735649885147 13020589578521603474827721)
      ·
        refine ⟨9765442183891202606120791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13020589578521603474827721 9765442183891202606120791)
        ·
          refine ⟨14648163275836803909181187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9765442183891202606120791 14648163275836803909181187)
          ·
            refine ⟨21972244913755205863771781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14648163275836803909181187 21972244913755205863771781)
            ·
              refine ⟨4119795921329101099457209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21972244913755205863771781 4119795921329101099457209)
              ·
                refine ⟨3089846940996825824592907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4119795921329101099457209 3089846940996825824592907)
                ·
                  refine ⟨4634770411495238736889361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3089846940996825824592907 4634770411495238736889361)
                  ·
                    refine ⟨3476077808621429052667021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4634770411495238736889361 3476077808621429052667021)
                    ·
                      refine ⟨1303529178233035894750133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3476077808621429052667021 1303529178233035894750133)
                      ·
                        rfl

theorem cell23_2538614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_2538614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538614 prefixEnd_2538614 := by exact prefixLift 2538614
  have htrace : WordTrace (prefixWord ++ tailWord_2538614) baseStart_2538614 baseEnd_2538614 := by
    simpa [prefixWord, tailWord_2538614, baseEnd_2538614] using wordTrace_append hprefix tailTrace_2538614
  have hstable : (prefixWord ++ tailWord_2538614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538614).length < 2 ^ (prefixWord ++ tailWord_2538614).sum := by decide
  have hdescent : baseEnd_2538614 < baseStart_2538614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538617 : List Nat := [1, 2, 1, 3, 5, 2, 2, 7]
def baseStart_2538617 : Nat := 118140960795 + 2538617 * 2 ^ 59
def prefixEnd_2538617 : Nat := 4983230072969 + 3 ^ 40 * 2538617 * 2
def baseEnd_2538617 : Nat := 48278915506481458630097

theorem tailTrace_2538617 : CollatzResearch.WordTrace tailWord_2538617 prefixEnd_2538617 48278915506481458630097 := by
  unfold tailWord_2538617
  simp only [CollatzResearch.WordTrace]
  refine ⟨92590968644031645111134105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61727312429354430074089403 92590968644031645111134105)
  ·
    refine ⟨69443226483023733833350579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92590968644031645111134105 69443226483023733833350579)
    ·
      refine ⟨104164839724535600750025869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69443226483023733833350579 104164839724535600750025869)
      ·
        refine ⟨39061814896700850281259701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104164839724535600750025869 39061814896700850281259701)
        ·
          refine ⟨3662045146565704713868097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39061814896700850281259701 3662045146565704713868097)
          ·
            refine ⟨2746533859924278535401073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3662045146565704713868097 2746533859924278535401073)
            ·
              refine ⟨2059900394943208901550805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2746533859924278535401073 2059900394943208901550805)
              ·
                refine ⟨48278915506481458630097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2059900394943208901550805 48278915506481458630097)
                ·
                  rfl

theorem cell23_2538617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 7].length) (baseStart_2538617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538617 prefixEnd_2538617 := by exact prefixLift 2538617
  have htrace : WordTrace (prefixWord ++ tailWord_2538617) baseStart_2538617 baseEnd_2538617 := by
    simpa [prefixWord, tailWord_2538617, baseEnd_2538617] using wordTrace_append hprefix tailTrace_2538617
  have hstable : (prefixWord ++ tailWord_2538617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538617).length < 2 ^ (prefixWord ++ tailWord_2538617).sum := by decide
  have hdescent : baseEnd_2538617 < baseStart_2538617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538622 : List Nat := [4, 2, 4, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_2538622 : Nat := 118140960795 + 2538622 * 2 ^ 59
def prefixEnd_2538622 : Nat := 4983230072969 + 3 ^ 40 * 2538622 * 2
def baseEnd_2538622 : Nat := 1303533286078271863450097

theorem tailTrace_2538622 : CollatzResearch.WordTrace tailWord_2538622 prefixEnd_2538622 1303533286078271863450097 := by
  unfold tailWord_2538622
  simp only [CollatzResearch.WordTrace]
  refine ⟨11573893876126691370633265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61727434006009020643377413 11573893876126691370633265)
  ·
    refine ⟨8680420407095018527974949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11573893876126691370633265 8680420407095018527974949)
    ·
      refine ⟨1627578826330315973995303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8680420407095018527974949 1627578826330315973995303)
      ·
        refine ⟨2441368239495473960992955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1627578826330315973995303 2441368239495473960992955)
        ·
          refine ⟨3662052359243210941489433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2441368239495473960992955 3662052359243210941489433)
          ·
            refine ⟨2746539269432408206117075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3662052359243210941489433 2746539269432408206117075)
            ·
              refine ⟨4119808904148612309175613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746539269432408206117075 4119808904148612309175613)
              ·
                refine ⟨1544928339055729615940855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4119808904148612309175613 1544928339055729615940855)
                ·
                  refine ⟨2317392508583594423911283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544928339055729615940855 2317392508583594423911283)
                  ·
                    refine ⟨3476088762875391635866925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2317392508583594423911283 3476088762875391635866925)
                    ·
                      refine ⟨1303533286078271863450097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3476088762875391635866925 1303533286078271863450097)
                      ·
                        rfl

theorem cell23_2538622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_2538622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538622 prefixEnd_2538622 := by exact prefixLift 2538622
  have htrace : WordTrace (prefixWord ++ tailWord_2538622) baseStart_2538622 baseEnd_2538622 := by
    simpa [prefixWord, tailWord_2538622, baseEnd_2538622] using wordTrace_append hprefix tailTrace_2538622
  have hstable : (prefixWord ++ tailWord_2538622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538622).length < 2 ^ (prefixWord ++ tailWord_2538622).sum := by decide
  have hdescent : baseEnd_2538622 < baseStart_2538622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538628 : List Nat := [2, 3, 2, 1, 2, 4, 1, 3, 1, 2, 2]
def baseStart_2538628 : Nat := 118140960795 + 2538628 * 2 ^ 59
def prefixEnd_2538628 : Nat := 4983230072969 + 3 ^ 40 * 2538628 * 2
def baseEnd_2538628 : Nat := 1303536366962198839975069

theorem tailTrace_2538628 : CollatzResearch.WordTrace tailWord_2538628 prefixEnd_2538628 1303536366962198839975069 := by
  unfold tailWord_2538628
  simp only [CollatzResearch.WordTrace]
  refine ⟨46295684923495896994892269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61727579897994529326523025 46295684923495896994892269)
  ·
    refine ⟨17360881846310961373084601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46295684923495896994892269 17360881846310961373084601)
    ·
      refine ⟨13020661384733221029813451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17360881846310961373084601 13020661384733221029813451)
      ·
        refine ⟨19530992077099831544720177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13020661384733221029813451 19530992077099831544720177)
        ·
          refine ⟨14648244057824873658540133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19530992077099831544720177 14648244057824873658540133)
          ·
            refine ⟨2746545760842163810976275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14648244057824873658540133 2746545760842163810976275)
            ·
              refine ⟨4119818641263245716464413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746545760842163810976275 4119818641263245716464413)
              ·
                refine ⟨1544931990473717143674155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4119818641263245716464413 1544931990473717143674155)
                ·
                  refine ⟨2317397985710575715511233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544931990473717143674155 2317397985710575715511233)
                  ·
                    refine ⟨1738048489282931786633425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2317397985710575715511233 1738048489282931786633425)
                    ·
                      refine ⟨1303536366962198839975069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738048489282931786633425 1303536366962198839975069)
                      ·
                        rfl

theorem cell23_2538628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_2538628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538628 prefixEnd_2538628 := by exact prefixLift 2538628
  have htrace : WordTrace (prefixWord ++ tailWord_2538628) baseStart_2538628 baseEnd_2538628 := by
    simpa [prefixWord, tailWord_2538628, baseEnd_2538628] using wordTrace_append hprefix tailTrace_2538628
  have hstable : (prefixWord ++ tailWord_2538628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538628).length < 2 ^ (prefixWord ++ tailWord_2538628).sum := by decide
  have hdescent : baseEnd_2538628 < baseStart_2538628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538643 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 4, 6]
def baseStart_2538643 : Nat := 118140960795 + 2538643 * 2 ^ 59
def prefixEnd_2538643 : Nat := 4983230072969 + 3 ^ 40 * 2538643 * 2
def baseEnd_2538643 : Nat := 434514689724005427095833

theorem tailTrace_2538643 : CollatzResearch.WordTrace tailWord_2538643 prefixEnd_2538643 434514689724005427095833 := by
  unfold tailWord_2538643
  simp only [CollatzResearch.WordTrace]
  refine ⟨92591916941937451551580583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61727944627958301034387055 92591916941937451551580583)
  ·
    refine ⟨138887875412906177327370875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92591916941937451551580583 138887875412906177327370875)
    ·
      refine ⟨208331813119359265991056313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138887875412906177327370875 208331813119359265991056313)
      ·
        refine ⟨156248859839519449493292235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208331813119359265991056313 156248859839519449493292235)
        ·
          refine ⟨234373289759279174239938353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156248859839519449493292235 234373289759279174239938353)
          ·
            refine ⟨175779967319459380679953765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234373289759279174239938353 175779967319459380679953765)
            ·
              refine ⟨32958743872398633877491331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 175779967319459380679953765 32958743872398633877491331)
              ·
                refine ⟨49438115808597950816236997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32958743872398633877491331 49438115808597950816236997)
                ·
                  refine ⟨9269646714112115778044437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49438115808597950816236997 9269646714112115778044437)
                  ·
                    refine ⟨434514689724005427095833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9269646714112115778044437 434514689724005427095833)
                    ·
                      rfl

theorem cell23_2538643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 6].length) (baseStart_2538643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538643 prefixEnd_2538643 := by exact prefixLift 2538643
  have htrace : WordTrace (prefixWord ++ tailWord_2538643) baseStart_2538643 baseEnd_2538643 := by
    simpa [prefixWord, tailWord_2538643, baseEnd_2538643] using wordTrace_append hprefix tailTrace_2538643
  have hstable : (prefixWord ++ tailWord_2538643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538643).length < 2 ^ (prefixWord ++ tailWord_2538643).sum := by decide
  have hdescent : baseEnd_2538643 < baseStart_2538643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538661 : List Nat := [1, 3, 1, 2, 1, 6, 2, 1, 2, 1, 3]
def baseStart_2538661 : Nat := 118140960795 + 2538661 * 2 ^ 59
def prefixEnd_2538661 : Nat := 4983230072969 + 3 ^ 40 * 2538661 * 2
def baseEnd_2538661 : Nat := 1303553311823797210862417

theorem tailTrace_2538661 : CollatzResearch.WordTrace tailWord_2538661 prefixEnd_2538661 1303553311823797210862417 := by
  unfold tailWord_2538661
  simp only [CollatzResearch.WordTrace]
  refine ⟨92592573455872240625735837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61728382303914827083823891 92592573455872240625735837)
  ·
    refine ⟨34722215045952090234650939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92592573455872240625735837 34722215045952090234650939)
    ·
      refine ⟨52083322568928135351976409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34722215045952090234650939 52083322568928135351976409)
      ·
        refine ⟨39062491926696101513982307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52083322568928135351976409 39062491926696101513982307)
        ·
          refine ⟨58593737890044152270973461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39062491926696101513982307 58593737890044152270973461)
          ·
            refine ⟨2746581463595819637701881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58593737890044152270973461 2746581463595819637701881)
            ·
              refine ⟨2059936097696864728276411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2746581463595819637701881 2059936097696864728276411)
              ·
                refine ⟨3089904146545297092414617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059936097696864728276411 3089904146545297092414617)
                ·
                  refine ⟨2317428109908972819310963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3089904146545297092414617 2317428109908972819310963)
                  ·
                    refine ⟨3476142164863459228966445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2317428109908972819310963 3476142164863459228966445)
                    ·
                      refine ⟨1303553311823797210862417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3476142164863459228966445 1303553311823797210862417)
                      ·
                        rfl

theorem cell23_2538661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_2538661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538661 prefixEnd_2538661 := by exact prefixLift 2538661
  have htrace : WordTrace (prefixWord ++ tailWord_2538661) baseStart_2538661 baseEnd_2538661 := by
    simpa [prefixWord, tailWord_2538661, baseEnd_2538661] using wordTrace_append hprefix tailTrace_2538661
  have hstable : (prefixWord ++ tailWord_2538661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538661).length < 2 ^ (prefixWord ++ tailWord_2538661).sum := by decide
  have hdescent : baseEnd_2538661 < baseStart_2538661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538683 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 7]
def baseStart_2538683 : Nat := 118140960795 + 2538683 * 2 ^ 59
def prefixEnd_2538683 : Nat := 4983230072969 + 3 ^ 40 * 2538683 * 2
def baseEnd_2538683 : Nat := 1303564608398196124787315

theorem tailTrace_2538683 : CollatzResearch.WordTrace tailWord_2538683 prefixEnd_2538683 1303564608398196124787315 := by
  unfold tailWord_2538683
  simp only [CollatzResearch.WordTrace]
  refine ⟨92593375861792538383036703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61728917241195025588691135 92593375861792538383036703)
  ·
    refine ⟨138890063792688807574555055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92593375861792538383036703 138890063792688807574555055)
    ·
      refine ⟨208335095689033211361832583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138890063792688807574555055 208335095689033211361832583)
      ·
        refine ⟨312502643533549817042748875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208335095689033211361832583 312502643533549817042748875)
        ·
          refine ⟨468753965300324725564123313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312502643533549817042748875 468753965300324725564123313)
          ·
            refine ⟨351565473975243544173092485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468753965300324725564123313 351565473975243544173092485)
            ·
              refine ⟨65918526370358164532454841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 351565473975243544173092485 65918526370358164532454841)
              ·
                refine ⟨49438894777768623399341131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65918526370358164532454841 49438894777768623399341131)
                ·
                  refine ⟨74158342166652935099011697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49438894777768623399341131 74158342166652935099011697)
                  ·
                    refine ⟨55618756624989701324258773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74158342166652935099011697 55618756624989701324258773)
                    ·
                      refine ⟨1303564608398196124787315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55618756624989701324258773 1303564608398196124787315)
                      ·
                        rfl

theorem cell23_2538683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_2538683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538683 prefixEnd_2538683 := by exact prefixLift 2538683
  have htrace : WordTrace (prefixWord ++ tailWord_2538683) baseStart_2538683 baseEnd_2538683 := by
    simpa [prefixWord, tailWord_2538683, baseEnd_2538683] using wordTrace_append hprefix tailTrace_2538683
  have hstable : (prefixWord ++ tailWord_2538683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538683).length < 2 ^ (prefixWord ++ tailWord_2538683).sum := by decide
  have hdescent : baseEnd_2538683 < baseStart_2538683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538684 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 1, 4, 2]
def baseStart_2538684 : Nat := 118140960795 + 2538684 * 2 ^ 59
def prefixEnd_2538684 : Nat := 4983230072969 + 3 ^ 40 * 2538684 * 2
def baseEnd_2538684 : Nat := 1303565121878850620874811

theorem tailTrace_2538684 : CollatzResearch.WordTrace tailWord_2538684 prefixEnd_2538684 1303565121878850620874811 := by
  unfold tailWord_2538684
  simp only [CollatzResearch.WordTrace]
  refine ⟨46296706167394457776911553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61728941556525943702548737 46296706167394457776911553)
  ·
    refine ⟨34722529625545843332683665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46296706167394457776911553 34722529625545843332683665)
    ·
      refine ⟨26041897219159382499512749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34722529625545843332683665 26041897219159382499512749)
      ·
        refine ⟨9765711457184768437317281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26041897219159382499512749 9765711457184768437317281)
        ·
          refine ⟨7324283592888576327987961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9765711457184768437317281 7324283592888576327987961)
          ·
            refine ⟨5493212694666432245990971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7324283592888576327987961 5493212694666432245990971)
            ·
              refine ⟨8239819041999648368986457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5493212694666432245990971 8239819041999648368986457)
              ·
                refine ⟨6179864281499736276739843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8239819041999648368986457 6179864281499736276739843)
                ·
                  refine ⟨9269796422249604415109765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6179864281499736276739843 9269796422249604415109765)
                  ·
                    refine ⟨1738086829171800827833081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9269796422249604415109765 1738086829171800827833081)
                    ·
                      refine ⟨1303565121878850620874811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738086829171800827833081 1303565121878850620874811)
                      ·
                        rfl

theorem cell23_2538684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_2538684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538684 prefixEnd_2538684 := by exact prefixLift 2538684
  have htrace : WordTrace (prefixWord ++ tailWord_2538684) baseStart_2538684 baseEnd_2538684 := by
    simpa [prefixWord, tailWord_2538684, baseEnd_2538684] using wordTrace_append hprefix tailTrace_2538684
  have hstable : (prefixWord ++ tailWord_2538684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538684).length < 2 ^ (prefixWord ++ tailWord_2538684).sum := by decide
  have hdescent : baseEnd_2538684 < baseStart_2538684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538757 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 4, 4, 2]
def baseStart_2538757 : Nat := 118140960795 + 2538757 * 2 ^ 59
def prefixEnd_2538757 : Nat := 4983230072969 + 3 ^ 40 * 2538757 * 2
def baseEnd_2538757 : Nat := 1303602605966628835261975

theorem tailTrace_2538757 : CollatzResearch.WordTrace tailWord_2538757 prefixEnd_2538757 1303602605966628835261975 := by
  unfold tailWord_2538757
  simp only [CollatzResearch.WordTrace]
  refine ⟨92596074863524449021230525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61730716575682966014153683 92596074863524449021230525)
  ·
    refine ⟨34723528073821668382961447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92596074863524449021230525 34723528073821668382961447)
    ·
      refine ⟨52085292110732502574442171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34723528073821668382961447 52085292110732502574442171)
      ·
        refine ⟨78127938166098753861663257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52085292110732502574442171 78127938166098753861663257)
        ·
          refine ⟨58595953624574065396247443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78127938166098753861663257 58595953624574065396247443)
          ·
            refine ⟨87893930436861098094371165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58595953624574065396247443 87893930436861098094371165)
            ·
              refine ⟨32960223913822911785389187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87893930436861098094371165 32960223913822911785389187)
              ·
                refine ⟨49440335870734367678083781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32960223913822911785389187 49440335870734367678083781)
                ·
                  refine ⟨9270062975762693939640709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49440335870734367678083781 9270062975762693939640709)
                  ·
                    refine ⟨1738136807955505113682633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9270062975762693939640709 1738136807955505113682633)
                    ·
                      refine ⟨1303602605966628835261975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738136807955505113682633 1303602605966628835261975)
                      ·
                        rfl

theorem cell23_2538757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 4, 2].length) (baseStart_2538757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538757 prefixEnd_2538757 := by exact prefixLift 2538757
  have htrace : WordTrace (prefixWord ++ tailWord_2538757) baseStart_2538757 baseEnd_2538757 := by
    simpa [prefixWord, tailWord_2538757, baseEnd_2538757] using wordTrace_append hprefix tailTrace_2538757
  have hstable : (prefixWord ++ tailWord_2538757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538757).length < 2 ^ (prefixWord ++ tailWord_2538757).sum := by decide
  have hdescent : baseEnd_2538757 < baseStart_2538757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538794 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2538794 : Nat := 118140960795 + 2538794 * 2 ^ 59
def prefixEnd_2538794 : Nat := 4983230072969 + 3 ^ 40 * 2538794 * 2
def baseEnd_2538794 : Nat := 1303621604750845190499305

theorem tailTrace_2538794 : CollatzResearch.WordTrace tailWord_2538794 prefixEnd_2538794 1303621604750845190499305 := by
  unfold tailWord_2538794
  simp only [CollatzResearch.WordTrace]
  refine ⟨23149356091097601085081859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61731616242926936226884957 23149356091097601085081859)
  ·
    refine ⟨34724034136646401627622789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23149356091097601085081859 34724034136646401627622789)
    ·
      refine ⟨6510756400621200305179273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34724034136646401627622789 6510756400621200305179273)
      ·
        refine ⟨4883067300465900228884455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6510756400621200305179273 4883067300465900228884455)
        ·
          refine ⟨7324600950698850343326683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4883067300465900228884455 7324600950698850343326683)
          ·
            refine ⟨10986901426048275514990025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7324600950698850343326683 10986901426048275514990025)
            ·
              refine ⟨8240176069536206636242519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10986901426048275514990025 8240176069536206636242519)
              ·
                refine ⟨12360264104304309954363779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8240176069536206636242519 12360264104304309954363779)
                ·
                  refine ⟨18540396156456464931545669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12360264104304309954363779 18540396156456464931545669)
                  ·
                    refine ⟨3476324279335587174664813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18540396156456464931545669 3476324279335587174664813)
                    ·
                      refine ⟨1303621604750845190499305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3476324279335587174664813 1303621604750845190499305)
                      ·
                        rfl

theorem cell23_2538794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2538794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538794 prefixEnd_2538794 := by exact prefixLift 2538794
  have htrace : WordTrace (prefixWord ++ tailWord_2538794) baseStart_2538794 baseEnd_2538794 := by
    simpa [prefixWord, tailWord_2538794, baseEnd_2538794] using wordTrace_append hprefix tailTrace_2538794
  have hstable : (prefixWord ++ tailWord_2538794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538794).length < 2 ^ (prefixWord ++ tailWord_2538794).sum := by decide
  have hdescent : baseEnd_2538794 < baseStart_2538794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538801 : List Nat := [1, 2, 2, 3, 3, 1, 3, 3, 1, 4]
def baseStart_2538801 : Nat := 118140960795 + 2538801 * 2 ^ 59
def prefixEnd_2538801 : Nat := 4983230072969 + 3 ^ 40 * 2538801 * 2
def baseEnd_2538801 : Nat := 434541733038475554370591

theorem tailTrace_2538801 : CollatzResearch.WordTrace tailWord_2538801 prefixEnd_2538801 434541733038475554370591 := by
  unfold tailWord_2538801
  simp only [CollatzResearch.WordTrace]
  refine ⟨92597679675365044535832257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61731786450243363023888171 92597679675365044535832257)
  ·
    refine ⟨69448259756523783401874193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92597679675365044535832257 69448259756523783401874193)
    ·
      refine ⟨52086194817392837551405645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69448259756523783401874193 52086194817392837551405645)
      ·
        refine ⟨19532323056522314081777117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52086194817392837551405645 19532323056522314081777117)
        ·
          refine ⟨7324621146195867780666419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19532323056522314081777117 7324621146195867780666419)
          ·
            refine ⟨10986931719293801670999629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7324621146195867780666419 10986931719293801670999629)
            ·
              refine ⟨4120099394735175626624861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10986931719293801670999629 4120099394735175626624861)
              ·
                refine ⟨1545037273025690859984323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4120099394735175626624861 1545037273025690859984323)
                ·
                  refine ⟨2317555909538536289976485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545037273025690859984323 2317555909538536289976485)
                  ·
                    refine ⟨434541733038475554370591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2317555909538536289976485 434541733038475554370591)
                    ·
                      rfl

theorem cell23_2538801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_2538801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538801 prefixEnd_2538801 := by exact prefixLift 2538801
  have htrace : WordTrace (prefixWord ++ tailWord_2538801) baseStart_2538801 baseEnd_2538801 := by
    simpa [prefixWord, tailWord_2538801, baseEnd_2538801] using wordTrace_append hprefix tailTrace_2538801
  have hstable : (prefixWord ++ tailWord_2538801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538801).length < 2 ^ (prefixWord ++ tailWord_2538801).sum := by decide
  have hdescent : baseEnd_2538801 < baseStart_2538801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538834 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_2538834 : Nat := 118140960795 + 2538834 * 2 ^ 59
def prefixEnd_2538834 : Nat := 4983230072969 + 3 ^ 40 * 2538834 * 2
def baseEnd_2538834 : Nat := 1303642143977025033999121

theorem tailTrace_2538834 : CollatzResearch.WordTrace tailWord_2538834 prefixEnd_2538834 1303642143977025033999121 := by
  unfold tailWord_2538834
  simp only [CollatzResearch.WordTrace]
  refine ⟨23149720821061372792945889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61732588856163660781189037 23149720821061372792945889)
  ·
    refine ⟨17362290615796029594709417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23149720821061372792945889 17362290615796029594709417)
    ·
      refine ⟨13021717961847022196032063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17362290615796029594709417 13021717961847022196032063)
      ·
        refine ⟨19532576942770533294048095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13021717961847022196032063 19532576942770533294048095)
        ·
          refine ⟨29298865414155799941072143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19532576942770533294048095 29298865414155799941072143)
          ·
            refine ⟨43948298121233699911608215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29298865414155799941072143 43948298121233699911608215)
            ·
              refine ⟨65922447181850549867412323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43948298121233699911608215 65922447181850549867412323)
              ·
                refine ⟨98883670772775824801118485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65922447181850549867412323 98883670772775824801118485)
                ·
                  refine ⟨4635172067473866787552429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98883670772775824801118485 4635172067473866787552429)
                  ·
                    refine ⟨1738189525302700045332161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4635172067473866787552429 1738189525302700045332161)
                    ·
                      refine ⟨1303642143977025033999121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738189525302700045332161 1303642143977025033999121)
                      ·
                        rfl

theorem cell23_2538834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_2538834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538834 prefixEnd_2538834 := by exact prefixLift 2538834
  have htrace : WordTrace (prefixWord ++ tailWord_2538834) baseStart_2538834 baseEnd_2538834 := by
    simpa [prefixWord, tailWord_2538834, baseEnd_2538834] using wordTrace_append hprefix tailTrace_2538834
  have hstable : (prefixWord ++ tailWord_2538834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538834).length < 2 ^ (prefixWord ++ tailWord_2538834).sum := by decide
  have hdescent : baseEnd_2538834 < baseStart_2538834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538845 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2538845 : Nat := 118140960795 + 2538845 * 2 ^ 59
def prefixEnd_2538845 : Nat := 4983230072969 + 3 ^ 40 * 2538845 * 2
def baseEnd_2538845 : Nat := 1303647792264224490961571

theorem tailTrace_2538845 : CollatzResearch.WordTrace tailWord_2538845 prefixEnd_2538845 1303647792264224490961571 := by
  unfold tailWord_2538845
  simp only [CollatzResearch.WordTrace]
  refine ⟨92599284487205640050433989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61732856324803760033622659 92599284487205640050433989)
  ·
    refine ⟨17362365841351057509456373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92599284487205640050433989 17362365841351057509456373)
    ·
      refine ⟨1627721797626661641511535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17362365841351057509456373 1627721797626661641511535)
      ·
        refine ⟨2441582696439992462267303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1627721797626661641511535 2441582696439992462267303)
        ·
          refine ⟨3662374044659988693400955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2441582696439992462267303 3662374044659988693400955)
          ·
            refine ⟨5493561066989983040101433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3662374044659988693400955 5493561066989983040101433)
            ·
              refine ⟨4120170800242487280076075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5493561066989983040101433 4120170800242487280076075)
              ·
                refine ⟨6180256200363730920114113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120170800242487280076075 6180256200363730920114113)
                ·
                  refine ⟨4635192150272798190085585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6180256200363730920114113 4635192150272798190085585)
                  ·
                    refine ⟨3476394112704598642564189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4635192150272798190085585 3476394112704598642564189)
                    ·
                      refine ⟨1303647792264224490961571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3476394112704598642564189 1303647792264224490961571)
                      ·
                        rfl

theorem cell23_2538845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2538845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538845 prefixEnd_2538845 := by exact prefixLift 2538845
  have htrace : WordTrace (prefixWord ++ tailWord_2538845) baseStart_2538845 baseEnd_2538845 := by
    simpa [prefixWord, tailWord_2538845, baseEnd_2538845] using wordTrace_append hprefix tailTrace_2538845
  have hstable : (prefixWord ++ tailWord_2538845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538845).length < 2 ^ (prefixWord ++ tailWord_2538845).sum := by decide
  have hdescent : baseEnd_2538845 < baseStart_2538845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538851 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 2, 3, 2]
def baseStart_2538851 : Nat := 118140960795 + 2538851 * 2 ^ 59
def prefixEnd_2538851 : Nat := 4983230072969 + 3 ^ 40 * 2538851 * 2
def baseEnd_2538851 : Nat := 1303650873148151467486543

theorem tailTrace_2538851 : CollatzResearch.WordTrace tailWord_2538851 prefixEnd_2538851 1303650873148151467486543 := by
  unfold tailWord_2538851
  simp only [CollatzResearch.WordTrace]
  refine ⟨92599503325183903075152407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61733002216789268716768271 92599503325183903075152407)
  ·
    refine ⟨138899254987775854612728611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92599503325183903075152407 138899254987775854612728611)
    ·
      refine ⟨208348882481663781919092917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138899254987775854612728611 208348882481663781919092917)
      ·
        refine ⟨19532707732655979554914961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 208348882481663781919092917 19532707732655979554914961)
        ·
          refine ⟨14649530799491984666186221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19532707732655979554914961 14649530799491984666186221)
          ·
            refine ⟨5493574049809494249819833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14649530799491984666186221 5493574049809494249819833)
            ·
              refine ⟨4120180537357120687364875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5493574049809494249819833 4120180537357120687364875)
              ·
                refine ⟨6180270806035681031047313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120180537357120687364875 6180270806035681031047313)
                ·
                  refine ⟨4635203104526760773285485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6180270806035681031047313 4635203104526760773285485)
                  ·
                    refine ⟨1738201164197535289982057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4635203104526760773285485 1738201164197535289982057)
                    ·
                      refine ⟨1303650873148151467486543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738201164197535289982057 1303650873148151467486543)
                      ·
                        rfl

theorem cell23_2538851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_2538851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538851 prefixEnd_2538851 := by exact prefixLift 2538851
  have htrace : WordTrace (prefixWord ++ tailWord_2538851) baseStart_2538851 baseEnd_2538851 := by
    simpa [prefixWord, tailWord_2538851, baseEnd_2538851] using wordTrace_append hprefix tailTrace_2538851
  have hstable : (prefixWord ++ tailWord_2538851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538851).length < 2 ^ (prefixWord ++ tailWord_2538851).sum := by decide
  have hdescent : baseEnd_2538851 < baseStart_2538851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538857 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 4, 4]
def baseStart_2538857 : Nat := 118140960795 + 2538857 * 2 ^ 59
def prefixEnd_2538857 : Nat := 4983230072969 + 3 ^ 40 * 2538857 * 2
def baseEnd_2538857 : Nat := 434551318010692814670505

theorem tailTrace_2538857 : CollatzResearch.WordTrace tailWord_2538857 prefixEnd_2538857 434551318010692814670505 := by
  unfold tailWord_2538857
  simp only [CollatzResearch.WordTrace]
  refine ⟨92599722163162166099870825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61733148108774777399913883 92599722163162166099870825)
  ·
    refine ⟨69449791622371624574903119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92599722163162166099870825 69449791622371624574903119)
    ·
      refine ⟨104174687433557436862354679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69449791622371624574903119 104174687433557436862354679)
      ·
        refine ⟨156262031150336155293532019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104174687433557436862354679 156262031150336155293532019)
        ·
          refine ⟨234393046725504232940298029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156262031150336155293532019 234393046725504232940298029)
          ·
            refine ⟨87897392522064087352611761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234393046725504232940298029 87897392522064087352611761)
            ·
              refine ⟨65923044391548065514458821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87897392522064087352611761 65923044391548065514458821)
              ·
                refine ⟨12360570823415262283961029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65923044391548065514458821 12360570823415262283961029)
                ·
                  refine ⟨2317607029390361678242693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12360570823415262283961029 2317607029390361678242693)
                  ·
                    refine ⟨434551318010692814670505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2317607029390361678242693 434551318010692814670505)
                    ·
                      rfl

theorem cell23_2538857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 4].length) (baseStart_2538857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538857 prefixEnd_2538857 := by exact prefixLift 2538857
  have htrace : WordTrace (prefixWord ++ tailWord_2538857) baseStart_2538857 baseEnd_2538857 := by
    simpa [prefixWord, tailWord_2538857, baseEnd_2538857] using wordTrace_append hprefix tailTrace_2538857
  have hstable : (prefixWord ++ tailWord_2538857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538857).length < 2 ^ (prefixWord ++ tailWord_2538857).sum := by decide
  have hdescent : baseEnd_2538857 < baseStart_2538857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538861 : List Nat := [1, 5, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_2538861 : Nat := 118140960795 + 2538861 * 2 ^ 59
def prefixEnd_2538861 : Nat := 4983230072969 + 3 ^ 40 * 2538861 * 2
def baseEnd_2538861 : Nat := 434552002651565476120499

theorem tailTrace_2538861 : CollatzResearch.WordTrace tailWord_2538861 prefixEnd_2538861 434552002651565476120499 := by
  unfold tailWord_2538861
  simp only [CollatzResearch.WordTrace]
  refine ⟨92599868055147674783016437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61733245370098449855344291 92599868055147674783016437)
  ·
    refine ⟨8681237630170094510907791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92599868055147674783016437 8681237630170094510907791)
    ·
      refine ⟨13021856445255141766361687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8681237630170094510907791 13021856445255141766361687)
      ·
        refine ⟨19532784667882712649542531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13021856445255141766361687 19532784667882712649542531)
        ·
          refine ⟨29299177001824068974313797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19532784667882712649542531 29299177001824068974313797)
          ·
            refine ⟨5493595687842012932683837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29299177001824068974313797 5493595687842012932683837)
            ·
              refine ⟨2060098382940754849756439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5493595687842012932683837 2060098382940754849756439)
              ·
                refine ⟨3090147574411132274634659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060098382940754849756439 3090147574411132274634659)
                ·
                  refine ⟨4635221361616698411951989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3090147574411132274634659 4635221361616698411951989)
                  ·
                    refine ⟨434552002651565476120499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4635221361616698411951989 434552002651565476120499)
                    ·
                      rfl

theorem cell23_2538861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_2538861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538861 prefixEnd_2538861 := by exact prefixLift 2538861
  have htrace : WordTrace (prefixWord ++ tailWord_2538861) baseStart_2538861 baseEnd_2538861 := by
    simpa [prefixWord, tailWord_2538861, baseEnd_2538861] using wordTrace_append hprefix tailTrace_2538861
  have hstable : (prefixWord ++ tailWord_2538861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538861).length < 2 ^ (prefixWord ++ tailWord_2538861).sum := by decide
  have hdescent : baseEnd_2538861 < baseStart_2538861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538867 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 3]
def baseStart_2538867 : Nat := 118140960795 + 2538867 * 2 ^ 59
def prefixEnd_2538867 : Nat := 4983230072969 + 3 ^ 40 * 2538867 * 2
def baseEnd_2538867 : Nat := 1303659088838623404886469

theorem tailTrace_2538867 : CollatzResearch.WordTrace tailWord_2538867 prefixEnd_2538867 1303659088838623404886469 := by
  unfold tailWord_2538867
  simp only [CollatzResearch.WordTrace]
  refine ⟨92600086893125937807734855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61733391262083958538489903 92600086893125937807734855)
  ·
    refine ⟨138900130339688906711602283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92600086893125937807734855 138900130339688906711602283)
    ·
      refine ⟨208350195509533360067403425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138900130339688906711602283 208350195509533360067403425)
      ·
        refine ⟨156262646632150020050552569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208350195509533360067403425 156262646632150020050552569)
        ·
          refine ⟨117196984974112515037914427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156262646632150020050552569 117196984974112515037914427)
          ·
            refine ⟨175795477461168772556871641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117196984974112515037914427 175795477461168772556871641)
            ·
              refine ⟨131846608095876579417653731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175795477461168772556871641 131846608095876579417653731)
              ·
                refine ⟨197769912143814869126480597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131846608095876579417653731 197769912143814869126480597)
                ·
                  refine ⟨4635232315870660995151889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 197769912143814869126480597 4635232315870660995151889)
                  ·
                    refine ⟨3476424236902995746363917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4635232315870660995151889 3476424236902995746363917)
                    ·
                      refine ⟨1303659088838623404886469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3476424236902995746363917 1303659088838623404886469)
                      ·
                        rfl

theorem cell23_2538867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 3].length) (baseStart_2538867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538867 prefixEnd_2538867 := by exact prefixLift 2538867
  have htrace : WordTrace (prefixWord ++ tailWord_2538867) baseStart_2538867 baseEnd_2538867 := by
    simpa [prefixWord, tailWord_2538867, baseEnd_2538867] using wordTrace_append hprefix tailTrace_2538867
  have hstable : (prefixWord ++ tailWord_2538867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538867).length < 2 ^ (prefixWord ++ tailWord_2538867).sum := by decide
  have hdescent : baseEnd_2538867 < baseStart_2538867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538877 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_2538877 : Nat := 118140960795 + 2538877 * 2 ^ 59
def prefixEnd_2538877 : Nat := 4983230072969 + 3 ^ 40 * 2538877 * 2
def baseEnd_2538877 : Nat := 1303664223645168365761423

theorem tailTrace_2538877 : CollatzResearch.WordTrace tailWord_2538877 prefixEnd_2538877 1303664223645168365761423 := by
  unfold tailWord_2538877
  simp only [CollatzResearch.WordTrace]
  refine ⟨92600451623089709515598885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61733634415393139677065923 92600451623089709515598885)
  ·
    refine ⟨17362584679329320534174791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92600451623089709515598885 17362584679329320534174791)
    ·
      refine ⟨26043877018993980801262187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17362584679329320534174791 26043877018993980801262187)
      ·
        refine ⟨39065815528490971201893281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26043877018993980801262187 39065815528490971201893281)
        ·
          refine ⟨29299361646368228401419961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39065815528490971201893281 29299361646368228401419961)
          ·
            refine ⟨21974521234776171301064971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29299361646368228401419961 21974521234776171301064971)
            ·
              refine ⟨32961781852164256951597457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21974521234776171301064971 32961781852164256951597457)
              ·
                refine ⟨24721336389123192713698093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32961781852164256951597457 24721336389123192713698093)
                ·
                  refine ⟨9270501145921197267636785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24721336389123192713698093 9270501145921197267636785)
                  ·
                    refine ⟨6952875859440897950727589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9270501145921197267636785 6952875859440897950727589)
                    ·
                      refine ⟨1303664223645168365761423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6952875859440897950727589 1303664223645168365761423)
                      ·
                        rfl

theorem cell23_2538877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_2538877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538877 prefixEnd_2538877 := by exact prefixLift 2538877
  have htrace : WordTrace (prefixWord ++ tailWord_2538877) baseStart_2538877 baseEnd_2538877 := by
    simpa [prefixWord, tailWord_2538877, baseEnd_2538877] using wordTrace_append hprefix tailTrace_2538877
  have hstable : (prefixWord ++ tailWord_2538877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538877).length < 2 ^ (prefixWord ++ tailWord_2538877).sum := by decide
  have hdescent : baseEnd_2538877 < baseStart_2538877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538884 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_2538884 : Nat := 118140960795 + 2538884 * 2 ^ 59
def prefixEnd_2538884 : Nat := 4983230072969 + 3 ^ 40 * 2538884 * 2
def baseEnd_2538884 : Nat := 1303667818009749838373891

theorem tailTrace_2538884 : CollatzResearch.WordTrace tailWord_2538884 prefixEnd_2538884 1303667818009749838373891 := by
  unfold tailWord_2538884
  simp only [CollatzResearch.WordTrace]
  refine ⟨46300353467032174855551853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61733804622709566474069137 46300353467032174855551853)
  ·
    refine ⟨17362632550137065570831945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46300353467032174855551853 17362632550137065570831945)
    ·
      refine ⟨13021974412602799178123959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17362632550137065570831945 13021974412602799178123959)
      ·
        refine ⟨19532961618904198767185939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13021974412602799178123959 19532961618904198767185939)
        ·
          refine ⟨29299442428356298150778909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19532961618904198767185939 29299442428356298150778909)
          ·
            refine ⟨10987290910633611806542091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29299442428356298150778909 10987290910633611806542091)
            ·
              refine ⟨16480936365950417709813137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10987290910633611806542091 16480936365950417709813137)
              ·
                refine ⟨12360702274462813282359853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16480936365950417709813137 12360702274462813282359853)
                ·
                  refine ⟨4635263352923554980884945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12360702274462813282359853 4635263352923554980884945)
                  ·
                    refine ⟨3476447514692666235663709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4635263352923554980884945 3476447514692666235663709)
                    ·
                      refine ⟨1303667818009749838373891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3476447514692666235663709 1303667818009749838373891)
                      ·
                        rfl

theorem cell23_2538884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_2538884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538884 prefixEnd_2538884 := by exact prefixLift 2538884
  have htrace : WordTrace (prefixWord ++ tailWord_2538884) baseStart_2538884 baseEnd_2538884 := by
    simpa [prefixWord, tailWord_2538884, baseEnd_2538884] using wordTrace_append hprefix tailTrace_2538884
  have hstable : (prefixWord ++ tailWord_2538884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538884).length < 2 ^ (prefixWord ++ tailWord_2538884).sum := by decide
  have hdescent : baseEnd_2538884 < baseStart_2538884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538887 : List Nat := [1, 1, 4, 2, 2, 2, 3, 8]
def baseStart_2538887 : Nat := 118140960795 + 2538887 * 2 ^ 59
def prefixEnd_2538887 : Nat := 4983230072969 + 3 ^ 40 * 2538887 * 2
def baseEnd_2538887 : Nat := 48284050313026419505051

theorem tailTrace_2538887 : CollatzResearch.WordTrace tailWord_2538887 prefixEnd_2538887 48284050313026419505051 := by
  unfold tailWord_2538887
  simp only [CollatzResearch.WordTrace]
  refine ⟨92600816353053481223462915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61733877568702320815641943 92600816353053481223462915)
  ·
    refine ⟨138901224529580221835194373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92600816353053481223462915 138901224529580221835194373)
    ·
      refine ⟨26043979599296291594098945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 138901224529580221835194373 26043979599296291594098945)
      ·
        refine ⟨19532984699472218695574209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26043979599296291594098945 19532984699472218695574209)
        ·
          refine ⟨14649738524604164021680657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19532984699472218695574209 14649738524604164021680657)
          ·
            refine ⟨10987303893453123016260493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14649738524604164021680657 10987303893453123016260493)
            ·
              refine ⟨4120238960044921131097685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10987303893453123016260493 4120238960044921131097685)
              ·
                refine ⟨48284050313026419505051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4120238960044921131097685 48284050313026419505051)
                ·
                  rfl

theorem cell23_2538887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 8].length) (baseStart_2538887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538887 prefixEnd_2538887 := by exact prefixLift 2538887
  have htrace : WordTrace (prefixWord ++ tailWord_2538887) baseStart_2538887 baseEnd_2538887 := by
    simpa [prefixWord, tailWord_2538887, baseEnd_2538887] using wordTrace_append hprefix tailTrace_2538887
  have hstable : (prefixWord ++ tailWord_2538887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538887).length < 2 ^ (prefixWord ++ tailWord_2538887).sum := by decide
  have hdescent : baseEnd_2538887 < baseStart_2538887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538897 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 3]
def baseStart_2538897 : Nat := 118140960795 + 2538897 * 2 ^ 59
def prefixEnd_2538897 : Nat := 4983230072969 + 3 ^ 40 * 2538897 * 2
def baseEnd_2538897 : Nat := 1303674493258258287511331

theorem tailTrace_2538897 : CollatzResearch.WordTrace tailWord_2538897 prefixEnd_2538897 1303674493258258287511331 := by
  unfold tailWord_2538897
  simp only [CollatzResearch.WordTrace]
  refine ⟨92601181083017252931326945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61734120722011501954217963 92601181083017252931326945)
  ·
    refine ⟨69450885812262939698495209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92601181083017252931326945 69450885812262939698495209)
    ·
      refine ⟨52088164359197204773871407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69450885812262939698495209 52088164359197204773871407)
      ·
        refine ⟨78132246538795807160807111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52088164359197204773871407 78132246538795807160807111)
        ·
          refine ⟨117198369808193710741210667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78132246538795807160807111 117198369808193710741210667)
          ·
            refine ⟨175797554712290566111816001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117198369808193710741210667 175797554712290566111816001)
            ·
              refine ⟨131848166034217924583862001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175797554712290566111816001 131848166034217924583862001)
              ·
                refine ⟨98886124525663443437896501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131848166034217924583862001 98886124525663443437896501)
                ·
                  refine ⟨9270574174280947822302797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98886124525663443437896501 9270574174280947822302797)
                  ·
                    refine ⟨3476465315355355433363549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9270574174280947822302797 3476465315355355433363549)
                    ·
                      refine ⟨1303674493258258287511331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3476465315355355433363549 1303674493258258287511331)
                      ·
                        rfl

theorem cell23_2538897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_2538897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538897 prefixEnd_2538897 := by exact prefixLift 2538897
  have htrace : WordTrace (prefixWord ++ tailWord_2538897) baseStart_2538897 baseEnd_2538897 := by
    simpa [prefixWord, tailWord_2538897, baseEnd_2538897] using wordTrace_append hprefix tailTrace_2538897
  have hstable : (prefixWord ++ tailWord_2538897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538897).length < 2 ^ (prefixWord ++ tailWord_2538897).sum := by decide
  have hdescent : baseEnd_2538897 < baseStart_2538897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538947 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 2, 6]
def baseStart_2538947 : Nat := 118140960795 + 2538947 * 2 ^ 59
def prefixEnd_2538947 : Nat := 4983230072969 + 3 ^ 40 * 2538947 * 2
def baseEnd_2538947 : Nat := 434566722430327697295367

theorem tailTrace_2538947 : CollatzResearch.WordTrace tailWord_2538947 prefixEnd_2538947 434566722430327697295367 := by
  unfold tailWord_2538947
  simp only [CollatzResearch.WordTrace]
  refine ⟨92603004732836111470647095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61735336488557407647098063 92603004732836111470647095)
  ·
    refine ⟨138904507099254167205970643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92603004732836111470647095 138904507099254167205970643)
    ·
      refine ⟨208356760648881250808955965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138904507099254167205970643 208356760648881250808955965)
      ·
        refine ⟨78133785243330469053358487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208356760648881250808955965 78133785243330469053358487)
        ·
          refine ⟨117200677864995703580037731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78133785243330469053358487 117200677864995703580037731)
          ·
            refine ⟨175801016797493555370056597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117200677864995703580037731 175801016797493555370056597)
            ·
              refine ⟨8240672662382510407971403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 175801016797493555370056597 8240672662382510407971403)
              ·
                refine ⟨12361008993573765611957105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8240672662382510407971403 12361008993573765611957105)
                ·
                  refine ⟨9270756745180324208967829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12361008993573765611957105 9270756745180324208967829)
                  ·
                    refine ⟨434566722430327697295367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9270756745180324208967829 434566722430327697295367)
                    ·
                      rfl

theorem cell23_2538947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 6].length) (baseStart_2538947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538947 prefixEnd_2538947 := by exact prefixLift 2538947
  have htrace : WordTrace (prefixWord ++ tailWord_2538947) baseStart_2538947 baseEnd_2538947 := by
    simpa [prefixWord, tailWord_2538947, baseEnd_2538947] using wordTrace_append hprefix tailTrace_2538947
  have hstable : (prefixWord ++ tailWord_2538947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538947).length < 2 ^ (prefixWord ++ tailWord_2538947).sum := by decide
  have hdescent : baseEnd_2538947 < baseStart_2538947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538948 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_2538948 : Nat := 118140960795 + 2538948 * 2 ^ 59
def prefixEnd_2538948 : Nat := 4983230072969 + 3 ^ 40 * 2538948 * 2
def baseEnd_2538948 : Nat := 1303700680771637587973597

theorem tailTrace_2538948 : CollatzResearch.WordTrace tailWord_2538948 prefixEnd_2538948 1303700680771637587973597 := by
  unfold tailWord_2538948
  simp only [CollatzResearch.WordTrace]
  refine ⟨46301520602916244320716749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61735360803888325760955665 46301520602916244320716749)
  ·
    refine ⟨17363070226093591620268781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46301520602916244320716749 17363070226093591620268781)
    ·
      refine ⟨6511151334785096857600793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17363070226093591620268781 6511151334785096857600793)
      ·
        refine ⟨4883363501088822643200595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6511151334785096857600793 4883363501088822643200595)
        ·
          refine ⟨7325045251633233964800893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4883363501088822643200595 7325045251633233964800893)
          ·
            refine ⟨2746891969362462736800335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7325045251633233964800893 2746891969362462736800335)
            ·
              refine ⟨4120337954043694105200503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746891969362462736800335 4120337954043694105200503)
              ·
                refine ⟨6180506931065541157800755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120337954043694105200503 6180506931065541157800755)
                ·
                  refine ⟨9270760396598311736701133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6180506931065541157800755 9270760396598311736701133)
                  ·
                    refine ⟨3476535148724366901262925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9270760396598311736701133 3476535148724366901262925)
                    ·
                      refine ⟨1303700680771637587973597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3476535148724366901262925 1303700680771637587973597)
                      ·
                        rfl

theorem cell23_2538948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_2538948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538948 prefixEnd_2538948 := by exact prefixLift 2538948
  have htrace : WordTrace (prefixWord ++ tailWord_2538948) baseStart_2538948 baseEnd_2538948 := by
    simpa [prefixWord, tailWord_2538948, baseEnd_2538948] using wordTrace_append hprefix tailTrace_2538948
  have hstable : (prefixWord ++ tailWord_2538948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538948).length < 2 ^ (prefixWord ++ tailWord_2538948).sum := by decide
  have hdescent : baseEnd_2538948 < baseStart_2538948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2538967 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_2538967 : Nat := 118140960795 + 2538967 * 2 ^ 59
def prefixEnd_2538967 : Nat := 4983230072969 + 3 ^ 40 * 2538967 * 2
def baseEnd_2538967 : Nat := 1303710436904073013636009

theorem tailTrace_2538967 : CollatzResearch.WordTrace tailWord_2538967 prefixEnd_2538967 1303710436904073013636009 := by
  unfold tailWord_2538967
  simp only [CollatzResearch.WordTrace]
  refine ⟨92603734192763654886375155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61735822795175769924250103 92603734192763654886375155)
  ·
    refine ⟨138905601289145482329562733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92603734192763654886375155 138905601289145482329562733)
    ·
      refine ⟨52089600483429555873586025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138905601289145482329562733 52089600483429555873586025)
      ·
        refine ⟨39067200362572166905189519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52089600483429555873586025 39067200362572166905189519)
        ·
          refine ⟨58600800543858250357784279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39067200362572166905189519 58600800543858250357784279)
          ·
            refine ⟨87901200815787375536676419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58600800543858250357784279 87901200815787375536676419)
            ·
              refine ⟨131851801223681063305014629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87901200815787375536676419 131851801223681063305014629)
              ·
                refine ⟨24722212729440199369690243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131851801223681063305014629 24722212729440199369690243)
                ·
                  refine ⟨37083319094160299054535365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24722212729440199369690243 37083319094160299054535365)
                  ·
                    refine ⟨6953122330155056072725381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37083319094160299054535365 6953122330155056072725381)
                    ·
                      refine ⟨1303710436904073013636009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6953122330155056072725381 1303710436904073013636009)
                      ·
                        rfl

theorem cell23_2538967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_2538967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2538967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2538967 prefixEnd_2538967 := by exact prefixLift 2538967
  have htrace : WordTrace (prefixWord ++ tailWord_2538967) baseStart_2538967 baseEnd_2538967 := by
    simpa [prefixWord, tailWord_2538967, baseEnd_2538967] using wordTrace_append hprefix tailTrace_2538967
  have hstable : (prefixWord ++ tailWord_2538967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2538967).length < 2 ^ (prefixWord ++ tailWord_2538967).sum := by decide
  have hdescent : baseEnd_2538967 < baseStart_2538967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2538967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539004 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_2539004 : Nat := 118140960795 + 2539004 * 2 ^ 59
def prefixEnd_2539004 : Nat := 4983230072969 + 3 ^ 40 * 2539004 * 2
def baseEnd_2539004 : Nat := 1303729435688289368873339

theorem tailTrace_2539004 : CollatzResearch.WordTrace tailWord_2539004 prefixEnd_2539004 1303729435688289368873339 := by
  unfold tailWord_2539004
  simp only [CollatzResearch.WordTrace]
  refine ⟨46302541846814805102736033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61736722462419740136981377 46302541846814805102736033)
  ·
    refine ⟨34726906385111103827052025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46302541846814805102736033 34726906385111103827052025)
    ·
      refine ⟨26045179788833327870289019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34726906385111103827052025 26045179788833327870289019)
      ·
        refine ⟨39067769683249991805433529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26045179788833327870289019 39067769683249991805433529)
        ·
          refine ⟨29300827262437493854075147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39067769683249991805433529 29300827262437493854075147)
          ·
            refine ⟨43951240893656240781112721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29300827262437493854075147 43951240893656240781112721)
            ·
              refine ⟨32963430670242180585834541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43951240893656240781112721 32963430670242180585834541)
              ·
                refine ⟨12361286501340817719687953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32963430670242180585834541 12361286501340817719687953)
                ·
                  refine ⟨9270964876005613289765965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12361286501340817719687953 9270964876005613289765965)
                  ·
                    refine ⟨3476611828502104983662237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9270964876005613289765965 3476611828502104983662237)
                    ·
                      refine ⟨1303729435688289368873339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3476611828502104983662237 1303729435688289368873339)
                      ·
                        rfl

theorem cell23_2539004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_2539004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539004 prefixEnd_2539004 := by exact prefixLift 2539004
  have htrace : WordTrace (prefixWord ++ tailWord_2539004) baseStart_2539004 baseEnd_2539004 := by
    simpa [prefixWord, tailWord_2539004, baseEnd_2539004] using wordTrace_append hprefix tailTrace_2539004
  have hstable : (prefixWord ++ tailWord_2539004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539004).length < 2 ^ (prefixWord ++ tailWord_2539004).sum := by decide
  have hdescent : baseEnd_2539004 < baseStart_2539004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539005 : List Nat := [1, 4, 1, 1, 1, 4, 4, 1, 2, 2, 2]
def baseStart_2539005 : Nat := 118140960795 + 2539005 * 2 ^ 59
def prefixEnd_2539005 : Nat := 4983230072969 + 3 ^ 40 * 2539005 * 2
def baseEnd_2539005 : Nat := 1303729949168943864960835

theorem tailTrace_2539005 : CollatzResearch.WordTrace tailWord_2539005 prefixEnd_2539005 1303729949168943864960835 := by
  unfold tailWord_2539005
  simp only [CollatzResearch.WordTrace]
  refine ⟨92605120166625987376258469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61736746777750658250838979 92605120166625987376258469)
  ·
    refine ⟨17363460031242372633048463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92605120166625987376258469 17363460031242372633048463)
    ·
      refine ⟨26045190046863558949572695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17363460031242372633048463 26045190046863558949572695)
      ·
        refine ⟨39067785070295338424359043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26045190046863558949572695 39067785070295338424359043)
        ·
          refine ⟨58601677605443007636538565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39067785070295338424359043 58601677605443007636538565)
          ·
            refine ⟨10987814551020563931850981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58601677605443007636538565 10987814551020563931850981)
            ·
              refine ⟨2060215228316355737222059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10987814551020563931850981 2060215228316355737222059)
              ·
                refine ⟨3090322842474533605833089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060215228316355737222059 3090322842474533605833089)
                ·
                  refine ⟨2317742131855900204374817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3090322842474533605833089 2317742131855900204374817)
                  ·
                    refine ⟨1738306598891925153281113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2317742131855900204374817 1738306598891925153281113)
                    ·
                      refine ⟨1303729949168943864960835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738306598891925153281113 1303729949168943864960835)
                      ·
                        rfl

theorem cell23_2539005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_2539005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539005 prefixEnd_2539005 := by exact prefixLift 2539005
  have htrace : WordTrace (prefixWord ++ tailWord_2539005) baseStart_2539005 baseEnd_2539005 := by
    simpa [prefixWord, tailWord_2539005, baseEnd_2539005] using wordTrace_append hprefix tailTrace_2539005
  have hstable : (prefixWord ++ tailWord_2539005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539005).length < 2 ^ (prefixWord ++ tailWord_2539005).sum := by decide
  have hdescent : baseEnd_2539005 < baseStart_2539005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539007 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 1, 7]
def baseStart_2539007 : Nat := 118140960795 + 2539007 * 2 ^ 59
def prefixEnd_2539007 : Nat := 4983230072969 + 3 ^ 40 * 2539007 * 2
def baseEnd_2539007 : Nat := 434576992043417619045275

theorem tailTrace_2539007 : CollatzResearch.WordTrace tailWord_2539007 prefixEnd_2539007 434576992043417619045275 := by
  unfold tailWord_2539007
  simp only [CollatzResearch.WordTrace]
  refine ⟨92605193112618741717831275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61736795408412494478554183 92605193112618741717831275)
  ·
    refine ⟨138907789668928112576746913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92605193112618741717831275 138907789668928112576746913)
    ·
      refine ⟨104180842251696084432560185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138907789668928112576746913 104180842251696084432560185)
      ·
        refine ⟨78135631688772063324420139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104180842251696084432560185 78135631688772063324420139)
        ·
          refine ⟨117203447533158094986630209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78135631688772063324420139 117203447533158094986630209)
          ·
            refine ⟨87902585649868571239972657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117203447533158094986630209 87902585649868571239972657)
            ·
              refine ⟨65926939237401428429979493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87902585649868571239972657 65926939237401428429979493)
              ·
                refine ⟨12361301107012767830621155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65926939237401428429979493 12361301107012767830621155)
                ·
                  refine ⟨18541951660519151745931733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12361301107012767830621155 18541951660519151745931733)
                  ·
                    refine ⟨434576992043417619045275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18541951660519151745931733 434576992043417619045275)
                    ·
                      rfl

theorem cell23_2539007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 7].length) (baseStart_2539007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539007 prefixEnd_2539007 := by exact prefixLift 2539007
  have htrace : WordTrace (prefixWord ++ tailWord_2539007) baseStart_2539007 baseEnd_2539007 := by
    simpa [prefixWord, tailWord_2539007, baseEnd_2539007] using wordTrace_append hprefix tailTrace_2539007
  have hstable : (prefixWord ++ tailWord_2539007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539007).length < 2 ^ (prefixWord ++ tailWord_2539007).sum := by decide
  have hdescent : baseEnd_2539007 < baseStart_2539007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539017 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 7]
def baseStart_2539017 : Nat := 118140960795 + 2539017 * 2 ^ 59
def prefixEnd_2539017 : Nat := 4983230072969 + 3 ^ 40 * 2539017 * 2
def baseEnd_2539017 : Nat := 1303736110936797818010779

theorem tailTrace_2539017 : CollatzResearch.WordTrace tailWord_2539017 prefixEnd_2539017 1303736110936797818010779 := by
  unfold tailWord_2539017
  simp only [CollatzResearch.WordTrace]
  refine ⟨92605557842582513425695305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61737038561721675617130203 92605557842582513425695305)
  ·
    refine ⟨69454168381936885069271479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92605557842582513425695305 69454168381936885069271479)
    ·
      refine ⟨104181252572905327603907219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69454168381936885069271479 104181252572905327603907219)
      ·
        refine ⟨156271878859357991405860829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104181252572905327603907219 156271878859357991405860829)
        ·
          refine ⟨58601954572259246777197811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156271878859357991405860829 58601954572259246777197811)
          ·
            refine ⟨87902931858388870165796717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58601954572259246777197811 87902931858388870165796717)
            ·
              refine ⟨32963599446895826312173769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87902931858388870165796717 32963599446895826312173769)
              ·
                refine ⟨24722699585171869734130327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32963599446895826312173769 24722699585171869734130327)
                ·
                  refine ⟨37084049377757804601195491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24722699585171869734130327 37084049377757804601195491)
                  ·
                    refine ⟨55626074066636706901793237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37084049377757804601195491 55626074066636706901793237)
                    ·
                      refine ⟨1303736110936797818010779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55626074066636706901793237 1303736110936797818010779)
                      ·
                        rfl

theorem cell23_2539017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_2539017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539017 prefixEnd_2539017 := by exact prefixLift 2539017
  have htrace : WordTrace (prefixWord ++ tailWord_2539017) baseStart_2539017 baseEnd_2539017 := by
    simpa [prefixWord, tailWord_2539017, baseEnd_2539017] using wordTrace_append hprefix tailTrace_2539017
  have hstable : (prefixWord ++ tailWord_2539017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539017).length < 2 ^ (prefixWord ++ tailWord_2539017).sum := by decide
  have hdescent : baseEnd_2539017 < baseStart_2539017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539061 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_2539061 : Nat := 118140960795 + 2539061 * 2 ^ 59
def prefixEnd_2539061 : Nat := 4983230072969 + 3 ^ 40 * 2539061 * 2
def baseEnd_2539061 : Nat := 1303758704085595645860577

theorem tailTrace_2539061 : CollatzResearch.WordTrace tailWord_2539061 prefixEnd_2539061 1303758704085595645860577 := by
  unfold tailWord_2539061
  simp only [CollatzResearch.WordTrace]
  refine ⟨92607162654423108940297037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61738108436282072626864691 92607162654423108940297037)
  ·
    refine ⟨34727685995408665852611389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92607162654423108940297037 34727685995408665852611389)
    ·
      refine ⟨13022882248278249694729271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34727685995408665852611389 13022882248278249694729271)
      ·
        refine ⟨19534323372417374542093907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13022882248278249694729271 19534323372417374542093907)
        ·
          refine ⟨29301485058626061813140861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19534323372417374542093907 29301485058626061813140861)
          ·
            refine ⟨10988056896984773179927823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29301485058626061813140861 10988056896984773179927823)
            ·
              refine ⟨16482085345477159769891735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10988056896984773179927823 16482085345477159769891735)
              ·
                refine ⟨24723128018215739654837603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16482085345477159769891735 24723128018215739654837603)
                ·
                  refine ⟨37084692027323609482256405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24723128018215739654837603 37084692027323609482256405)
                  ·
                    refine ⟨1738344938780794194480769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37084692027323609482256405 1738344938780794194480769)
                    ·
                      refine ⟨1303758704085595645860577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738344938780794194480769 1303758704085595645860577)
                      ·
                        rfl

theorem cell23_2539061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_2539061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539061 prefixEnd_2539061 := by exact prefixLift 2539061
  have htrace : WordTrace (prefixWord ++ tailWord_2539061) baseStart_2539061 baseEnd_2539061 := by
    simpa [prefixWord, tailWord_2539061, baseEnd_2539061] using wordTrace_append hprefix tailTrace_2539061
  have hstable : (prefixWord ++ tailWord_2539061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539061).length < 2 ^ (prefixWord ++ tailWord_2539061).sum := by decide
  have hdescent : baseEnd_2539061 < baseStart_2539061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539071 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 3, 4]
def baseStart_2539071 : Nat := 118140960795 + 2539071 * 2 ^ 59
def prefixEnd_2539071 : Nat := 4983230072969 + 3 ^ 40 * 2539071 * 2
def baseEnd_2539071 : Nat := 434587946297380202245177

theorem tailTrace_2539071 : CollatzResearch.WordTrace tailWord_2539071 prefixEnd_2539071 434587946297380202245177 := by
  unfold tailWord_2539071
  simp only [CollatzResearch.WordTrace]
  refine ⟨92607527384386880648161067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61738351589591253765440711 92607527384386880648161067)
  ·
    refine ⟨138911291076580320972241601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92607527384386880648161067 138911291076580320972241601)
    ·
      refine ⟨104183468307435240729181201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138911291076580320972241601 104183468307435240729181201)
      ·
        refine ⟨78137601230576430546885901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104183468307435240729181201 78137601230576430546885901)
        ·
          refine ⟨29301600461466161455082213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78137601230576430546885901 29301600461466161455082213)
          ·
            refine ⟨5494050086524905272827915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29301600461466161455082213 5494050086524905272827915)
            ·
              refine ⟨8241075129787357909241873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5494050086524905272827915 8241075129787357909241873)
              ·
                refine ⟨6180806347340518431931405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8241075129787357909241873 6180806347340518431931405)
                ·
                  refine ⟨2317802380252694411974277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6180806347340518431931405 2317802380252694411974277)
                  ·
                    refine ⟨434587946297380202245177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2317802380252694411974277 434587946297380202245177)
                    ·
                      rfl

theorem cell23_2539071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 4].length) (baseStart_2539071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539071 prefixEnd_2539071 := by exact prefixLift 2539071
  have htrace : WordTrace (prefixWord ++ tailWord_2539071) baseStart_2539071 baseEnd_2539071 := by
    simpa [prefixWord, tailWord_2539071, baseEnd_2539071] using wordTrace_append hprefix tailTrace_2539071
  have hstable : (prefixWord ++ tailWord_2539071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539071).length < 2 ^ (prefixWord ++ tailWord_2539071).sum := by decide
  have hdescent : baseEnd_2539071 < baseStart_2539071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539088 : List Nat := [2, 1, 1, 1, 1, 3, 6, 3, 1, 4]
def baseStart_2539088 : Nat := 118140960795 + 2539088 * 2 ^ 59
def prefixEnd_2539088 : Nat := 4983230072969 + 3 ^ 40 * 2539088 * 2
def baseEnd_2539088 : Nat := 434590856021089013407651

theorem tailTrace_2539088 : CollatzResearch.WordTrace tailWord_2539088 prefixEnd_2539088 434590856021089013407651 := by
  unfold tailWord_2539088
  simp only [CollatzResearch.WordTrace]
  refine ⟨46304073712662646275764959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61738764950216861701019945 46304073712662646275764959)
  ·
    refine ⟨69456110568993969413647439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46304073712662646275764959 69456110568993969413647439)
    ·
      refine ⟨104184165853490954120471159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69456110568993969413647439 104184165853490954120471159)
      ·
        refine ⟨156276248780236431180706739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104184165853490954120471159 156276248780236431180706739)
        ·
          refine ⟨234414373170354646771060109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156276248780236431180706739 234414373170354646771060109)
          ·
            refine ⟨87905389938882992539147541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234414373170354646771060109 87905389938882992539147541)
            ·
              refine ⟨4120565153385140275272541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87905389938882992539147541 4120565153385140275272541)
              ·
                refine ⟨1545211932519427603227203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4120565153385140275272541 1545211932519427603227203)
                ·
                  refine ⟨2317817898779141404840805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545211932519427603227203 2317817898779141404840805)
                  ·
                    refine ⟨434590856021089013407651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2317817898779141404840805 434590856021089013407651)
                    ·
                      rfl

theorem cell23_2539088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 1, 4].length) (baseStart_2539088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539088 prefixEnd_2539088 := by exact prefixLift 2539088
  have htrace : WordTrace (prefixWord ++ tailWord_2539088) baseStart_2539088 baseEnd_2539088 := by
    simpa [prefixWord, tailWord_2539088, baseEnd_2539088] using wordTrace_append hprefix tailTrace_2539088
  have hstable : (prefixWord ++ tailWord_2539088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539088).length < 2 ^ (prefixWord ++ tailWord_2539088).sum := by decide
  have hdescent : baseEnd_2539088 < baseStart_2539088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539131 : List Nat := [1, 1, 1, 1, 1, 4, 6, 2, 1, 5]
def baseStart_2539131 : Nat := 118140960795 + 2539131 * 2 ^ 59
def prefixEnd_2539131 : Nat := 4983230072969 + 3 ^ 40 * 2539131 * 2
def baseEnd_2539131 : Nat := 434598215910470123995085

theorem tailTrace_2539131 : CollatzResearch.WordTrace tailWord_2539131 prefixEnd_2539131 434598215910470123995085 := by
  unfold tailWord_2539131
  simp only [CollatzResearch.WordTrace]
  refine ⟨92609715764169510895345247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61739810509446340596896831 92609715764169510895345247)
  ·
    refine ⟨138914573646254266343017871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92609715764169510895345247 138914573646254266343017871)
    ·
      refine ⟨208371860469381399514526807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138914573646254266343017871 208371860469381399514526807)
      ·
        refine ⟨312557790704072099271790211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208371860469381399514526807 312557790704072099271790211)
        ·
          refine ⟨468836686056108148907685317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312557790704072099271790211 468836686056108148907685317)
          ·
            refine ⟨87906878635520277920190997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 468836686056108148907685317 87906878635520277920190997)
            ·
              refine ⟨4120634936040013027508953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87906878635520277920190997 4120634936040013027508953)
              ·
                refine ⟨3090476202030009770631715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4120634936040013027508953 3090476202030009770631715)
                ·
                  refine ⟨4635714303045014655947573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3090476202030009770631715 4635714303045014655947573)
                  ·
                    refine ⟨434598215910470123995085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4635714303045014655947573 434598215910470123995085)
                    ·
                      rfl

theorem cell23_2539131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 5].length) (baseStart_2539131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539131 prefixEnd_2539131 := by exact prefixLift 2539131
  have htrace : WordTrace (prefixWord ++ tailWord_2539131) baseStart_2539131 baseEnd_2539131 := by
    simpa [prefixWord, tailWord_2539131, baseEnd_2539131] using wordTrace_append hprefix tailTrace_2539131
  have hstable : (prefixWord ++ tailWord_2539131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539131).length < 2 ^ (prefixWord ++ tailWord_2539131).sum := by decide
  have hdescent : baseEnd_2539131 < baseStart_2539131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539145 : List Nat := [1, 2, 1, 1, 4, 1, 5, 3, 1, 1, 3]
def baseStart_2539145 : Nat := 118140960795 + 2539145 * 2 ^ 59
def prefixEnd_2539145 : Nat := 4983230072969 + 3 ^ 40 * 2539145 * 2
def baseEnd_2539145 : Nat := 1303801836460573317210191

theorem tailTrace_2539145 : CollatzResearch.WordTrace tailWord_2539145 prefixEnd_2539145 1303801836460573317210191 := by
  unfold tailWord_2539145
  simp only [CollatzResearch.WordTrace]
  refine ⟨92610226386118791286354889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61740150924079194190903259 92610226386118791286354889)
  ·
    refine ⟨69457669789589093464766167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92610226386118791286354889 69457669789589093464766167)
    ·
      refine ⟨104186504684383640197149251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69457669789589093464766167 104186504684383640197149251)
      ·
        refine ⟨156279757026575460295723877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104186504684383640197149251 156279757026575460295723877)
        ·
          refine ⟨29302454442482898805448227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156279757026575460295723877 29302454442482898805448227)
          ·
            refine ⟨43953681663724348208172341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29302454442482898805448227 43953681663724348208172341)
            ·
              refine ⟨4120657655974157644516157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43953681663724348208172341 4120657655974157644516157)
              ·
                refine ⟨1545246620990309116693559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4120657655974157644516157 1545246620990309116693559)
                ·
                  refine ⟨2317869931485463675040339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545246620990309116693559 2317869931485463675040339)
                  ·
                    refine ⟨3476804897228195512560509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2317869931485463675040339 3476804897228195512560509)
                    ·
                      refine ⟨1303801836460573317210191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3476804897228195512560509 1303801836460573317210191)
                      ·
                        rfl

theorem cell23_2539145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 3, 1, 1, 3].length) (baseStart_2539145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539145 prefixEnd_2539145 := by exact prefixLift 2539145
  have htrace : WordTrace (prefixWord ++ tailWord_2539145) baseStart_2539145 baseEnd_2539145 := by
    simpa [prefixWord, tailWord_2539145, baseEnd_2539145] using wordTrace_append hprefix tailTrace_2539145
  have hstable : (prefixWord ++ tailWord_2539145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539145).length < 2 ^ (prefixWord ++ tailWord_2539145).sum := by decide
  have hdescent : baseEnd_2539145 < baseStart_2539145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539171 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 3]
def baseStart_2539171 : Nat := 118140960795 + 2539171 * 2 ^ 59
def prefixEnd_2539171 : Nat := 4983230072969 + 3 ^ 40 * 2539171 * 2
def baseEnd_2539171 : Nat := 1303815186957590215485071

theorem tailTrace_2539171 : CollatzResearch.WordTrace tailWord_2539171 prefixEnd_2539171 1303815186957590215485071 := by
  unfold tailWord_2539171
  simp only [CollatzResearch.WordTrace]
  refine ⟨92611174684024597726801367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61740783122683065151200911 92611174684024597726801367)
  ·
    refine ⟨138916762026036896590202051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92611174684024597726801367 138916762026036896590202051)
    ·
      refine ⟨208375143039055344885303077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138916762026036896590202051 208375143039055344885303077)
      ·
        refine ⟨39070339319822877165994327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208375143039055344885303077 39070339319822877165994327)
        ·
          refine ⟨58605508979734315748991491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39070339319822877165994327 58605508979734315748991491)
          ·
            refine ⟨87908263469601473623487237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58605508979734315748991491 87908263469601473623487237)
            ·
              refine ⟨16482799400550276304403857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87908263469601473623487237 16482799400550276304403857)
              ·
                refine ⟨12362099550412707228302893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16482799400550276304403857 12362099550412707228302893)
                ·
                  refine ⟨4635787331404765210613585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12362099550412707228302893 4635787331404765210613585)
                  ·
                    refine ⟨3476840498553573907960189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4635787331404765210613585 3476840498553573907960189)
                    ·
                      refine ⟨1303815186957590215485071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3476840498553573907960189 1303815186957590215485071)
                      ·
                        rfl

theorem cell23_2539171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_2539171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539171 prefixEnd_2539171 := by exact prefixLift 2539171
  have htrace : WordTrace (prefixWord ++ tailWord_2539171) baseStart_2539171 baseEnd_2539171 := by
    simpa [prefixWord, tailWord_2539171, baseEnd_2539171] using wordTrace_append hprefix tailTrace_2539171
  have hstable : (prefixWord ++ tailWord_2539171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539171).length < 2 ^ (prefixWord ++ tailWord_2539171).sum := by decide
  have hdescent : baseEnd_2539171 < baseStart_2539171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539181 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2539181 : Nat := 118140960795 + 2539181 * 2 ^ 59
def prefixEnd_2539181 : Nat := 4983230072969 + 3 ^ 40 * 2539181 * 2
def baseEnd_2539181 : Nat := 1303820321764135176360025

theorem tailTrace_2539181 : CollatzResearch.WordTrace tailWord_2539181 prefixEnd_2539181 1303820321764135176360025 := by
  unfold tailWord_2539181
  simp only [CollatzResearch.WordTrace]
  refine ⟨92611539413988369434665397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61741026275992246289776931 92611539413988369434665397)
  ·
    refine ⟨8682331820061409634499881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92611539413988369434665397 8682331820061409634499881)
    ·
      refine ⟨6511748865046057225874911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8682331820061409634499881 6511748865046057225874911)
      ·
        refine ⟨9767623297569085838812367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6511748865046057225874911 9767623297569085838812367)
        ·
          refine ⟨14651434946353628758218551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9767623297569085838812367 14651434946353628758218551)
          ·
            refine ⟨21977152419530443137327827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14651434946353628758218551 21977152419530443137327827)
            ·
              refine ⟨32965728629295664705991741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21977152419530443137327827 32965728629295664705991741)
              ·
                refine ⟨12362148235985874264746903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32965728629295664705991741 12362148235985874264746903)
                ·
                  refine ⟨18543222353978811397120355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12362148235985874264746903 18543222353978811397120355)
                  ·
                    refine ⟨27814833530968217095680533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18543222353978811397120355 27814833530968217095680533)
                    ·
                      refine ⟨1303820321764135176360025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27814833530968217095680533 1303820321764135176360025)
                      ·
                        rfl

theorem cell23_2539181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2539181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539181 prefixEnd_2539181 := by exact prefixLift 2539181
  have htrace : WordTrace (prefixWord ++ tailWord_2539181) baseStart_2539181 baseEnd_2539181 := by
    simpa [prefixWord, tailWord_2539181, baseEnd_2539181] using wordTrace_append hprefix tailTrace_2539181
  have hstable : (prefixWord ++ tailWord_2539181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539181).length < 2 ^ (prefixWord ++ tailWord_2539181).sum := by decide
  have hdescent : baseEnd_2539181 < baseStart_2539181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539182 : List Nat := [4, 1, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2539182 : Nat := 118140960795 + 2539182 * 2 ^ 59
def prefixEnd_2539182 : Nat := 4983230072969 + 3 ^ 40 * 2539182 * 2
def baseEnd_2539182 : Nat := 434606945081596557482507

theorem tailTrace_2539182 : CollatzResearch.WordTrace tailWord_2539182 prefixEnd_2539182 434606945081596557482507 := by
  unfold tailWord_2539182
  simp only [CollatzResearch.WordTrace]
  refine ⟨11576446985873093325681475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61741050591323164403634533 11576446985873093325681475)
  ·
    refine ⟨17364670478809639988522213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11576446985873093325681475 17364670478809639988522213)
    ·
      refine ⟨3255875714776807497847915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17364670478809639988522213 3255875714776807497847915)
      ·
        refine ⟨4883813572165211246771873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3255875714776807497847915 4883813572165211246771873)
        ·
          refine ⟨3662860179123908435078905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4883813572165211246771873 3662860179123908435078905)
          ·
            refine ⟨2747145134342931326309179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3662860179123908435078905 2747145134342931326309179)
            ·
              refine ⟨4120717701514396989463769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2747145134342931326309179 4120717701514396989463769)
              ·
                refine ⟨3090538276135797742097827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4120717701514396989463769 3090538276135797742097827)
                ·
                  refine ⟨4635807414203696613146741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3090538276135797742097827 4635807414203696613146741)
                  ·
                    refine ⟨434606945081596557482507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4635807414203696613146741 434606945081596557482507)
                    ·
                      rfl

theorem cell23_2539182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2539182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539182 prefixEnd_2539182 := by exact prefixLift 2539182
  have htrace : WordTrace (prefixWord ++ tailWord_2539182) baseStart_2539182 baseEnd_2539182 := by
    simpa [prefixWord, tailWord_2539182, baseEnd_2539182] using wordTrace_append hprefix tailTrace_2539182
  have hstable : (prefixWord ++ tailWord_2539182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539182).length < 2 ^ (prefixWord ++ tailWord_2539182).sum := by decide
  have hdescent : baseEnd_2539182 < baseStart_2539182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539198 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_2539198 : Nat := 118140960795 + 2539198 * 2 ^ 59
def prefixEnd_2539198 : Nat := 4983230072969 + 3 ^ 40 * 2539198 * 2
def baseEnd_2539198 : Nat := 1303829050935261609847447

theorem tailTrace_2539198 : CollatzResearch.WordTrace tailWord_2539198 prefixEnd_2539198 1303829050935261609847447 := by
  unfold tailWord_2539198
  simp only [CollatzResearch.WordTrace]
  refine ⟨11576519931865847667254281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61741439636617854225356165 11576519931865847667254281)
  ·
    refine ⟨8682389948899385750440711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11576519931865847667254281 8682389948899385750440711)
    ·
      refine ⟨13023584923349078625661067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8682389948899385750440711 13023584923349078625661067)
      ·
        refine ⟨19535377385023617938491601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13023584923349078625661067 19535377385023617938491601)
        ·
          refine ⟨14651533038767713453868701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19535377385023617938491601 14651533038767713453868701)
          ·
            refine ⟨5494324889537892545200763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14651533038767713453868701 5494324889537892545200763)
            ·
              refine ⟨8241487334306838817801145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5494324889537892545200763 8241487334306838817801145)
              ·
                refine ⟨6181115500730129113350859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8241487334306838817801145 6181115500730129113350859)
                ·
                  refine ⟨9271673251095193670026289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6181115500730129113350859 9271673251095193670026289)
                  ·
                    refine ⟨6953754938321395252519717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9271673251095193670026289 6953754938321395252519717)
                    ·
                      refine ⟨1303829050935261609847447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6953754938321395252519717 1303829050935261609847447)
                      ·
                        rfl

theorem cell23_2539198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_2539198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539198 prefixEnd_2539198 := by exact prefixLift 2539198
  have htrace : WordTrace (prefixWord ++ tailWord_2539198) baseStart_2539198 baseEnd_2539198 := by
    simpa [prefixWord, tailWord_2539198, baseEnd_2539198] using wordTrace_append hprefix tailTrace_2539198
  have hstable : (prefixWord ++ tailWord_2539198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539198).length < 2 ^ (prefixWord ++ tailWord_2539198).sum := by decide
  have hdescent : baseEnd_2539198 < baseStart_2539198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539235 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2539235 : Nat := 118140960795 + 2539235 * 2 ^ 59
def prefixEnd_2539235 : Nat := 4983230072969 + 3 ^ 40 * 2539235 * 2
def baseEnd_2539235 : Nat := 1303848049719477965084777

theorem tailTrace_2539235 : CollatzResearch.WordTrace tailWord_2539235 prefixEnd_2539235 1303848049719477965084777 := by
  unfold tailWord_2539235
  simp only [CollatzResearch.WordTrace]
  refine ⟨92613508955792736657131159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61742339303861824438087439 92613508955792736657131159)
  ·
    refine ⟨138920263433689104985696739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92613508955792736657131159 138920263433689104985696739)
    ·
      refine ⟨208380395150533657478545109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138920263433689104985696739 208380395150533657478545109)
      ·
        refine ⟨4883915511340632597153401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 208380395150533657478545109 4883915511340632597153401)
        ·
          refine ⟨3662936633505474447865051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4883915511340632597153401 3662936633505474447865051)
          ·
            refine ⟨5494404950258211671797577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3662936633505474447865051 5494404950258211671797577)
            ·
              refine ⟨4120803712693658753848183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5494404950258211671797577 4120803712693658753848183)
              ·
                refine ⟨6181205569040488130772275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120803712693658753848183 6181205569040488130772275)
                ·
                  refine ⟨9271808353560732196158413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6181205569040488130772275 9271808353560732196158413)
                  ·
                    refine ⟨3476928132585274573559405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9271808353560732196158413 3476928132585274573559405)
                    ·
                      refine ⟨1303848049719477965084777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3476928132585274573559405 1303848049719477965084777)
                      ·
                        rfl

theorem cell23_2539235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2539235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539235 prefixEnd_2539235 := by exact prefixLift 2539235
  have htrace : WordTrace (prefixWord ++ tailWord_2539235) baseStart_2539235 baseEnd_2539235 := by
    simpa [prefixWord, tailWord_2539235, baseEnd_2539235] using wordTrace_append hprefix tailTrace_2539235
  have hstable : (prefixWord ++ tailWord_2539235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539235).length < 2 ^ (prefixWord ++ tailWord_2539235).sum := by decide
  have hdescent : baseEnd_2539235 < baseStart_2539235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539245 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_2539245 : Nat := 118140960795 + 2539245 * 2 ^ 59
def prefixEnd_2539245 : Nat := 4983230072969 + 3 ^ 40 * 2539245 * 2
def baseEnd_2539245 : Nat := 1303853184526022925959731

theorem tailTrace_2539245 : CollatzResearch.WordTrace tailWord_2539245 prefixEnd_2539245 1303853184526022925959731 := by
  unfold tailWord_2539245
  simp only [CollatzResearch.WordTrace]
  refine ⟨92613873685756508364995189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61742582457171005576663459 92613873685756508364995189)
  ·
    refine ⟨8682550658039672659218299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92613873685756508364995189 8682550658039672659218299)
    ·
      refine ⟨13023825987059508988827449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8682550658039672659218299 13023825987059508988827449)
      ·
        refine ⟨9767869490294631741620587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13023825987059508988827449 9767869490294631741620587)
        ·
          refine ⟨14651804235441947612430881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9767869490294631741620587 14651804235441947612430881)
          ·
            refine ⟨10988853176581460709323161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14651804235441947612430881 10988853176581460709323161)
            ·
              refine ⟨8241639882436095531992371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10988853176581460709323161 8241639882436095531992371)
              ·
                refine ⟨12362459823654143297988557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8241639882436095531992371 12362459823654143297988557)
                ·
                  refine ⟨4635922433870303736745709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12362459823654143297988557 4635922433870303736745709)
                  ·
                    refine ⟨1738470912701363901279641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4635922433870303736745709 1738470912701363901279641)
                    ·
                      refine ⟨1303853184526022925959731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738470912701363901279641 1303853184526022925959731)
                      ·
                        rfl

theorem cell23_2539245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_2539245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539245 prefixEnd_2539245 := by exact prefixLift 2539245
  have htrace : WordTrace (prefixWord ++ tailWord_2539245) baseStart_2539245 baseEnd_2539245 := by
    simpa [prefixWord, tailWord_2539245, baseEnd_2539245] using wordTrace_append hprefix tailTrace_2539245
  have hstable : (prefixWord ++ tailWord_2539245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539245).length < 2 ^ (prefixWord ++ tailWord_2539245).sum := by decide
  have hdescent : baseEnd_2539245 < baseStart_2539245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539252 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2539252 : Nat := 118140960795 + 2539252 * 2 ^ 59
def prefixEnd_2539252 : Nat := 4983230072969 + 3 ^ 40 * 2539252 * 2
def baseEnd_2539252 : Nat := 1303856778890604398572199

theorem tailTrace_2539252 : CollatzResearch.WordTrace tailWord_2539252 prefixEnd_2539252 1303856778890604398572199 := by
  unfold tailWord_2539252
  simp only [CollatzResearch.WordTrace]
  refine ⟨46307064498365574280250005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61742752664487432373666673 46307064498365574280250005)
  ·
    refine ⟨2170643648360886294386719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 46307064498365574280250005 2170643648360886294386719)
    ·
      refine ⟨3255965472541329441580079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2170643648360886294386719 3255965472541329441580079)
      ·
        refine ⟨4883948208811994162370119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3255965472541329441580079 4883948208811994162370119)
        ·
          refine ⟨7325922313217991243555179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4883948208811994162370119 7325922313217991243555179)
          ·
            refine ⟨10988883469826986865332769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7325922313217991243555179 10988883469826986865332769)
            ·
              refine ⟨8241662602370240148999577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10988883469826986865332769 8241662602370240148999577)
              ·
                refine ⟨6181246951777680111749683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8241662602370240148999577 6181246951777680111749683)
                ·
                  refine ⟨9271870427666520167624525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6181246951777680111749683 9271870427666520167624525)
                  ·
                    refine ⟨3476951410374945062859197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9271870427666520167624525 3476951410374945062859197)
                    ·
                      refine ⟨1303856778890604398572199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3476951410374945062859197 1303856778890604398572199)
                      ·
                        rfl

theorem cell23_2539252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2539252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539252 prefixEnd_2539252 := by exact prefixLift 2539252
  have htrace : WordTrace (prefixWord ++ tailWord_2539252) baseStart_2539252 baseEnd_2539252 := by
    simpa [prefixWord, tailWord_2539252, baseEnd_2539252] using wordTrace_append hprefix tailTrace_2539252
  have hstable : (prefixWord ++ tailWord_2539252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539252).length < 2 ^ (prefixWord ++ tailWord_2539252).sum := by decide
  have hdescent : baseEnd_2539252 < baseStart_2539252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539261 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_2539261 : Nat := 118140960795 + 2539261 * 2 ^ 59
def prefixEnd_2539261 : Nat := 4983230072969 + 3 ^ 40 * 2539261 * 2
def baseEnd_2539261 : Nat := 1303861400216494863359657

theorem tailTrace_2539261 : CollatzResearch.WordTrace tailWord_2539261 prefixEnd_2539261 1303861400216494863359657 := by
  unfold tailWord_2539261
  simp only [CollatzResearch.WordTrace]
  refine ⟨92614457253698543097577637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61742971502465695398385091 92614457253698543097577637)
  ·
    refine ⟨17365210735068476830795807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92614457253698543097577637 17365210735068476830795807)
    ·
      refine ⟨26047816102602715246193711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17365210735068476830795807 26047816102602715246193711)
      ·
        refine ⟨39071724153904072869290567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26047816102602715246193711 39071724153904072869290567)
        ·
          refine ⟨58607586230856109303935851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39071724153904072869290567 58607586230856109303935851)
          ·
            refine ⟨87911379346284163955903777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58607586230856109303935851 87911379346284163955903777)
            ·
              refine ⟨65933534509713122966927833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87911379346284163955903777 65933534509713122966927833)
              ·
                refine ⟨49450150882284842225195875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65933534509713122966927833 49450150882284842225195875)
                ·
                  refine ⟨74175226323427263337793813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49450150882284842225195875 74175226323427263337793813)
                  ·
                    refine ⟨3476963733910652968959085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74175226323427263337793813 3476963733910652968959085)
                    ·
                      refine ⟨1303861400216494863359657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3476963733910652968959085 1303861400216494863359657)
                      ·
                        rfl

theorem cell23_2539261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_2539261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539261 prefixEnd_2539261 := by exact prefixLift 2539261
  have htrace : WordTrace (prefixWord ++ tailWord_2539261) baseStart_2539261 baseEnd_2539261 := by
    simpa [prefixWord, tailWord_2539261, baseEnd_2539261] using wordTrace_append hprefix tailTrace_2539261
  have hstable : (prefixWord ++ tailWord_2539261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539261).length < 2 ^ (prefixWord ++ tailWord_2539261).sum := by decide
  have hdescent : baseEnd_2539261 < baseStart_2539261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539270 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2539270 : Nat := 118140960795 + 2539270 * 2 ^ 59
def prefixEnd_2539270 : Nat := 4983230072969 + 3 ^ 40 * 2539270 * 2
def baseEnd_2539270 : Nat := 1303866021542385328147117

theorem tailTrace_2539270 : CollatzResearch.WordTrace tailWord_2539270 prefixEnd_2539270 1303866021542385328147117 := by
  unfold tailWord_2539270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2894212047208310551082977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61743190340443958423103509 2894212047208310551082977)
  ·
    refine ⟨2170659035406232913312233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2894212047208310551082977 2170659035406232913312233)
    ·
      refine ⟨1627994276554674684984175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2170659035406232913312233 1627994276554674684984175)
      ·
        refine ⟨2441991414832012027476263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1627994276554674684984175 2441991414832012027476263)
        ·
          refine ⟨3662987122248018041214395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2441991414832012027476263 3662987122248018041214395)
          ·
            refine ⟨5494480683372027061821593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3662987122248018041214395 5494480683372027061821593)
            ·
              refine ⟨4120860512529020296366195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5494480683372027061821593 4120860512529020296366195)
              ·
                refine ⟨6181290768793530444549293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120860512529020296366195 6181290768793530444549293)
                ·
                  refine ⟨2317984038297573916705985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6181290768793530444549293 2317984038297573916705985)
                  ·
                    refine ⟨1738488028723180437529489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2317984038297573916705985 1738488028723180437529489)
                    ·
                      refine ⟨1303866021542385328147117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738488028723180437529489 1303866021542385328147117)
                      ·
                        rfl

theorem cell23_2539270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2539270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539270 prefixEnd_2539270 := by exact prefixLift 2539270
  have htrace : WordTrace (prefixWord ++ tailWord_2539270) baseStart_2539270 baseEnd_2539270 := by
    simpa [prefixWord, tailWord_2539270, baseEnd_2539270] using wordTrace_append hprefix tailTrace_2539270
  have hstable : (prefixWord ++ tailWord_2539270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539270).length < 2 ^ (prefixWord ++ tailWord_2539270).sum := by decide
  have hdescent : baseEnd_2539270 < baseStart_2539270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539391 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 6]
def baseStart_2539391 : Nat := 118140960795 + 2539391 * 2 ^ 59
def prefixEnd_2539391 : Nat := 4983230072969 + 3 ^ 40 * 2539391 * 2
def baseEnd_2539391 : Nat := 1303928152701579354734059

theorem tailTrace_2539391 : CollatzResearch.WordTrace tailWord_2539391 prefixEnd_2539391 1303928152701579354734059 := by
  unfold tailWord_2539391
  simp only [CollatzResearch.WordTrace]
  refine ⟨92619198743227575299810027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61746132495485050199873351 92619198743227575299810027)
  ·
    refine ⟨138928798114841362949715041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92619198743227575299810027 138928798114841362949715041)
    ·
      refine ⟨104196598586131022212286281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138928798114841362949715041 104196598586131022212286281)
      ·
        refine ⟨78147448939598266659214711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104196598586131022212286281 78147448939598266659214711)
        ·
          refine ⟨117221173409397399988822067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78147448939598266659214711 117221173409397399988822067)
          ·
            refine ⟨175831760114096099983233101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117221173409397399988822067 175831760114096099983233101)
            ·
              refine ⟨65936910042786037493712413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175831760114096099983233101 65936910042786037493712413)
              ·
                refine ⟨24726341266044764060142155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65936910042786037493712413 24726341266044764060142155)
                ·
                  refine ⟨37089511899067146090213233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24726341266044764060142155 37089511899067146090213233)
                  ·
                    refine ⟨27817133924300359567659925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37089511899067146090213233 27817133924300359567659925)
                    ·
                      refine ⟨1303928152701579354734059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27817133924300359567659925 1303928152701579354734059)
                      ·
                        rfl

theorem cell23_2539391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_2539391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539391 prefixEnd_2539391 := by exact prefixLift 2539391
  have htrace : WordTrace (prefixWord ++ tailWord_2539391) baseStart_2539391 baseEnd_2539391 := by
    simpa [prefixWord, tailWord_2539391, baseEnd_2539391] using wordTrace_append hprefix tailTrace_2539391
  have hstable : (prefixWord ++ tailWord_2539391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539391).length < 2 ^ (prefixWord ++ tailWord_2539391).sum := by decide
  have hdescent : baseEnd_2539391 < baseStart_2539391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539411 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 5]
def baseStart_2539411 : Nat := 118140960795 + 2539411 * 2 ^ 59
def prefixEnd_2539411 : Nat := 4983230072969 + 3 ^ 40 * 2539411 * 2
def baseEnd_2539411 : Nat := 1303938422314669276483967

theorem tailTrace_2539411 : CollatzResearch.WordTrace tailWord_2539411 prefixEnd_2539411 1303938422314669276483967 := by
  unfold tailWord_2539411
  simp only [CollatzResearch.WordTrace]
  refine ⟨92619928203155118715538087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61746618802103412477025391 92619928203155118715538087)
  ·
    refine ⟨138929892304732678073307131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92619928203155118715538087 138929892304732678073307131)
    ·
      refine ⟨208394838457099017109960697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138929892304732678073307131 208394838457099017109960697)
      ·
        refine ⟨156296128842824262832470523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208394838457099017109960697 156296128842824262832470523)
        ·
          refine ⟨234444193264236394248705785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156296128842824262832470523 234444193264236394248705785)
          ·
            refine ⟨175833144948177295686529339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234444193264236394248705785 175833144948177295686529339)
            ·
              refine ⟨263749717422265943529794009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175833144948177295686529339 263749717422265943529794009)
              ·
                refine ⟨197812288066699457647345507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263749717422265943529794009 197812288066699457647345507)
                ·
                  refine ⟨296718432100049186471018261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197812288066699457647345507 296718432100049186471018261)
                  ·
                    refine ⟨13908676504689805615828981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 296718432100049186471018261 13908676504689805615828981)
                    ·
                      refine ⟨1303938422314669276483967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13908676504689805615828981 1303938422314669276483967)
                      ·
                        rfl

theorem cell23_2539411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_2539411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539411 prefixEnd_2539411 := by exact prefixLift 2539411
  have htrace : WordTrace (prefixWord ++ tailWord_2539411) baseStart_2539411 baseEnd_2539411 := by
    simpa [prefixWord, tailWord_2539411, baseEnd_2539411] using wordTrace_append hprefix tailTrace_2539411
  have hstable : (prefixWord ++ tailWord_2539411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539411).length < 2 ^ (prefixWord ++ tailWord_2539411).sum := by decide
  have hdescent : baseEnd_2539411 < baseStart_2539411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539415 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 5, 1, 3]
def baseStart_2539415 : Nat := 118140960795 + 2539415 * 2 ^ 59
def prefixEnd_2539415 : Nat := 4983230072969 + 3 ^ 40 * 2539415 * 2
def baseEnd_2539415 : Nat := 1303940476237287260833949

theorem tailTrace_2539415 : CollatzResearch.WordTrace tailWord_2539415 prefixEnd_2539415 1303940476237287260833949 := by
  unfold tailWord_2539415
  simp only [CollatzResearch.WordTrace]
  refine ⟨92620074095140627398683699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61746716063427084932455799 92620074095140627398683699)
  ·
    refine ⟨138930111142710941098025549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92620074095140627398683699 138930111142710941098025549)
    ·
      refine ⟨52098791678516602911759581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138930111142710941098025549 52098791678516602911759581)
      ·
        refine ⟨19537046879443726091909843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52098791678516602911759581 19537046879443726091909843)
        ·
          refine ⟨29305570319165589137864765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19537046879443726091909843 29305570319165589137864765)
          ·
            refine ⟨10989588869687095926699287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29305570319165589137864765 10989588869687095926699287)
            ·
              refine ⟨16484383304530643890048931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10989588869687095926699287 16484383304530643890048931)
              ·
                refine ⟨24726574956795965835073397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16484383304530643890048931 24726574956795965835073397)
                ·
                  refine ⟨2318116402199621797038131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24726574956795965835073397 2318116402199621797038131)
                  ·
                    refine ⟨3477174603299432695557197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2318116402199621797038131 3477174603299432695557197)
                    ·
                      refine ⟨1303940476237287260833949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3477174603299432695557197 1303940476237287260833949)
                      ·
                        rfl

theorem cell23_2539415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_2539415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539415 prefixEnd_2539415 := by exact prefixLift 2539415
  have htrace : WordTrace (prefixWord ++ tailWord_2539415) baseStart_2539415 baseEnd_2539415 := by
    simpa [prefixWord, tailWord_2539415, baseEnd_2539415] using wordTrace_append hprefix tailTrace_2539415
  have hstable : (prefixWord ++ tailWord_2539415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539415).length < 2 ^ (prefixWord ++ tailWord_2539415).sum := by decide
  have hdescent : baseEnd_2539415 < baseStart_2539415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539472 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 3, 2, 2]
def baseStart_2539472 : Nat := 118140960795 + 2539472 * 2 ^ 59
def prefixEnd_2539472 : Nat := 4983230072969 + 3 ^ 40 * 2539472 * 2
def baseEnd_2539472 : Nat := 1303969744634593537821187

theorem tailTrace_2539472 : CollatzResearch.WordTrace tailWord_2539472 prefixEnd_2539472 1303969744634593537821187 := by
  unfold tailWord_2539472
  simp only [CollatzResearch.WordTrace]
  refine ⟨46311076527967063066754335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61748102037289417422339113 46311076527967063066754335)
  ·
    refine ⟨69466614791950594600131503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46311076527967063066754335 69466614791950594600131503)
    ·
      refine ⟨104199922187925891900197255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69466614791950594600131503 104199922187925891900197255)
      ·
        refine ⟨156299883281888837850295883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104199922187925891900197255 156299883281888837850295883)
        ·
          refine ⟨234449824922833256775443825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156299883281888837850295883 234449824922833256775443825)
          ·
            refine ⟨175837368692124942581582869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234449824922833256775443825 175837368692124942581582869)
            ·
              refine ⟨8242376657443356683511697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 175837368692124942581582869 8242376657443356683511697)
              ·
                refine ⟨6181782493082517512633773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8242376657443356683511697 6181782493082517512633773)
                ·
                  refine ⟨2318168434905944067237665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6181782493082517512633773 2318168434905944067237665)
                  ·
                    refine ⟨1738626326179458050428249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2318168434905944067237665 1738626326179458050428249)
                    ·
                      refine ⟨1303969744634593537821187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738626326179458050428249 1303969744634593537821187)
                      ·
                        rfl

theorem cell23_2539472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 3, 2, 2].length) (baseStart_2539472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539472 prefixEnd_2539472 := by exact prefixLift 2539472
  have htrace : WordTrace (prefixWord ++ tailWord_2539472) baseStart_2539472 baseEnd_2539472 := by
    simpa [prefixWord, tailWord_2539472, baseEnd_2539472] using wordTrace_append hprefix tailTrace_2539472
  have hstable : (prefixWord ++ tailWord_2539472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539472).length < 2 ^ (prefixWord ++ tailWord_2539472).sum := by decide
  have hdescent : baseEnd_2539472 < baseStart_2539472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539495 : List Nat := [1, 1, 5, 2, 3, 2, 9]
def baseStart_2539495 : Nat := 118140960795 + 2539495 * 2 ^ 59
def prefixEnd_2539495 : Nat := 4983230072969 + 3 ^ 40 * 2539495 * 2
def baseEnd_2539495 : Nat := 16098537712217863553501

theorem tailTrace_2539495 : CollatzResearch.WordTrace tailWord_2539495 prefixEnd_2539495 16098537712217863553501 := by
  unfold tailWord_2539495
  simp only [CollatzResearch.WordTrace]
  refine ⟨92622991934850801061595939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61748661289900534041063959 92622991934850801061595939)
  ·
    refine ⟨138934487902276201592393909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92622991934850801061595939 138934487902276201592393909)
    ·
      refine ⟨13025108240838393899286929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 138934487902276201592393909 13025108240838393899286929)
      ·
        refine ⟨9768831180628795424465197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13025108240838393899286929 9768831180628795424465197)
        ·
          refine ⟨3663311692735798284174449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9768831180628795424465197 3663311692735798284174449)
          ·
            refine ⟨2747483769551848713130837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3663311692735798284174449 2747483769551848713130837)
            ·
              refine ⟨16098537712217863553501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2747483769551848713130837 16098537712217863553501)
              ·
                rfl

theorem cell23_2539495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 9].length) (baseStart_2539495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539495 prefixEnd_2539495 := by exact prefixLift 2539495
  have htrace : WordTrace (prefixWord ++ tailWord_2539495) baseStart_2539495 baseEnd_2539495 := by
    simpa [prefixWord, tailWord_2539495, baseEnd_2539495] using wordTrace_append hprefix tailTrace_2539495
  have hstable : (prefixWord ++ tailWord_2539495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539495).length < 2 ^ (prefixWord ++ tailWord_2539495).sum := by decide
  have hdescent : baseEnd_2539495 < baseStart_2539495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539532 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 3, 3, 2]
def baseStart_2539532 : Nat := 118140960795 + 2539532 * 2 ^ 59
def prefixEnd_2539532 : Nat := 4983230072969 + 3 ^ 40 * 2539532 * 2
def baseEnd_2539532 : Nat := 1304000553473863303070911

theorem tailTrace_2539532 : CollatzResearch.WordTrace tailWord_2539532 prefixEnd_2539532 1304000553473863303070911 := by
  unfold tailWord_2539532
  simp only [CollatzResearch.WordTrace]
  refine ⟨46312170717858378190346425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61749560957144504253795233 46312170717858378190346425)
  ·
    refine ⟨34734128038393783642759819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46312170717858378190346425 34734128038393783642759819)
    ·
      refine ⟨52101192057590675464139729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34734128038393783642759819 52101192057590675464139729)
      ·
        refine ⟨39075894043193006598104797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52101192057590675464139729 39075894043193006598104797)
        ·
          refine ⟨14653460266197377474289299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39075894043193006598104797 14653460266197377474289299)
          ·
            refine ⟨21980190399296066211433949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14653460266197377474289299 21980190399296066211433949)
            ·
              refine ⟨8242571399736024829287731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21980190399296066211433949 8242571399736024829287731)
              ·
                refine ⟨12363857099604037243931597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8242571399736024829287731 12363857099604037243931597)
                ·
                  refine ⟨4636446412351513966474349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12363857099604037243931597 4636446412351513966474349)
                  ·
                    refine ⟨1738667404631817737427881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4636446412351513966474349 1738667404631817737427881)
                    ·
                      refine ⟨1304000553473863303070911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738667404631817737427881 1304000553473863303070911)
                      ·
                        rfl

theorem cell23_2539532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_2539532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539532 prefixEnd_2539532 := by exact prefixLift 2539532
  have htrace : WordTrace (prefixWord ++ tailWord_2539532) baseStart_2539532 baseEnd_2539532 := by
    simpa [prefixWord, tailWord_2539532, baseEnd_2539532] using wordTrace_append hprefix tailTrace_2539532
  have hstable : (prefixWord ++ tailWord_2539532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539532).length < 2 ^ (prefixWord ++ tailWord_2539532).sum := by decide
  have hdescent : baseEnd_2539532 < baseStart_2539532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539556 : List Nat := [2, 3, 1, 4, 2, 1, 2, 2, 2, 1, 3]
def baseStart_2539556 : Nat := 118140960795 + 2539556 * 2 ^ 59
def prefixEnd_2539556 : Nat := 4983230072969 + 3 ^ 40 * 2539556 * 2
def baseEnd_2539556 : Nat := 1304012877009571209170801

theorem tailTrace_2539556 : CollatzResearch.WordTrace tailWord_2539556 prefixEnd_2539556 1304012877009571209170801 := by
  unfold tailWord_2539556
  simp only [CollatzResearch.WordTrace]
  refine ⟨46312608393814904239783261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61750144525086538986377681 46312608393814904239783261)
  ·
    refine ⟨17367228147680589089918723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46312608393814904239783261 17367228147680589089918723)
    ·
      refine ⟨26050842221520883634878085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17367228147680589089918723 26050842221520883634878085)
      ·
        refine ⟨4884532916535165681539641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26050842221520883634878085 4884532916535165681539641)
        ·
          refine ⟨3663399687401374261154731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4884532916535165681539641 3663399687401374261154731)
          ·
            refine ⟨5495099531102061391732097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3663399687401374261154731 5495099531102061391732097)
            ·
              refine ⟨4121324648326546043799073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5495099531102061391732097 4121324648326546043799073)
              ·
                refine ⟨3090993486244909532849305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4121324648326546043799073 3090993486244909532849305)
                ·
                  refine ⟨2318245114683682149636979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3090993486244909532849305 2318245114683682149636979)
                  ·
                    refine ⟨3477367672025523224455469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2318245114683682149636979 3477367672025523224455469)
                    ·
                      refine ⟨1304012877009571209170801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3477367672025523224455469 1304012877009571209170801)
                      ·
                        rfl

theorem cell23_2539556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_2539556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539556 prefixEnd_2539556 := by exact prefixLift 2539556
  have htrace : WordTrace (prefixWord ++ tailWord_2539556) baseStart_2539556 baseEnd_2539556 := by
    simpa [prefixWord, tailWord_2539556, baseEnd_2539556] using wordTrace_append hprefix tailTrace_2539556
  have hstable : (prefixWord ++ tailWord_2539556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539556).length < 2 ^ (prefixWord ++ tailWord_2539556).sum := by decide
  have hdescent : baseEnd_2539556 < baseStart_2539556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539585 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 9]
def baseStart_2539585 : Nat := 118140960795 + 2539585 * 2 ^ 59
def prefixEnd_2539585 : Nat := 4983230072969 + 3 ^ 40 * 2539585 * 2
def baseEnd_2539585 : Nat := 144891974216505732856463

theorem tailTrace_2539585 : CollatzResearch.WordTrace tailWord_2539585 prefixEnd_2539585 144891974216505732856463 := by
  unfold tailWord_2539585
  simp only [CollatzResearch.WordTrace]
  refine ⟨92626274504524746432372209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61750849669683164288248139 92626274504524746432372209)
  ·
    refine ⟨69469705878393559824279157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92626274504524746432372209 69469705878393559824279157)
    ·
      refine ⟨6512784926099396233526171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69469705878393559824279157 6512784926099396233526171)
      ·
        refine ⟨9769177389149094350289257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6512784926099396233526171 9769177389149094350289257)
        ·
          refine ⟨7326883041861820762716943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9769177389149094350289257 7326883041861820762716943)
          ·
            refine ⟨10990324562792731144075415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7326883041861820762716943 10990324562792731144075415)
            ·
              refine ⟨16485486844189096716113123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10990324562792731144075415 16485486844189096716113123)
              ·
                refine ⟨24728230266283645074169685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16485486844189096716113123 24728230266283645074169685)
                ·
                  refine ⟨144891974216505732856463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24728230266283645074169685 144891974216505732856463)
                  ·
                    rfl

theorem cell23_2539585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 9].length) (baseStart_2539585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539585 prefixEnd_2539585 := by exact prefixLift 2539585
  have htrace : WordTrace (prefixWord ++ tailWord_2539585) baseStart_2539585 baseEnd_2539585 := by
    simpa [prefixWord, tailWord_2539585, baseEnd_2539585] using wordTrace_append hprefix tailTrace_2539585
  have hstable : (prefixWord ++ tailWord_2539585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539585).length < 2 ^ (prefixWord ++ tailWord_2539585).sum := by decide
  have hdescent : baseEnd_2539585 < baseStart_2539585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539612 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_2539612 : Nat := 118140960795 + 2539612 * 2 ^ 59
def prefixEnd_2539612 : Nat := 4983230072969 + 3 ^ 40 * 2539612 * 2
def baseEnd_2539612 : Nat := 1304041631926222990070543

theorem tailTrace_2539612 : CollatzResearch.WordTrace tailWord_2539612 prefixEnd_2539612 1304041631926222990070543 := by
  unfold tailWord_2539612
  simp only [CollatzResearch.WordTrace]
  refine ⟨46313629637713465021802545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61751506183617953362403393 46313629637713465021802545)
  ·
    refine ⟨34735222228285098766351909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46313629637713465021802545 34735222228285098766351909)
    ·
      refine ⟨6512854167803456018690983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34735222228285098766351909 6512854167803456018690983)
      ·
        refine ⟨9769281251705184028036475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6512854167803456018690983 9769281251705184028036475)
        ·
          refine ⟨14653921877557776042054713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9769281251705184028036475 14653921877557776042054713)
          ·
            refine ⟨10990441408168332031541035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14653921877557776042054713 10990441408168332031541035)
            ·
              refine ⟨16485662112252498047311553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10990441408168332031541035 16485662112252498047311553)
              ·
                refine ⟨12364246584189373535483665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16485662112252498047311553 12364246584189373535483665)
                ·
                  refine ⟨9273184938142030151612749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12364246584189373535483665 9273184938142030151612749)
                  ·
                    refine ⟨3477444351803261306854781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9273184938142030151612749 3477444351803261306854781)
                    ·
                      refine ⟨1304041631926222990070543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3477444351803261306854781 1304041631926222990070543)
                      ·
                        rfl

theorem cell23_2539612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_2539612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539612 prefixEnd_2539612 := by exact prefixLift 2539612
  have htrace : WordTrace (prefixWord ++ tailWord_2539612) baseStart_2539612 baseEnd_2539612 := by
    simpa [prefixWord, tailWord_2539612, baseEnd_2539612] using wordTrace_append hprefix tailTrace_2539612
  have hstable : (prefixWord ++ tailWord_2539612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539612).length < 2 ^ (prefixWord ++ tailWord_2539612).sum := by decide
  have hdescent : baseEnd_2539612 < baseStart_2539612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539613 : List Nat := [1, 4, 4, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_2539613 : Nat := 118140960795 + 2539613 * 2 ^ 59
def prefixEnd_2539613 : Nat := 4983230072969 + 3 ^ 40 * 2539613 * 2
def baseEnd_2539613 : Nat := 1304042145406877486158039

theorem tailTrace_2539613 : CollatzResearch.WordTrace tailWord_2539613 prefixEnd_2539613 1304042145406877486158039 := by
  unfold tailWord_2539613
  simp only [CollatzResearch.WordTrace]
  refine ⟨92627295748423307214391493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61751530498948871476260995 92627295748423307214391493)
  ·
    refine ⟨17367617952829370102698405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92627295748423307214391493 17367617952829370102698405)
    ·
      refine ⟨3256428366155506894255951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17367617952829370102698405 3256428366155506894255951)
      ·
        refine ⟨4884642549233260341383927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3256428366155506894255951 4884642549233260341383927)
        ·
          refine ⟨7326963823849890512075891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4884642549233260341383927 7326963823849890512075891)
          ·
            refine ⟨10990445735774835768113837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7326963823849890512075891 10990445735774835768113837)
            ·
              refine ⟨4121417150915563413042689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10990445735774835768113837 4121417150915563413042689)
              ·
                refine ⟨3091062863186672559782017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4121417150915563413042689 3091062863186672559782017)
                ·
                  refine ⟨2318297147390004419836513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3091062863186672559782017 2318297147390004419836513)
                  ·
                    refine ⟨1738722860542503314877385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2318297147390004419836513 1738722860542503314877385)
                    ·
                      refine ⟨1304042145406877486158039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738722860542503314877385 1304042145406877486158039)
                      ·
                        rfl

theorem cell23_2539613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_2539613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539613 prefixEnd_2539613 := by exact prefixLift 2539613
  have htrace : WordTrace (prefixWord ++ tailWord_2539613) baseStart_2539613 baseEnd_2539613 := by
    simpa [prefixWord, tailWord_2539613, baseEnd_2539613] using wordTrace_append hprefix tailTrace_2539613
  have hstable : (prefixWord ++ tailWord_2539613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539613).length < 2 ^ (prefixWord ++ tailWord_2539613).sum := by decide
  have hdescent : baseEnd_2539613 < baseStart_2539613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539652 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_2539652 : Nat := 118140960795 + 2539652 * 2 ^ 59
def prefixEnd_2539652 : Nat := 4983230072969 + 3 ^ 40 * 2539652 * 2
def baseEnd_2539652 : Nat := 1304062171152402833570359

theorem tailTrace_2539652 : CollatzResearch.WordTrace tailWord_2539652 prefixEnd_2539652 1304062171152402833570359 := by
  unfold tailWord_2539652
  simp only [CollatzResearch.WordTrace]
  refine ⟨46314359097641008437530605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61752478796854677916707473 46314359097641008437530605)
  ·
    refine ⟨17367884661615378164073977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46314359097641008437530605 17367884661615378164073977)
    ·
      refine ⟨13025913496211533623055483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17367884661615378164073977 13025913496211533623055483)
      ·
        refine ⟨19538870244317300434583225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13025913496211533623055483 19538870244317300434583225)
        ·
          refine ⟨14654152683237975325937419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19538870244317300434583225 14654152683237975325937419)
          ·
            refine ⟨21981229024856962988906129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14654152683237975325937419 21981229024856962988906129)
            ·
              refine ⟨16485921768642722241679597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21981229024856962988906129 16485921768642722241679597)
              ·
                refine ⟨6182220663241020840629849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16485921768642722241679597 6182220663241020840629849)
                ·
                  refine ⟨4636665497430765630472387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6182220663241020840629849 4636665497430765630472387)
                  ·
                    refine ⟨6954998246146148445708581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4636665497430765630472387 6954998246146148445708581)
                    ·
                      refine ⟨1304062171152402833570359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6954998246146148445708581 1304062171152402833570359)
                      ·
                        rfl

theorem cell23_2539652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_2539652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539652 prefixEnd_2539652 := by exact prefixLift 2539652
  have htrace : WordTrace (prefixWord ++ tailWord_2539652) baseStart_2539652 baseEnd_2539652 := by
    simpa [prefixWord, tailWord_2539652, baseEnd_2539652] using wordTrace_append hprefix tailTrace_2539652
  have hstable : (prefixWord ++ tailWord_2539652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539652).length < 2 ^ (prefixWord ++ tailWord_2539652).sum := by decide
  have hdescent : baseEnd_2539652 < baseStart_2539652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539670 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_2539670 : Nat := 118140960795 + 2539670 * 2 ^ 59
def prefixEnd_2539670 : Nat := 4983230072969 + 3 ^ 40 * 2539670 * 2
def baseEnd_2539670 : Nat := 144896823756020418127253

theorem tailTrace_2539670 : CollatzResearch.WordTrace tailWord_2539670 prefixEnd_2539670 144896823756020418127253 := by
  unfold tailWord_2539670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5789335919326050371826029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61752916472811203966144309 5789335919326050371826029)
  ·
    refine ⟨2171000969747268889434761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5789335919326050371826029 2171000969747268889434761)
    ·
      refine ⟨1628250727310451667076071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2171000969747268889434761 1628250727310451667076071)
      ·
        refine ⟨2442376090965677500614107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628250727310451667076071 2442376090965677500614107)
        ·
          refine ⟨3663564136448516250921161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2442376090965677500614107 3663564136448516250921161)
          ·
            refine ⟨2747673102336387188190871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3663564136448516250921161 2747673102336387188190871)
            ·
              refine ⟨4121509653504580782286307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2747673102336387188190871 4121509653504580782286307)
              ·
                refine ⟨6182264480256871173429461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4121509653504580782286307 6182264480256871173429461)
                ·
                  refine ⟨144896823756020418127253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6182264480256871173429461 144896823756020418127253)
                  ·
                    rfl

theorem cell23_2539670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_2539670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539670 prefixEnd_2539670 := by exact prefixLift 2539670
  have htrace : WordTrace (prefixWord ++ tailWord_2539670) baseStart_2539670 baseEnd_2539670 := by
    simpa [prefixWord, tailWord_2539670, baseEnd_2539670] using wordTrace_append hprefix tailTrace_2539670
  have hstable : (prefixWord ++ tailWord_2539670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539670).length < 2 ^ (prefixWord ++ tailWord_2539670).sum := by decide
  have hdescent : baseEnd_2539670 < baseStart_2539670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539679 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 3, 4]
def baseStart_2539679 : Nat := 118140960795 + 2539679 * 2 ^ 59
def prefixEnd_2539679 : Nat := 4983230072969 + 3 ^ 40 * 2539679 * 2
def baseEnd_2539679 : Nat := 434692011710024742644245

theorem tailTrace_2539679 : CollatzResearch.WordTrace tailWord_2539679 prefixEnd_2539679 434692011710024742644245 := by
  unfold tailWord_2539679
  simp only [CollatzResearch.WordTrace]
  refine ⟨92629702966184200486294091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61753135310789466990862727 92629702966184200486294091)
  ·
    refine ⟨138944554449276300729441137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92629702966184200486294091 138944554449276300729441137)
    ·
      refine ⟨104208415836957225547080853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138944554449276300729441137 104208415836957225547080853)
      ·
        refine ⟨4884769492357369947519415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104208415836957225547080853 4884769492357369947519415)
        ·
          refine ⟨7327154238536054921279123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4884769492357369947519415 7327154238536054921279123)
          ·
            refine ⟨10990731357804082381918685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7327154238536054921279123 10990731357804082381918685)
            ·
              refine ⟨4121524259176530893219507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10990731357804082381918685 4121524259176530893219507)
              ·
                refine ⟨6182286388764796339829261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4121524259176530893219507 6182286388764796339829261)
                ·
                  refine ⟨2318357395786798627435973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6182286388764796339829261 2318357395786798627435973)
                  ·
                    refine ⟨434692011710024742644245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2318357395786798627435973 434692011710024742644245)
                    ·
                      rfl

theorem cell23_2539679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 4].length) (baseStart_2539679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539679 prefixEnd_2539679 := by exact prefixLift 2539679
  have htrace : WordTrace (prefixWord ++ tailWord_2539679) baseStart_2539679 baseEnd_2539679 := by
    simpa [prefixWord, tailWord_2539679, baseEnd_2539679] using wordTrace_append hprefix tailTrace_2539679
  have hstable : (prefixWord ++ tailWord_2539679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539679).length < 2 ^ (prefixWord ++ tailWord_2539679).sum := by decide
  have hdescent : baseEnd_2539679 < baseStart_2539679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539729 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 2, 3, 2]
def baseStart_2539729 : Nat := 118140960795 + 2539729 * 2 ^ 59
def prefixEnd_2539729 : Nat := 4983230072969 + 3 ^ 40 * 2539729 * 2
def baseEnd_2539729 : Nat := 1304101709162799032307505

theorem tailTrace_2539729 : CollatzResearch.WordTrace tailWord_2539729 prefixEnd_2539729 1304101709162799032307505 := by
  unfold tailWord_2539729
  simp only [CollatzResearch.WordTrace]
  refine ⟨92631526616003059025614241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61754351077335372683742827 92631526616003059025614241)
  ·
    refine ⟨69473644962002294269210681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92631526616003059025614241 69473644962002294269210681)
    ·
      refine ⟨52105233721501720701908011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69473644962002294269210681 52105233721501720701908011)
      ·
        refine ⟨78157850582252581052862017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52105233721501720701908011 78157850582252581052862017)
        ·
          refine ⟨58618387936689435789646513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78157850582252581052862017 58618387936689435789646513)
          ·
            refine ⟨43963790952517076842234885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58618387936689435789646513 43963790952517076842234885)
            ·
              refine ⟨8243210803596951907919041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43963790952517076842234885 8243210803596951907919041)
              ·
                refine ⟨6182408102697713930939281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8243210803596951907919041 6182408102697713930939281)
                ·
                  refine ⟨4636806077023285448204461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6182408102697713930939281 4636806077023285448204461)
                  ·
                    refine ⟨1738802278883732043076673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4636806077023285448204461 1738802278883732043076673)
                    ·
                      refine ⟨1304101709162799032307505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738802278883732043076673 1304101709162799032307505)
                      ·
                        rfl

theorem cell23_2539729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 3, 2].length) (baseStart_2539729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539729 prefixEnd_2539729 := by exact prefixLift 2539729
  have htrace : WordTrace (prefixWord ++ tailWord_2539729) baseStart_2539729 baseEnd_2539729 := by
    simpa [prefixWord, tailWord_2539729, baseEnd_2539729] using wordTrace_append hprefix tailTrace_2539729
  have hstable : (prefixWord ++ tailWord_2539729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539729).length < 2 ^ (prefixWord ++ tailWord_2539729).sum := by decide
  have hdescent : baseEnd_2539729 < baseStart_2539729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539735 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 5, 6]
def baseStart_2539735 : Nat := 118140960795 + 2539735 * 2 ^ 59
def prefixEnd_2539735 : Nat := 4983230072969 + 3 ^ 40 * 2539735 * 2
def baseEnd_2539735 : Nat := 434701596682242002944159

theorem tailTrace_2539735 : CollatzResearch.WordTrace tailWord_2539735 prefixEnd_2539735 434701596682242002944159 := by
  unfold tailWord_2539735
  simp only [CollatzResearch.WordTrace]
  refine ⟨92631745453981322050332659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61754496969320881366888439 92631745453981322050332659)
  ·
    refine ⟨138947618180971983075498989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92631745453981322050332659 138947618180971983075498989)
    ·
      refine ⟨52105356817864493653312121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138947618180971983075498989 52105356817864493653312121)
      ·
        refine ⟨39079017613398370239984091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52105356817864493653312121 39079017613398370239984091)
        ·
          refine ⟨58618526420097555359976137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39079017613398370239984091 58618526420097555359976137)
          ·
            refine ⟨43963894815073166519982103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58618526420097555359976137 43963894815073166519982103)
            ·
              refine ⟨65945842222609749779973155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43963894815073166519982103 65945842222609749779973155)
              ·
                refine ⟨98918763333914624669959733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65945842222609749779973155 98918763333914624669959733)
                ·
                  refine ⟨9273634062554496062808725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98918763333914624669959733 9273634062554496062808725)
                  ·
                    refine ⟨434701596682242002944159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9273634062554496062808725 434701596682242002944159)
                    ·
                      rfl

theorem cell23_2539735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_2539735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539735 prefixEnd_2539735 := by exact prefixLift 2539735
  have htrace : WordTrace (prefixWord ++ tailWord_2539735) baseStart_2539735 baseEnd_2539735 := by
    simpa [prefixWord, tailWord_2539735, baseEnd_2539735] using wordTrace_append hprefix tailTrace_2539735
  have hstable : (prefixWord ++ tailWord_2539735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539735).length < 2 ^ (prefixWord ++ tailWord_2539735).sum := by decide
  have hdescent : baseEnd_2539735 < baseStart_2539735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539752 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 1, 6]
def baseStart_2539752 : Nat := 118140960795 + 2539752 * 2 ^ 59
def prefixEnd_2539752 : Nat := 4983230072969 + 3 ^ 40 * 2539752 * 2
def baseEnd_2539752 : Nat := 434704506405950814106633

theorem tailTrace_2539752 : CollatzResearch.WordTrace tailWord_2539752 prefixEnd_2539752 434704506405950814106633 := by
  unfold tailWord_2539752
  simp only [CollatzResearch.WordTrace]
  refine ⟨46316182747459866976850755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61754910329946489302467673 46316182747459866976850755)
  ·
    refine ⟨69474274121189800465276133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46316182747459866976850755 69474274121189800465276133)
    ·
      refine ⟨13026426397723087587239275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69474274121189800465276133 13026426397723087587239275)
      ·
        refine ⟨19539639596584631380858913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13026426397723087587239275 19539639596584631380858913)
        ·
          refine ⟨14654729697438473535644185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19539639596584631380858913 14654729697438473535644185)
          ·
            refine ⟨10991047273078855151733139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14654729697438473535644185 10991047273078855151733139)
            ·
              refine ⟨16486570909618282727599709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10991047273078855151733139 16486570909618282727599709)
              ·
                refine ⟨6182464091106856022849891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16486570909618282727599709 6182464091106856022849891)
                ·
                  refine ⟨9273696136660284034274837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6182464091106856022849891 9273696136660284034274837)
                  ·
                    refine ⟨434704506405950814106633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9273696136660284034274837 434704506405950814106633)
                    ·
                      rfl

theorem cell23_2539752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_2539752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539752 prefixEnd_2539752 := by exact prefixLift 2539752
  have htrace : WordTrace (prefixWord ++ tailWord_2539752) baseStart_2539752 baseEnd_2539752 := by
    simpa [prefixWord, tailWord_2539752, baseEnd_2539752] using wordTrace_append hprefix tailTrace_2539752
  have hstable : (prefixWord ++ tailWord_2539752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539752).length < 2 ^ (prefixWord ++ tailWord_2539752).sum := by decide
  have hdescent : baseEnd_2539752 < baseStart_2539752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539779 : List Nat := [1, 1, 1, 3, 2, 3, 3, 3, 1, 2, 3]
def baseStart_2539779 : Nat := 118140960795 + 2539779 * 2 ^ 59
def prefixEnd_2539779 : Nat := 4983230072969 + 3 ^ 40 * 2539779 * 2
def baseEnd_2539779 : Nat := 1304127383195523836682275

theorem tailTrace_2539779 : CollatzResearch.WordTrace tailWord_2539779 prefixEnd_2539779 1304127383195523836682275 := by
  unfold tailWord_2539779
  simp only [CollatzResearch.WordTrace]
  refine ⟨92633350265821917564934391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61755566843881278376622927 92633350265821917564934391)
  ·
    refine ⟨138950025398732876347401587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92633350265821917564934391 138950025398732876347401587)
    ·
      refine ⟨208425038098099314521102381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138950025398732876347401587 208425038098099314521102381)
      ·
        refine ⟨78159389286787242945413393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208425038098099314521102381 78159389286787242945413393)
        ·
          refine ⟨58619541965090432209060045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78159389286787242945413393 58619541965090432209060045)
          ·
            refine ⟨21982328236908912078397517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58619541965090432209060045 21982328236908912078397517)
            ·
              refine ⟨8243373088840842029399069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21982328236908912078397517 8243373088840842029399069)
              ·
                refine ⟨3091264908315315761024651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8243373088840842029399069 3091264908315315761024651)
                ·
                  refine ⟨4636897362472973641536977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091264908315315761024651 4636897362472973641536977)
                  ·
                    refine ⟨3477673021854730231152733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4636897362472973641536977 3477673021854730231152733)
                    ·
                      refine ⟨1304127383195523836682275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3477673021854730231152733 1304127383195523836682275)
                      ·
                        rfl

theorem cell23_2539779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_2539779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539779 prefixEnd_2539779 := by exact prefixLift 2539779
  have htrace : WordTrace (prefixWord ++ tailWord_2539779) baseStart_2539779 baseEnd_2539779 := by
    simpa [prefixWord, tailWord_2539779, baseEnd_2539779] using wordTrace_append hprefix tailTrace_2539779
  have hstable : (prefixWord ++ tailWord_2539779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539779).length < 2 ^ (prefixWord ++ tailWord_2539779).sum := by decide
  have hdescent : baseEnd_2539779 < baseStart_2539779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539793 : List Nat := [1, 2, 2, 1, 1, 5, 2, 4, 1, 2, 2]
def baseStart_2539793 : Nat := 118140960795 + 2539793 * 2 ^ 59
def prefixEnd_2539793 : Nat := 4983230072969 + 3 ^ 40 * 2539793 * 2
def baseEnd_2539793 : Nat := 1304134571924686781907211

theorem tailTrace_2539793 : CollatzResearch.WordTrace tailWord_2539793 prefixEnd_2539793 1304134571924686781907211 := by
  unfold tailWord_2539793
  simp only [CollatzResearch.WordTrace]
  refine ⟨92633860887771197955944033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61755907258514131970629355 92633860887771197955944033)
  ·
    refine ⟨69475395665828398466958025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92633860887771197955944033 69475395665828398466958025)
    ·
      refine ⟨52106546749371298850218519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69475395665828398466958025 52106546749371298850218519)
      ·
        refine ⟨78159820124056948275327779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52106546749371298850218519 78159820124056948275327779)
        ·
          refine ⟨117239730186085422412991669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78159820124056948275327779 117239730186085422412991669)
          ·
            refine ⟨10991224704945508351217969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117239730186085422412991669 10991224704945508351217969)
            ·
              refine ⟨8243418528709131263413477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10991224704945508351217969 8243418528709131263413477)
              ·
                refine ⟨1545640974132962111890027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8243418528709131263413477 1545640974132962111890027)
                ·
                  refine ⟨2318461461199443167835041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545640974132962111890027 2318461461199443167835041)
                  ·
                    refine ⟨1738846095899582375876281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2318461461199443167835041 1738846095899582375876281)
                    ·
                      refine ⟨1304134571924686781907211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738846095899582375876281 1304134571924686781907211)
                      ·
                        rfl

theorem cell23_2539793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 1, 2, 2].length) (baseStart_2539793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539793 prefixEnd_2539793 := by exact prefixLift 2539793
  have htrace : WordTrace (prefixWord ++ tailWord_2539793) baseStart_2539793 baseEnd_2539793 := by
    simpa [prefixWord, tailWord_2539793, baseEnd_2539793] using wordTrace_append hprefix tailTrace_2539793
  have hstable : (prefixWord ++ tailWord_2539793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539793).length < 2 ^ (prefixWord ++ tailWord_2539793).sum := by decide
  have hdescent : baseEnd_2539793 < baseStart_2539793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539795 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 1, 9]
def baseStart_2539795 : Nat := 118140960795 + 2539795 * 2 ^ 59
def prefixEnd_2539795 : Nat := 4983230072969 + 3 ^ 40 * 2539795 * 2
def baseEnd_2539795 : Nat := 434711866295331924694067

theorem tailTrace_2539795 : CollatzResearch.WordTrace tailWord_2539795 prefixEnd_2539795 434711866295331924694067 := by
  unfold tailWord_2539795
  simp only [CollatzResearch.WordTrace]
  refine ⟨92633933833763952297516839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61755955889175968198344559 92633933833763952297516839)
  ·
    refine ⟨138950900750645928446275259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92633933833763952297516839 138950900750645928446275259)
    ·
      refine ⟨208426351125968892669412889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138950900750645928446275259 208426351125968892669412889)
      ·
        refine ⟨156319763344476669502059667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208426351125968892669412889 156319763344476669502059667)
        ·
          refine ⟨234479645016715004253089501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156319763344476669502059667 234479645016715004253089501)
          ·
            refine ⟨87929866881268126594908563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234479645016715004253089501 87929866881268126594908563)
            ·
              refine ⟨131894800321902189892362845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87929866881268126594908563 131894800321902189892362845)
              ·
                refine ⟨49460550120713321209636067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131894800321902189892362845 49460550120713321209636067)
                ·
                  refine ⟨74190825181069981814454101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49460550120713321209636067 74190825181069981814454101)
                  ·
                    refine ⟨434711866295331924694067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 74190825181069981814454101 434711866295331924694067)
                    ·
                      rfl

theorem cell23_2539795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 9].length) (baseStart_2539795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539795 prefixEnd_2539795 := by exact prefixLift 2539795
  have htrace : WordTrace (prefixWord ++ tailWord_2539795) baseStart_2539795 baseEnd_2539795 := by
    simpa [prefixWord, tailWord_2539795, baseEnd_2539795] using wordTrace_append hprefix tailTrace_2539795
  have hstable : (prefixWord ++ tailWord_2539795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539795).length < 2 ^ (prefixWord ++ tailWord_2539795).sum := by decide
  have hdescent : baseEnd_2539795 < baseStart_2539795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539806 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2539806 : Nat := 118140960795 + 2539806 * 2 ^ 59
def prefixEnd_2539806 : Nat := 4983230072969 + 3 ^ 40 * 2539806 * 2
def baseEnd_2539806 : Nat := 1304141247173195231044651

theorem tailTrace_2539806 : CollatzResearch.WordTrace tailWord_2539806 prefixEnd_2539806 1304141247173195231044651 := by
  unfold tailWord_2539806
  simp only [CollatzResearch.WordTrace]
  refine ⟨11579291879590512647020909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61756223357816067450778181 11579291879590512647020909)
  ·
    refine ⟨4342234454846442242632841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11579291879590512647020909 4342234454846442242632841)
    ·
      refine ⟨3256675841134831681974631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4342234454846442242632841 3256675841134831681974631)
      ·
        refine ⟨4885013761702247522961947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3256675841134831681974631 4885013761702247522961947)
        ·
          refine ⟨7327520642553371284442921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4885013761702247522961947 7327520642553371284442921)
          ·
            refine ⟨5495640481915028463332191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7327520642553371284442921 5495640481915028463332191)
            ·
              refine ⟨8243460722872542694998287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5495640481915028463332191 8243460722872542694998287)
              ·
                refine ⟨12365191084308814042497431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8243460722872542694998287 12365191084308814042497431)
                ·
                  refine ⟨18547786626463221063746147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12365191084308814042497431 18547786626463221063746147)
                  ·
                    refine ⟨27821679939694831595619221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18547786626463221063746147 27821679939694831595619221)
                    ·
                      refine ⟨1304141247173195231044651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27821679939694831595619221 1304141247173195231044651)
                      ·
                        rfl

theorem cell23_2539806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2539806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539806 prefixEnd_2539806 := by exact prefixLift 2539806
  have htrace : WordTrace (prefixWord ++ tailWord_2539806) baseStart_2539806 baseEnd_2539806 := by
    simpa [prefixWord, tailWord_2539806, baseEnd_2539806] using wordTrace_append hprefix tailTrace_2539806
  have hstable : (prefixWord ++ tailWord_2539806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539806).length < 2 ^ (prefixWord ++ tailWord_2539806).sum := by decide
  have hdescent : baseEnd_2539806 < baseStart_2539806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539809 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_2539809 : Nat := 118140960795 + 2539809 * 2 ^ 59
def prefixEnd_2539809 : Nat := 4983230072969 + 3 ^ 40 * 2539809 * 2
def baseEnd_2539809 : Nat := 1304142787615158719307137

theorem tailTrace_2539809 : CollatzResearch.WordTrace tailWord_2539809 prefixEnd_2539809 1304142787615158719307137 := by
  unfold tailWord_2539809
  simp only [CollatzResearch.WordTrace]
  refine ⟨92634444455713232688526481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61756296303808821792350987 92634444455713232688526481)
  ·
    refine ⟨69475833341784924516394861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92634444455713232688526481 69475833341784924516394861)
    ·
      refine ⟨26053437503169346693648073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69475833341784924516394861 26053437503169346693648073)
      ·
        refine ⟨19540078127377010020236055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26053437503169346693648073 19540078127377010020236055)
        ·
          refine ⟨29310117191065515030354083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19540078127377010020236055 29310117191065515030354083)
          ·
            refine ⟨43965175786598272545531125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29310117191065515030354083 43965175786598272545531125)
            ·
              refine ⟨4121735229993588051143543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43965175786598272545531125 4121735229993588051143543)
              ·
                refine ⟨6182602844990382076715315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4121735229993588051143543 6182602844990382076715315)
                ·
                  refine ⟨9273904267485573115072973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6182602844990382076715315 9273904267485573115072973)
                  ·
                    refine ⟨3477714100307089918152365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9273904267485573115072973 3477714100307089918152365)
                    ·
                      refine ⟨1304142787615158719307137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3477714100307089918152365 1304142787615158719307137)
                      ·
                        rfl

theorem cell23_2539809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_2539809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539809 prefixEnd_2539809 := by exact prefixLift 2539809
  have htrace : WordTrace (prefixWord ++ tailWord_2539809) baseStart_2539809 baseEnd_2539809 := by
    simpa [prefixWord, tailWord_2539809, baseEnd_2539809] using wordTrace_append hprefix tailTrace_2539809
  have hstable : (prefixWord ++ tailWord_2539809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539809).length < 2 ^ (prefixWord ++ tailWord_2539809).sum := by decide
  have hdescent : baseEnd_2539809 < baseStart_2539809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539816 : List Nat := [2, 1, 5, 1, 3, 2, 2, 7]
def baseStart_2539816 : Nat := 118140960795 + 2539816 * 2 ^ 59
def prefixEnd_2539816 : Nat := 4983230072969 + 3 ^ 40 * 2539816 * 2
def baseEnd_2539816 : Nat := 48301717851101488589615

theorem tailTrace_2539816 : CollatzResearch.WordTrace tailWord_2539816 prefixEnd_2539816 48301717851101488589615 := by
  unfold tailWord_2539816
  simp only [CollatzResearch.WordTrace]
  refine ⟨46317349883343936442015651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61756466511125248589354201 46317349883343936442015651)
  ·
    refine ⟨69476024825015904663023477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46317349883343936442015651 69476024825015904663023477)
    ·
      refine ⟨6513377327345241062158451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69476024825015904663023477 6513377327345241062158451)
      ·
        refine ⟨9770065991017861593237677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6513377327345241062158451 9770065991017861593237677)
        ·
          refine ⟨3663774746631698097464129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9770065991017861593237677 3663774746631698097464129)
          ·
            refine ⟨2747831059973773573098097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3663774746631698097464129 2747831059973773573098097)
            ·
              refine ⟨2060873294980330179823573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2747831059973773573098097 2060873294980330179823573)
              ·
                refine ⟨48301717851101488589615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2060873294980330179823573 48301717851101488589615)
                ·
                  rfl

theorem cell23_2539816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 7].length) (baseStart_2539816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539816 prefixEnd_2539816 := by exact prefixLift 2539816
  have htrace : WordTrace (prefixWord ++ tailWord_2539816) baseStart_2539816 baseEnd_2539816 := by
    simpa [prefixWord, tailWord_2539816, baseEnd_2539816] using wordTrace_append hprefix tailTrace_2539816
  have hstable : (prefixWord ++ tailWord_2539816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539816).length < 2 ^ (prefixWord ++ tailWord_2539816).sum := by decide
  have hdescent : baseEnd_2539816 < baseStart_2539816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539836 : List Nat := [2, 2, 2, 2, 1, 2, 1, 5, 1, 3, 2]
def baseStart_2539836 : Nat := 118140960795 + 2539836 * 2 ^ 59
def prefixEnd_2539836 : Nat := 4983230072969 + 3 ^ 40 * 2539836 * 2
def baseEnd_2539836 : Nat := 1304156651592830113669513

theorem tailTrace_2539836 : CollatzResearch.WordTrace tailWord_2539836 prefixEnd_2539836 1304156651592830113669513 := by
  unfold tailWord_2539836
  simp only [CollatzResearch.WordTrace]
  refine ⟨46317714613307708149879681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61756952817743610866506241 46317714613307708149879681)
  ·
    refine ⟨34738285959980781112409761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46317714613307708149879681 34738285959980781112409761)
    ·
      refine ⟨26053714469985585834307321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34738285959980781112409761 26053714469985585834307321)
      ·
        refine ⟨19540285852489189375730491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26053714469985585834307321 19540285852489189375730491)
        ·
          refine ⟨29310428778733784063595737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19540285852489189375730491 29310428778733784063595737)
          ·
            refine ⟨21982821584050338047696803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29310428778733784063595737 21982821584050338047696803)
            ·
              refine ⟨32974232376075507071545205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21982821584050338047696803 32974232376075507071545205)
              ·
                refine ⟨3091334285257078787957363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32974232376075507071545205 3091334285257078787957363)
                ·
                  refine ⟨4637001427885618181936045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091334285257078787957363 4637001427885618181936045)
                  ·
                    refine ⟨1738875535457106818226017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4637001427885618181936045 1738875535457106818226017)
                    ·
                      refine ⟨1304156651592830113669513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738875535457106818226017 1304156651592830113669513)
                      ·
                        rfl

theorem cell23_2539836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_2539836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539836 prefixEnd_2539836 := by exact prefixLift 2539836
  have htrace : WordTrace (prefixWord ++ tailWord_2539836) baseStart_2539836 baseEnd_2539836 := by
    simpa [prefixWord, tailWord_2539836, baseEnd_2539836] using wordTrace_append hprefix tailTrace_2539836
  have hstable : (prefixWord ++ tailWord_2539836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539836).length < 2 ^ (prefixWord ++ tailWord_2539836).sum := by decide
  have hdescent : baseEnd_2539836 < baseStart_2539836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539844 : List Nat := [2, 3, 4, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_2539844 : Nat := 118140960795 + 2539844 * 2 ^ 59
def prefixEnd_2539844 : Nat := 4983230072969 + 3 ^ 40 * 2539844 * 2
def baseEnd_2539844 : Nat := 1304160759438066082369477

theorem tailTrace_2539844 : CollatzResearch.WordTrace tailWord_2539844 prefixEnd_2539844 1304160759438066082369477 := by
  unfold tailWord_2539844
  simp only [CollatzResearch.WordTrace]
  refine ⟨46317860505293216833025293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61757147340390955777367057 46317860505293216833025293)
  ·
    refine ⟨17369197689484956312384485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46317860505293216833025293 17369197689484956312384485)
    ·
      refine ⟨3256724566778429308572091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17369197689484956312384485 3256724566778429308572091)
      ·
        refine ⟨4885086850167643962858137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3256724566778429308572091 4885086850167643962858137)
        ·
          refine ⟨3663815137625732972143603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4885086850167643962858137 3663815137625732972143603)
          ·
            refine ⟨5495722706438599458215405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3663815137625732972143603 5495722706438599458215405)
            ·
              refine ⟨2060896014914474796830777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5495722706438599458215405 2060896014914474796830777)
              ·
                refine ⟨1545672011185856097623083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2060896014914474796830777 1545672011185856097623083)
                ·
                  refine ⟨2318508016778784146434625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545672011185856097623083 2318508016778784146434625)
                  ·
                    refine ⟨1738881012584088109825969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2318508016778784146434625 1738881012584088109825969)
                    ·
                      refine ⟨1304160759438066082369477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1738881012584088109825969 1304160759438066082369477)
                      ·
                        rfl

theorem cell23_2539844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_2539844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539844 prefixEnd_2539844 := by exact prefixLift 2539844
  have htrace : WordTrace (prefixWord ++ tailWord_2539844) baseStart_2539844 baseEnd_2539844 := by
    simpa [prefixWord, tailWord_2539844, baseEnd_2539844] using wordTrace_append hprefix tailTrace_2539844
  have hstable : (prefixWord ++ tailWord_2539844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539844).length < 2 ^ (prefixWord ++ tailWord_2539844).sum := by decide
  have hdescent : baseEnd_2539844 < baseStart_2539844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539852 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2539852 : Nat := 118140960795 + 2539852 * 2 ^ 59
def prefixEnd_2539852 : Nat := 4983230072969 + 3 ^ 40 * 2539852 * 2
def baseEnd_2539852 : Nat := 1304164867283302051069439

theorem tailTrace_2539852 : CollatzResearch.WordTrace tailWord_2539852 prefixEnd_2539852 1304164867283302051069439 := by
  unfold tailWord_2539852
  simp only [CollatzResearch.WordTrace]
  refine ⟨46318006397278725516170905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61757341863038300688227873 46318006397278725516170905)
  ·
    refine ⟨34738504797959044137128179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46318006397278725516170905 34738504797959044137128179)
    ·
      refine ⟨52107757196938566205692269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34738504797959044137128179 52107757196938566205692269)
      ·
        refine ⟨19540408948851962327134601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52107757196938566205692269 19540408948851962327134601)
        ·
          refine ⟨14655306711638971745350951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19540408948851962327134601 14655306711638971745350951)
          ·
            refine ⟨21982960067458457618026427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14655306711638971745350951 21982960067458457618026427)
            ·
              refine ⟨32974440101187686427039641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21982960067458457618026427 32974440101187686427039641)
              ·
                refine ⟨24730830075890764820279731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32974440101187686427039641 24730830075890764820279731)
                ·
                  refine ⟨37096245113836147230419597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24730830075890764820279731 37096245113836147230419597)
                  ·
                    refine ⟨13911091917688555211407349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37096245113836147230419597 13911091917688555211407349)
                    ·
                      refine ⟨1304164867283302051069439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13911091917688555211407349 1304164867283302051069439)
                      ·
                        rfl

theorem cell23_2539852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2539852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539852 prefixEnd_2539852 := by exact prefixLift 2539852
  have htrace : WordTrace (prefixWord ++ tailWord_2539852) baseStart_2539852 baseEnd_2539852 := by
    simpa [prefixWord, tailWord_2539852, baseEnd_2539852] using wordTrace_append hprefix tailTrace_2539852
  have hstable : (prefixWord ++ tailWord_2539852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539852).length < 2 ^ (prefixWord ++ tailWord_2539852).sum := by decide
  have hdescent : baseEnd_2539852 < baseStart_2539852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539860 : List Nat := [2, 4, 1, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_2539860 : Nat := 118140960795 + 2539860 * 2 ^ 59
def prefixEnd_2539860 : Nat := 4983230072969 + 3 ^ 40 * 2539860 * 2
def baseEnd_2539860 : Nat := 1304168975128538019769403

theorem tailTrace_2539860 : CollatzResearch.WordTrace tailWord_2539860 prefixEnd_2539860 1304168975128538019769403 := by
  unfold tailWord_2539860
  simp only [CollatzResearch.WordTrace]
  refine ⟨46318152289264234199316517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61757536385685645599088689 46318152289264234199316517)
  ·
    refine ⟨8684653554237043912371847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46318152289264234199316517 8684653554237043912371847)
    ·
      refine ⟨13026980331355565868557771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8684653554237043912371847 13026980331355565868557771)
      ·
        refine ⟨19540470497033348802836657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13026980331355565868557771 19540470497033348802836657)
        ·
          refine ⟨14655352872775011602127493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19540470497033348802836657 14655352872775011602127493)
          ·
            refine ⟨2747878663645314675398905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14655352872775011602127493 2747878663645314675398905)
            ·
              refine ⟨2060908997733986006549179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2747878663645314675398905 2060908997733986006549179)
              ·
                refine ⟨3091363496600979009823769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060908997733986006549179 3091363496600979009823769)
                ·
                  refine ⟨2318522622450734257367827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3091363496600979009823769 2318522622450734257367827)
                  ·
                    refine ⟨3477783933676101386051741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2318522622450734257367827 3477783933676101386051741)
                    ·
                      refine ⟨1304168975128538019769403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3477783933676101386051741 1304168975128538019769403)
                      ·
                        rfl

theorem cell23_2539860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_2539860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539860 prefixEnd_2539860 := by exact prefixLift 2539860
  have htrace : WordTrace (prefixWord ++ tailWord_2539860) baseStart_2539860 baseEnd_2539860 := by
    simpa [prefixWord, tailWord_2539860, baseEnd_2539860] using wordTrace_append hprefix tailTrace_2539860
  have hstable : (prefixWord ++ tailWord_2539860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539860).length < 2 ^ (prefixWord ++ tailWord_2539860).sum := by decide
  have hdescent : baseEnd_2539860 < baseStart_2539860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539889 : List Nat := [1, 2, 2, 2, 1, 2, 1, 7, 5]
def baseStart_2539889 : Nat := 118140960795 + 2539889 * 2 ^ 59
def prefixEnd_2539889 : Nat := 4983230072969 + 3 ^ 40 * 2539889 * 2
def baseEnd_2539889 : Nat := 144909318451946489589641

theorem tailTrace_2539889 : CollatzResearch.WordTrace tailWord_2539889 prefixEnd_2539889 144909318451946489589641 := by
  unfold tailWord_2539889
  simp only [CollatzResearch.WordTrace]
  refine ⟨92637362295423406351438721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61758241530282270900959147 92637362295423406351438721)
  ·
    refine ⟨69478021721567554763579041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92637362295423406351438721 69478021721567554763579041)
    ·
      refine ⟨52108516291175666072684281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69478021721567554763579041 52108516291175666072684281)
      ·
        refine ⟨39081387218381749554513211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52108516291175666072684281 39081387218381749554513211)
        ·
          refine ⟨58622080827572624331769817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39081387218381749554513211 58622080827572624331769817)
          ·
            refine ⟨43966560620679468248827363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58622080827572624331769817 43966560620679468248827363)
            ·
              refine ⟨65949840931019202373241045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43966560620679468248827363 65949840931019202373241045)
              ·
                refine ⟨1545699396820762555622837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 65949840931019202373241045 1545699396820762555622837)
                ·
                  refine ⟨144909318451946489589641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1545699396820762555622837 144909318451946489589641)
                  ·
                    rfl

theorem cell23_2539889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 5].length) (baseStart_2539889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539889 prefixEnd_2539889 := by exact prefixLift 2539889
  have htrace : WordTrace (prefixWord ++ tailWord_2539889) baseStart_2539889 baseEnd_2539889 := by
    simpa [prefixWord, tailWord_2539889, baseEnd_2539889] using wordTrace_append hprefix tailTrace_2539889
  have hstable : (prefixWord ++ tailWord_2539889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539889).length < 2 ^ (prefixWord ++ tailWord_2539889).sum := by decide
  have hdescent : baseEnd_2539889 < baseStart_2539889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539936 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 2, 5]
def baseStart_2539936 : Nat := 118140960795 + 2539936 * 2 ^ 59
def prefixEnd_2539936 : Nat := 4983230072969 + 3 ^ 40 * 2539936 * 2
def baseEnd_2539936 : Nat := 434735999886093240806351

theorem tailTrace_2539936 : CollatzResearch.WordTrace tailWord_2539936 prefixEnd_2539936 434735999886093240806351 := by
  unfold tailWord_2539936
  simp only [CollatzResearch.WordTrace]
  refine ⟨46319538263126566689199831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61759384350835422252266441 46319538263126566689199831)
  ·
    refine ⟨69479307394689850033799747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46319538263126566689199831 69479307394689850033799747)
    ·
      refine ⟨104218961092034775050699621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69479307394689850033799747 104218961092034775050699621)
      ·
        refine ⟨19541055204756520322006179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104218961092034775050699621 19541055204756520322006179)
        ·
          refine ⟨29311582807134780483009269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19541055204756520322006179 29311582807134780483009269)
          ·
            refine ⟨2747960888168885670282119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29311582807134780483009269 2747960888168885670282119)
            ·
              refine ⟨4121941332253328505423179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2747960888168885670282119 4121941332253328505423179)
              ·
                refine ⟨6182911998379992758134769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4121941332253328505423179 6182911998379992758134769)
                ·
                  refine ⟨4637183998784994568601077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6182911998379992758134769 4637183998784994568601077)
                  ·
                    refine ⟨434735999886093240806351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4637183998784994568601077 434735999886093240806351)
                    ·
                      rfl

theorem cell23_2539936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 2, 5].length) (baseStart_2539936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539936 prefixEnd_2539936 := by exact prefixLift 2539936
  have htrace : WordTrace (prefixWord ++ tailWord_2539936) baseStart_2539936 baseEnd_2539936 := by
    simpa [prefixWord, tailWord_2539936, baseEnd_2539936] using wordTrace_append hprefix tailTrace_2539936
  have hstable : (prefixWord ++ tailWord_2539936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539936).length < 2 ^ (prefixWord ++ tailWord_2539936).sum := by decide
  have hdescent : baseEnd_2539936 < baseStart_2539936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539939 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 4]
def baseStart_2539939 : Nat := 118140960795 + 2539939 * 2 ^ 59
def prefixEnd_2539939 : Nat := 4983230072969 + 3 ^ 40 * 2539939 * 2
def baseEnd_2539939 : Nat := 1304209540100243210681539

theorem tailTrace_2539939 : CollatzResearch.WordTrace tailWord_2539939 prefixEnd_2539939 1304209540100243210681539 := by
  unfold tailWord_2539939
  simp only [CollatzResearch.WordTrace]
  refine ⟨92639185945242264890758871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61759457296828176593839247 92639185945242264890758871)
  ·
    refine ⟨138958778917863397336138307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92639185945242264890758871 138958778917863397336138307)
    ·
      refine ⟨208438168376795096004207461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138958778917863397336138307 208438168376795096004207461)
      ·
        refine ⟨39082156570649080500788899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208438168376795096004207461 39082156570649080500788899)
        ·
          refine ⟨58623234855973620751183349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39082156570649080500788899 58623234855973620751183349)
          ·
            refine ⟨5495928267747526945423439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58623234855973620751183349 5495928267747526945423439)
            ·
              refine ⟨8243892401621290418135159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5495928267747526945423439 8243892401621290418135159)
              ·
                refine ⟨12365838602431935627202739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8243892401621290418135159 12365838602431935627202739)
                ·
                  refine ⟨18548757903647903440804109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12365838602431935627202739 18548757903647903440804109)
                  ·
                    refine ⟨6955784213867963790301541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18548757903647903440804109 6955784213867963790301541)
                    ·
                      refine ⟨1304209540100243210681539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6955784213867963790301541 1304209540100243210681539)
                      ·
                        rfl

theorem cell23_2539939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_2539939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539939 prefixEnd_2539939 := by exact prefixLift 2539939
  have htrace : WordTrace (prefixWord ++ tailWord_2539939) baseStart_2539939 baseEnd_2539939 := by
    simpa [prefixWord, tailWord_2539939, baseEnd_2539939] using wordTrace_append hprefix tailTrace_2539939
  have hstable : (prefixWord ++ tailWord_2539939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539939).length < 2 ^ (prefixWord ++ tailWord_2539939).sum := by decide
  have hdescent : baseEnd_2539939 < baseStart_2539939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2539966 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_2539966 : Nat := 118140960795 + 2539966 * 2 ^ 59
def prefixEnd_2539966 : Nat := 4983230072969 + 3 ^ 40 * 2539966 * 2
def baseEnd_2539966 : Nat := 434741134692638201681305

theorem tailTrace_2539966 : CollatzResearch.WordTrace tailWord_2539966 prefixEnd_2539966 434741134692638201681305 := by
  unfold tailWord_2539966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11580021339518056062748969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61760113810762965667994501 11580021339518056062748969)
  ·
    refine ⟨8685016004638542047061727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11580021339518056062748969 8685016004638542047061727)
    ·
      refine ⟨13027524006957813070592591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8685016004638542047061727 13027524006957813070592591)
      ·
        refine ⟨19541286010436719605888887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13027524006957813070592591 19541286010436719605888887)
        ·
          refine ⟨29311929015655079408833331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19541286010436719605888887 29311929015655079408833331)
          ·
            refine ⟨43967893523482619113249997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29311929015655079408833331 43967893523482619113249997)
            ·
              refine ⟨16487960071305982167468749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43967893523482619113249997 16487960071305982167468749)
              ·
                refine ⟨6182985026739743312800781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16487960071305982167468749 6182985026739743312800781)
                ·
                  refine ⟨2318619385027403742300293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6182985026739743312800781 2318619385027403742300293)
                  ·
                    refine ⟨434741134692638201681305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2318619385027403742300293 434741134692638201681305)
                    ·
                      rfl

theorem cell23_2539966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_2539966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2539966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2539966 prefixEnd_2539966 := by exact prefixLift 2539966
  have htrace : WordTrace (prefixWord ++ tailWord_2539966) baseStart_2539966 baseEnd_2539966 := by
    simpa [prefixWord, tailWord_2539966, baseEnd_2539966] using wordTrace_append hprefix tailTrace_2539966
  have hstable : (prefixWord ++ tailWord_2539966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2539966).length < 2 ^ (prefixWord ++ tailWord_2539966).sum := by decide
  have hdescent : baseEnd_2539966 < baseStart_2539966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2539966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540043 : List Nat := [1, 1, 1, 1, 7, 3, 1, 2, 1, 5]
def baseStart_2540043 : Nat := 118140960795 + 2540043 * 2 ^ 59
def prefixEnd_2540043 : Nat := 4983230072969 + 3 ^ 40 * 2540043 * 2
def baseEnd_2540043 : Nat := 434754314029436934593687

theorem tailTrace_2540043 : CollatzResearch.WordTrace tailWord_2540043 prefixEnd_2540043 434754314029436934593687 := by
  unfold tailWord_2540043
  simp only [CollatzResearch.WordTrace]
  refine ⟨92642979136865490652544783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61761986091243660435029855 92642979136865490652544783)
  ·
    refine ⟨138964468705298235978817175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92642979136865490652544783 138964468705298235978817175)
    ·
      refine ⟨208446703057947353968225763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138964468705298235978817175 208446703057947353968225763)
      ·
        refine ⟨312670054586921030952338645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208446703057947353968225763 312670054586921030952338645)
        ·
          refine ⟨7328204404380961662945437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 312670054586921030952338645 7328204404380961662945437)
          ·
            refine ⟨2748076651642860623604539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7328204404380961662945437 2748076651642860623604539)
            ·
              refine ⟨4122114977464290935406809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2748076651642860623604539 4122114977464290935406809)
              ·
                refine ⟨3091586233098218201555107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4122114977464290935406809 3091586233098218201555107)
                ·
                  refine ⟨4637379349647327302332661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091586233098218201555107 4637379349647327302332661)
                  ·
                    refine ⟨434754314029436934593687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4637379349647327302332661 434754314029436934593687)
                    ·
                      rfl

theorem cell23_2540043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 5].length) (baseStart_2540043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540043 prefixEnd_2540043 := by exact prefixLift 2540043
  have htrace : WordTrace (prefixWord ++ tailWord_2540043) baseStart_2540043 baseEnd_2540043 := by
    simpa [prefixWord, tailWord_2540043, baseEnd_2540043] using wordTrace_append hprefix tailTrace_2540043
  have hstable : (prefixWord ++ tailWord_2540043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540043).length < 2 ^ (prefixWord ++ tailWord_2540043).sum := by decide
  have hdescent : baseEnd_2540043 < baseStart_2540043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540056 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 1, 6]
def baseStart_2540056 : Nat := 118140960795 + 2540056 * 2 ^ 59
def prefixEnd_2540056 : Nat := 4983230072969 + 3 ^ 40 * 2540056 * 2
def baseEnd_2540056 : Nat := 434756539112273084306167

theorem tailTrace_2540056 : CollatzResearch.WordTrace tailWord_2540056 prefixEnd_2540056 434756539112273084306167 := by
  unfold tailWord_2540056
  simp only [CollatzResearch.WordTrace]
  refine ⟨46321726642909196936384011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61762302190545595915178681 46321726642909196936384011)
  ·
    refine ⟨69482589964363795404576017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46321726642909196936384011 69482589964363795404576017)
    ·
      refine ⟨52111942473272846553432013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69482589964363795404576017 52111942473272846553432013)
      ·
        refine ⟨19541978427477317457537005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52111942473272846553432013 19541978427477317457537005)
        ·
          refine ⟨7328241910303994046576377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19541978427477317457537005 7328241910303994046576377)
          ·
            refine ⟨5496181432727995534932283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7328241910303994046576377 5496181432727995534932283)
            ·
              refine ⟨8244272149091993302398425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5496181432727995534932283 8244272149091993302398425)
              ·
                refine ⟨6183204111818994976798819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8244272149091993302398425 6183204111818994976798819)
                ·
                  refine ⟨9274806167728492465198229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6183204111818994976798819 9274806167728492465198229)
                  ·
                    refine ⟨434756539112273084306167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9274806167728492465198229 434756539112273084306167)
                    ·
                      rfl

theorem cell23_2540056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_2540056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540056 prefixEnd_2540056 := by exact prefixLift 2540056
  have htrace : WordTrace (prefixWord ++ tailWord_2540056) baseStart_2540056 baseEnd_2540056 := by
    simpa [prefixWord, tailWord_2540056, baseEnd_2540056] using wordTrace_append hprefix tailTrace_2540056
  have hstable : (prefixWord ++ tailWord_2540056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540056).length < 2 ^ (prefixWord ++ tailWord_2540056).sum := by decide
  have hdescent : baseEnd_2540056 < baseStart_2540056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540074 : List Nat := [3, 1, 4, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_2540074 : Nat := 118140960795 + 2540074 * 2 ^ 59
def prefixEnd_2540074 : Nat := 4983230072969 + 3 ^ 40 * 2540074 * 2
def baseEnd_2540074 : Nat := 1304278859988600182493419

theorem tailTrace_2540074 : CollatzResearch.WordTrace tailWord_2540074 prefixEnd_2540074 1304278859988600182493419 := by
  unfold tailWord_2540074
  simp only [CollatzResearch.WordTrace]
  refine ⟨23161027449938295736730819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61762739866502121964615517 23161027449938295736730819)
  ·
    refine ⟨34741541174907443605096229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23161027449938295736730819 34741541174907443605096229)
    ·
      refine ⟨6514038970295145675955543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34741541174907443605096229 6514038970295145675955543)
      ·
        refine ⟨9771058455442718513933315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6514038970295145675955543 9771058455442718513933315)
        ·
          refine ⟨14656587683164077770899973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9771058455442718513933315 14656587683164077770899973)
          ·
            refine ⟨2748110190593264582043745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14656587683164077770899973 2748110190593264582043745)
            ·
              refine ⟨2061082642944948436532809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2748110190593264582043745 2061082642944948436532809)
              ·
                refine ⟨1545811982208711327399607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061082642944948436532809 1545811982208711327399607)
                ·
                  refine ⟨2318717973313066991099411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545811982208711327399607 2318717973313066991099411)
                  ·
                    refine ⟨3478076959969600486649117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2318717973313066991099411 3478076959969600486649117)
                    ·
                      refine ⟨1304278859988600182493419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3478076959969600486649117 1304278859988600182493419)
                      ·
                        rfl

theorem cell23_2540074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_2540074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540074 prefixEnd_2540074 := by exact prefixLift 2540074
  have htrace : WordTrace (prefixWord ++ tailWord_2540074) baseStart_2540074 baseEnd_2540074 := by
    simpa [prefixWord, tailWord_2540074, baseEnd_2540074] using wordTrace_append hprefix tailTrace_2540074
  have hstable : (prefixWord ++ tailWord_2540074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540074).length < 2 ^ (prefixWord ++ tailWord_2540074).sum := by decide
  have hdescent : baseEnd_2540074 < baseStart_2540074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540093 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_2540093 : Nat := 118140960795 + 2540093 * 2 ^ 59
def prefixEnd_2540093 : Nat := 4983230072969 + 3 ^ 40 * 2540093 * 2
def baseEnd_2540093 : Nat := 1304288616121035608155831

theorem tailTrace_2540093 : CollatzResearch.WordTrace tailWord_2540093 prefixEnd_2540093 1304288616121035608155831 := by
  unfold tailWord_2540093
  simp only [CollatzResearch.WordTrace]
  refine ⟨92644802786684349191864933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61763201857789566127909955 92644802786684349191864933)
  ·
    refine ⟨17370900522503315473474675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92644802786684349191864933 17370900522503315473474675)
    ·
      refine ⟨26056350783754973210212013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17370900522503315473474675 26056350783754973210212013)
      ·
        refine ⟨9771131543908114953829505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26056350783754973210212013 9771131543908114953829505)
        ·
          refine ⟨7328348657931086215372129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9771131543908114953829505 7328348657931086215372129)
          ·
            refine ⟨5496261493448314661529097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7328348657931086215372129 5496261493448314661529097)
            ·
              refine ⟨4122196120086235996146823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5496261493448314661529097 4122196120086235996146823)
              ·
                refine ⟨6183294180129353994220235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4122196120086235996146823 6183294180129353994220235)
                ·
                  refine ⟨9274941270194030991330353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6183294180129353994220235 9274941270194030991330353)
                  ·
                    refine ⟨6956205952645523243497765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9274941270194030991330353 6956205952645523243497765)
                    ·
                      refine ⟨1304288616121035608155831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6956205952645523243497765 1304288616121035608155831)
                      ·
                        rfl

theorem cell23_2540093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_2540093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540093 prefixEnd_2540093 := by exact prefixLift 2540093
  have htrace : WordTrace (prefixWord ++ tailWord_2540093) baseStart_2540093 baseEnd_2540093 := by
    simpa [prefixWord, tailWord_2540093, baseEnd_2540093] using wordTrace_append hprefix tailTrace_2540093
  have hstable : (prefixWord ++ tailWord_2540093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540093).length < 2 ^ (prefixWord ++ tailWord_2540093).sum := by decide
  have hdescent : baseEnd_2540093 < baseStart_2540093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540096 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 3]
def baseStart_2540096 : Nat := 118140960795 + 2540096 * 2 ^ 59
def prefixEnd_2540096 : Nat := 4983230072969 + 3 ^ 40 * 2540096 * 2
def baseEnd_2540096 : Nat := 1304290156562999096418317

theorem tailTrace_2540096 : CollatzResearch.WordTrace tailWord_2540096 prefixEnd_2540096 1304290156562999096418317 := by
  unfold tailWord_2540096
  simp only [CollatzResearch.WordTrace]
  refine ⟨46322456102836740352112071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61763274803782320469482761 46322456102836740352112071)
  ·
    refine ⟨69483684154255110528168107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46322456102836740352112071 69483684154255110528168107)
    ·
      refine ⟨104225526231382665792252161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69483684154255110528168107 104225526231382665792252161)
      ·
        refine ⟨78169144673536999344189121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104225526231382665792252161 78169144673536999344189121)
        ·
          refine ⟨58626858505152749508141841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78169144673536999344189121 58626858505152749508141841)
          ·
            refine ⟨43970143878864562131106381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58626858505152749508141841 43970143878864562131106381)
            ·
              refine ⟨16488803954574210799164893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43970143878864562131106381 16488803954574210799164893)
              ·
                refine ⟨6183301482965329049686835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16488803954574210799164893 6183301482965329049686835)
                ·
                  refine ⟨9274952224447993574530253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6183301482965329049686835 9274952224447993574530253)
                  ·
                    refine ⟨3478107084167997590448845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9274952224447993574530253 3478107084167997590448845)
                    ·
                      refine ⟨1304290156562999096418317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3478107084167997590448845 1304290156562999096418317)
                      ·
                        rfl

theorem cell23_2540096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_2540096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540096 prefixEnd_2540096 := by exact prefixLift 2540096
  have htrace : WordTrace (prefixWord ++ tailWord_2540096) baseStart_2540096 baseEnd_2540096 := by
    simpa [prefixWord, tailWord_2540096, baseEnd_2540096] using wordTrace_append hprefix tailTrace_2540096
  have hstable : (prefixWord ++ tailWord_2540096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540096).length < 2 ^ (prefixWord ++ tailWord_2540096).sum := by decide
  have hdescent : baseEnd_2540096 < baseStart_2540096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540139 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 5]
def baseStart_2540139 : Nat := 118140960795 + 2540139 * 2 ^ 59
def prefixEnd_2540139 : Nat := 4983230072969 + 3 ^ 40 * 2540139 * 2
def baseEnd_2540139 : Nat := 1304312236231142428180619

theorem tailTrace_2540139 : CollatzResearch.WordTrace tailWord_2540139 prefixEnd_2540139 1304312236231142428180619 := by
  unfold tailWord_2540139
  simp only [CollatzResearch.WordTrace]
  refine ⟨92646480544517699048039471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61764320363011799365359647 92646480544517699048039471)
  ·
    refine ⟨138969720816776548572059207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92646480544517699048039471 138969720816776548572059207)
    ·
      refine ⟨208454581225164822858088811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138969720816776548572059207 208454581225164822858088811)
      ·
        refine ⟨312681871837747234287133217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208454581225164822858088811 312681871837747234287133217)
        ·
          refine ⟨234511403878310425715349913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312681871837747234287133217 234511403878310425715349913)
          ·
            refine ⟨175883552908732819286512435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234511403878310425715349913 175883552908732819286512435)
            ·
              refine ⟨263825329363099228929768653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175883552908732819286512435 263825329363099228929768653)
              ·
                refine ⟨98934498511162210848663245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263825329363099228929768653 98934498511162210848663245)
                ·
                  refine ⟨37100436941685829068248717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98934498511162210848663245 37100436941685829068248717)
                  ·
                    refine ⟨13912663853132185900593269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37100436941685829068248717 13912663853132185900593269)
                    ·
                      refine ⟨1304312236231142428180619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13912663853132185900593269 1304312236231142428180619)
                      ·
                        rfl

theorem cell23_2540139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 5].length) (baseStart_2540139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540139 prefixEnd_2540139 := by exact prefixLift 2540139
  have htrace : WordTrace (prefixWord ++ tailWord_2540139) baseStart_2540139 baseEnd_2540139 := by
    simpa [prefixWord, tailWord_2540139, baseEnd_2540139] using wordTrace_append hprefix tailTrace_2540139
  have hstable : (prefixWord ++ tailWord_2540139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540139).length < 2 ^ (prefixWord ++ tailWord_2540139).sum := by decide
  have hdescent : baseEnd_2540139 < baseStart_2540139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540156 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_2540156 : Nat := 118140960795 + 2540156 * 2 ^ 59
def prefixEnd_2540156 : Nat := 4983230072969 + 3 ^ 40 * 2540156 * 2
def baseEnd_2540156 : Nat := 1304320965402268861668041

theorem tailTrace_2540156 : CollatzResearch.WordTrace tailWord_2540156 prefixEnd_2540156 1304320965402268861668041 := by
  unfold tailWord_2540156
  simp only [CollatzResearch.WordTrace]
  refine ⟨46323550292728055475704161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61764733723637407300938881 46323550292728055475704161)
  ·
    refine ⟨34742662719546041606778121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46323550292728055475704161 34742662719546041606778121)
    ·
      refine ⟨26056997039659531205083591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34742662719546041606778121 26056997039659531205083591)
      ·
        refine ⟨39085495559489296807625387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26056997039659531205083591 39085495559489296807625387)
        ·
          refine ⟨58628243339233945211438081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39085495559489296807625387 58628243339233945211438081)
          ·
            refine ⟨43971182504425458908578561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58628243339233945211438081 43971182504425458908578561)
            ·
              refine ⟨32978386878319094181433921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43971182504425458908578561 32978386878319094181433921)
              ·
                refine ⟨24733790158739320636075441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32978386878319094181433921 24733790158739320636075441)
                ·
                  refine ⟨18550342619054490477056581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24733790158739320636075441 18550342619054490477056581)
                  ·
                    refine ⟨3478189241072716964448109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18550342619054490477056581 3478189241072716964448109)
                    ·
                      refine ⟨1304320965402268861668041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3478189241072716964448109 1304320965402268861668041)
                      ·
                        rfl

theorem cell23_2540156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_2540156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540156 prefixEnd_2540156 := by exact prefixLift 2540156
  have htrace : WordTrace (prefixWord ++ tailWord_2540156) baseStart_2540156 baseEnd_2540156 := by
    simpa [prefixWord, tailWord_2540156, baseEnd_2540156] using wordTrace_append hprefix tailTrace_2540156
  have hstable : (prefixWord ++ tailWord_2540156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540156).length < 2 ^ (prefixWord ++ tailWord_2540156).sum := by decide
  have hdescent : baseEnd_2540156 < baseStart_2540156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540157 : List Nat := [1, 4, 1, 1, 5, 1, 2, 2, 1, 3, 2]
def baseStart_2540157 : Nat := 118140960795 + 2540157 * 2 ^ 59
def prefixEnd_2540157 : Nat := 4983230072969 + 3 ^ 40 * 2540157 * 2
def baseEnd_2540157 : Nat := 1304321478882923357755537

theorem tailTrace_2540157 : CollatzResearch.WordTrace tailWord_2540157 prefixEnd_2540157 1304321478882923357755537 := by
  unfold tailWord_2540157
  simp only [CollatzResearch.WordTrace]
  refine ⟨92647137058452488122194725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61764758038968325414796483 92647137058452488122194725)
  ·
    refine ⟨17371338198459841522911511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92647137058452488122194725 17371338198459841522911511)
    ·
      refine ⟨26057007297689762284367267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17371338198459841522911511 26057007297689762284367267)
      ·
        refine ⟨39085510946534643426550901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26057007297689762284367267 39085510946534643426550901)
        ·
          refine ⟨3664266651237622821239147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39085510946534643426550901 3664266651237622821239147)
          ·
            refine ⟨5496399976856434231858721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3664266651237622821239147 5496399976856434231858721)
            ·
              refine ⟨4122299982642325673894041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5496399976856434231858721 4122299982642325673894041)
              ·
                refine ⟨3091724986981744255420531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4122299982642325673894041 3091724986981744255420531)
                ·
                  refine ⟨4637587480472616383130797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3091724986981744255420531 4637587480472616383130797)
                  ·
                    refine ⟨1739095305177231143674049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4637587480472616383130797 1739095305177231143674049)
                    ·
                      refine ⟨1304321478882923357755537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1739095305177231143674049 1304321478882923357755537)
                      ·
                        rfl

theorem cell23_2540157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_2540157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540157 prefixEnd_2540157 := by exact prefixLift 2540157
  have htrace : WordTrace (prefixWord ++ tailWord_2540157) baseStart_2540157 baseEnd_2540157 := by
    simpa [prefixWord, tailWord_2540157, baseEnd_2540157] using wordTrace_append hprefix tailTrace_2540157
  have hstable : (prefixWord ++ tailWord_2540157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540157).length < 2 ^ (prefixWord ++ tailWord_2540157).sum := by decide
  have hdescent : baseEnd_2540157 < baseStart_2540157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540159 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 9]
def baseStart_2540159 : Nat := 118140960795 + 2540159 * 2 ^ 59
def prefixEnd_2540159 : Nat := 4983230072969 + 3 ^ 40 * 2540159 * 2
def baseEnd_2540159 : Nat := 144924722871581372214503

theorem tailTrace_2540159 : CollatzResearch.WordTrace tailWord_2540159 prefixEnd_2540159 144924722871581372214503 := by
  unfold tailWord_2540159
  simp only [CollatzResearch.WordTrace]
  refine ⟨92647210004445242463767531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61764806669630161642511687 92647210004445242463767531)
  ·
    refine ⟨138970815006667863695651297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92647210004445242463767531 138970815006667863695651297)
    ·
      refine ⟨104228111255000897771738473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138970815006667863695651297 104228111255000897771738473)
      ·
        refine ⟨78171083441250673328803855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104228111255000897771738473 78171083441250673328803855)
        ·
          refine ⟨117256625161876009993205783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78171083441250673328803855 117256625161876009993205783)
          ·
            refine ⟨175884937742814014989808675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117256625161876009993205783 175884937742814014989808675)
            ·
              refine ⟨263827406614221022484713013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175884937742814014989808675 263827406614221022484713013)
              ·
                refine ⟨24733819370083220857941845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 263827406614221022484713013 24733819370083220857941845)
                ·
                  refine ⟨144924722871581372214503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24733819370083220857941845 144924722871581372214503)
                  ·
                    rfl

theorem cell23_2540159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 9].length) (baseStart_2540159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540159 prefixEnd_2540159 := by exact prefixLift 2540159
  have htrace : WordTrace (prefixWord ++ tailWord_2540159) baseStart_2540159 baseEnd_2540159 := by
    simpa [prefixWord, tailWord_2540159, baseEnd_2540159] using wordTrace_append hprefix tailTrace_2540159
  have hstable : (prefixWord ++ tailWord_2540159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540159).length < 2 ^ (prefixWord ++ tailWord_2540159).sum := by decide
  have hdescent : baseEnd_2540159 < baseStart_2540159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540223 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 2, 5]
def baseStart_2540223 : Nat := 118140960795 + 2540223 * 2 ^ 59
def prefixEnd_2540223 : Nat := 4983230072969 + 3 ^ 40 * 2540223 * 2
def baseEnd_2540223 : Nat := 434785122868706699843411

theorem tailTrace_2540223 : CollatzResearch.WordTrace tailWord_2540223 prefixEnd_2540223 434785122868706699843411 := by
  unfold tailWord_2540223
  simp only [CollatzResearch.WordTrace]
  refine ⟨92649544276213381394097323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61766362850808920929398215 92649544276213381394097323)
  ·
    refine ⟨138974316414320072091145985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92649544276213381394097323 138974316414320072091145985)
    ·
      refine ⟨104230737310740054068359489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138974316414320072091145985 104230737310740054068359489)
      ·
        refine ⟨78173052983055040551269617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104230737310740054068359489 78173052983055040551269617)
        ·
          refine ⟨58629789737291280413452213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78173052983055040551269617 58629789737291280413452213)
          ·
            refine ⟨5496542787871057538761145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58629789737291280413452213 5496542787871057538761145)
            ·
              refine ⟨4122407090903293154070859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5496542787871057538761145 4122407090903293154070859)
              ·
                refine ⟨6183610636354939731106289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4122407090903293154070859 6183610636354939731106289)
                ·
                  refine ⟨4637707977266204798329717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6183610636354939731106289 4637707977266204798329717)
                  ·
                    refine ⟨434785122868706699843411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4637707977266204798329717 434785122868706699843411)
                    ·
                      rfl

theorem cell23_2540223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 5].length) (baseStart_2540223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540223 prefixEnd_2540223 := by exact prefixLift 2540223
  have htrace : WordTrace (prefixWord ++ tailWord_2540223) baseStart_2540223 baseEnd_2540223 := by
    simpa [prefixWord, tailWord_2540223, baseEnd_2540223] using wordTrace_append hprefix tailTrace_2540223
  have hstable : (prefixWord ++ tailWord_2540223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540223).length < 2 ^ (prefixWord ++ tailWord_2540223).sum := by decide
  have hdescent : baseEnd_2540223 < baseStart_2540223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540244 : List Nat := [2, 4, 1, 3, 2, 2, 2, 2, 5]
def baseStart_2540244 : Nat := 118140960795 + 2540244 * 2 ^ 59
def prefixEnd_2540244 : Nat := 4983230072969 + 3 ^ 40 * 2540244 * 2
def baseEnd_2540244 : Nat := 144929572411096057485293

theorem tailTrace_2540244 : CollatzResearch.WordTrace tailWord_2540244 prefixEnd_2540244 144929572411096057485293 := by
  unfold tailWord_2540244
  simp only [CollatzResearch.WordTrace]
  refine ⟨46325155104568650990305893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61766873472758201320407857 46325155104568650990305893)
  ·
    refine ⟨8685966582106622060682355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46325155104568650990305893 8685966582106622060682355)
    ·
      refine ⟨13028949873159933091023533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8685966582106622060682355 13028949873159933091023533)
      ·
        refine ⟨4885856202434974909133825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13028949873159933091023533 4885856202434974909133825)
        ·
          refine ⟨3664392151826231181850369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4885856202434974909133825 3664392151826231181850369)
          ·
            refine ⟨2748294113869673386387777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3664392151826231181850369 2748294113869673386387777)
            ·
              refine ⟨2061220585402255039790833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2748294113869673386387777 2061220585402255039790833)
              ·
                refine ⟨1545915439051691279843125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061220585402255039790833 1545915439051691279843125)
                ·
                  refine ⟨144929572411096057485293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1545915439051691279843125 144929572411096057485293)
                  ·
                    rfl

theorem cell23_2540244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_2540244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540244 prefixEnd_2540244 := by exact prefixLift 2540244
  have htrace : WordTrace (prefixWord ++ tailWord_2540244) baseStart_2540244 baseEnd_2540244 := by
    simpa [prefixWord, tailWord_2540244, baseEnd_2540244] using wordTrace_append hprefix tailTrace_2540244
  have hstable : (prefixWord ++ tailWord_2540244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540244).length < 2 ^ (prefixWord ++ tailWord_2540244).sum := by decide
  have hdescent : baseEnd_2540244 < baseStart_2540244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540256 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 4]
def baseStart_2540256 : Nat := 118140960795 + 2540256 * 2 ^ 59
def prefixEnd_2540256 : Nat := 4983230072969 + 3 ^ 40 * 2540256 * 2
def baseEnd_2540256 : Nat := 1304372313467718470417581

theorem tailTrace_2540256 : CollatzResearch.WordTrace tailWord_2540256 prefixEnd_2540256 1304372313467718470417581 := by
  unfold tailWord_2540256
  simp only [CollatzResearch.WordTrace]
  refine ⟨46325373942546914015024311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61767165256729218686699081 46325373942546914015024311)
  ·
    refine ⟨69488060913820371022536467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46325373942546914015024311 69488060913820371022536467)
    ·
      refine ⟨104232091370730556533804701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69488060913820371022536467 104232091370730556533804701)
      ·
        refine ⟨39087034264023958700176763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104232091370730556533804701 39087034264023958700176763)
        ·
          refine ⟨58630551396035938050265145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39087034264023958700176763 58630551396035938050265145)
          ·
            refine ⟨43972913547026953537698859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58630551396035938050265145 43972913547026953537698859)
            ·
              refine ⟨65959370320540430306548289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43972913547026953537698859 65959370320540430306548289)
              ·
                refine ⟨49469527740405322729911217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65959370320540430306548289 49469527740405322729911217)
                ·
                  refine ⟨37102145805303992047433413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49469527740405322729911217 37102145805303992047433413)
                  ·
                    refine ⟨6956652338494498508893765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37102145805303992047433413 6956652338494498508893765)
                    ·
                      refine ⟨1304372313467718470417581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6956652338494498508893765 1304372313467718470417581)
                      ·
                        rfl

theorem cell23_2540256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_2540256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540256 prefixEnd_2540256 := by exact prefixLift 2540256
  have htrace : WordTrace (prefixWord ++ tailWord_2540256) baseStart_2540256 baseEnd_2540256 := by
    simpa [prefixWord, tailWord_2540256, baseEnd_2540256] using wordTrace_append hprefix tailTrace_2540256
  have hstable : (prefixWord ++ tailWord_2540256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540256).length < 2 ^ (prefixWord ++ tailWord_2540256).sum := by decide
  have hdescent : baseEnd_2540256 < baseStart_2540256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540260 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 2, 4, 2]
def baseStart_2540260 : Nat := 118140960795 + 2540260 * 2 ^ 59
def prefixEnd_2540260 : Nat := 4983230072969 + 3 ^ 40 * 2540260 * 2
def baseEnd_2540260 : Nat := 1304374367390336454767563

theorem tailTrace_2540260 : CollatzResearch.WordTrace tailWord_2540260 prefixEnd_2540260 1304374367390336454767563 := by
  unfold tailWord_2540260
  simp only [CollatzResearch.WordTrace]
  refine ⟨46325446888539668356597117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61767262518052891142129489 46325446888539668356597117)
  ·
    refine ⟨17372042583202375633723919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46325446888539668356597117 17372042583202375633723919)
    ·
      refine ⟨26058063874803563450585879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17372042583202375633723919 26058063874803563450585879)
      ·
        refine ⟨39087095812205345175878819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26058063874803563450585879 39087095812205345175878819)
        ·
          refine ⟨58630643718308017763818229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39087095812205345175878819 58630643718308017763818229)
          ·
            refine ⟨5496622848591376665357959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58630643718308017763818229 5496622848591376665357959)
            ·
              refine ⟨8244934272887064998036939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5496622848591376665357959 8244934272887064998036939)
              ·
                refine ⟨12367401409330597497055409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8244934272887064998036939 12367401409330597497055409)
                ·
                  refine ⟨9275551056997948122791557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12367401409330597497055409 9275551056997948122791557)
                  ·
                    refine ⟨1739165823187115273023417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9275551056997948122791557 1739165823187115273023417)
                    ·
                      refine ⟨1304374367390336454767563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1739165823187115273023417 1304374367390336454767563)
                      ·
                        rfl

theorem cell23_2540260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_2540260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540260 prefixEnd_2540260 := by exact prefixLift 2540260
  have htrace : WordTrace (prefixWord ++ tailWord_2540260) baseStart_2540260 baseEnd_2540260 := by
    simpa [prefixWord, tailWord_2540260, baseEnd_2540260] using wordTrace_append hprefix tailTrace_2540260
  have hstable : (prefixWord ++ tailWord_2540260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540260).length < 2 ^ (prefixWord ++ tailWord_2540260).sum := by decide
  have hdescent : baseEnd_2540260 < baseStart_2540260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540266 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 10]
def baseStart_2540266 : Nat := 118140960795 + 2540266 * 2 ^ 59
def prefixEnd_2540266 : Nat := 4983230072969 + 3 ^ 40 * 2540266 * 2
def baseEnd_2540266 : Nat := 144930827586029270143615

theorem tailTrace_2540266 : CollatzResearch.WordTrace tailWord_2540266 prefixEnd_2540266 144930827586029270143615 := by
  unfold tailWord_2540266
  simp only [CollatzResearch.WordTrace]
  refine ⟨23162778153764399934478163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61767408410038399825275101 23162778153764399934478163)
  ·
    refine ⟨34744167230646599901717245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23162778153764399934478163 34744167230646599901717245)
    ·
      refine ⟨13029062711492474963143967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34744167230646599901717245 13029062711492474963143967)
      ·
        refine ⟨19543594067238712444715951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13029062711492474963143967 19543594067238712444715951)
        ·
          refine ⟨29315391100858068667073927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19543594067238712444715951 29315391100858068667073927)
          ·
            refine ⟨43973086651287103000610891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29315391100858068667073927 43973086651287103000610891)
            ·
              refine ⟨65959629976930654500916337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43973086651287103000610891 65959629976930654500916337)
              ·
                refine ⟨49469722482697990875687253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65959629976930654500916337 49469722482697990875687253)
                ·
                  refine ⟨144930827586029270143615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 49469722482697990875687253 144930827586029270143615)
                  ·
                    rfl

theorem cell23_2540266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_2540266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540266 prefixEnd_2540266 := by exact prefixLift 2540266
  have htrace : WordTrace (prefixWord ++ tailWord_2540266) baseStart_2540266 baseEnd_2540266 := by
    simpa [prefixWord, tailWord_2540266, baseEnd_2540266] using wordTrace_append hprefix tailTrace_2540266
  have hstable : (prefixWord ++ tailWord_2540266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540266).length < 2 ^ (prefixWord ++ tailWord_2540266).sum := by decide
  have hdescent : baseEnd_2540266 < baseStart_2540266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540270 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_2540270 : Nat := 118140960795 + 2540270 * 2 ^ 59
def prefixEnd_2540270 : Nat := 4983230072969 + 3 ^ 40 * 2540270 * 2
def baseEnd_2540270 : Nat := 434793167398960471880839

theorem tailTrace_2540270 : CollatzResearch.WordTrace tailWord_2540270 prefixEnd_2540270 434793167398960471880839 := by
  unfold tailWord_2540270
  simp only [CollatzResearch.WordTrace]
  refine ⟨11581407313380388552632283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61767505671362072280705509 11581407313380388552632283)
  ·
    refine ⟨17372110970070582828948425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11581407313380388552632283 17372110970070582828948425)
    ·
      refine ⟨13029083227552937121711319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17372110970070582828948425 13029083227552937121711319)
      ·
        refine ⟨19543624841329405682566979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13029083227552937121711319 19543624841329405682566979)
        ·
          refine ⟨29315437261994108523850469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19543624841329405682566979 29315437261994108523850469)
          ·
            refine ⟨5496644486623895348221963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29315437261994108523850469 5496644486623895348221963)
            ·
              refine ⟨8244966729935843022332945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5496644486623895348221963 8244966729935843022332945)
              ·
                refine ⟨6183725047451882266749709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8244966729935843022332945 6183725047451882266749709)
                ·
                  refine ⟨2318896892794455850031141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6183725047451882266749709 2318896892794455850031141)
                  ·
                    refine ⟨434793167398960471880839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2318896892794455850031141 434793167398960471880839)
                    ·
                      rfl

theorem cell23_2540270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_2540270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540270 prefixEnd_2540270 := by exact prefixLift 2540270
  have htrace : WordTrace (prefixWord ++ tailWord_2540270) baseStart_2540270 baseEnd_2540270 := by
    simpa [prefixWord, tailWord_2540270, baseEnd_2540270] using wordTrace_append hprefix tailTrace_2540270
  have hstable : (prefixWord ++ tailWord_2540270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540270).length < 2 ^ (prefixWord ++ tailWord_2540270).sum := by decide
  have hdescent : baseEnd_2540270 < baseStart_2540270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540320 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 1, 5, 2]
def baseStart_2540320 : Nat := 118140960795 + 2540320 * 2 ^ 59
def prefixEnd_2540320 : Nat := 4983230072969 + 3 ^ 40 * 2540320 * 2
def baseEnd_2540320 : Nat := 1304405176229606220017287

theorem tailTrace_2540320 : CollatzResearch.WordTrace tailWord_2540320 prefixEnd_2540320 1304405176229606220017287 := by
  unfold tailWord_2540320
  simp only [CollatzResearch.WordTrace]
  refine ⟨46326541078430983480189207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61768721437907977973585609 46326541078430983480189207)
  ·
    refine ⟨69489811617646475220283811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46326541078430983480189207 69489811617646475220283811)
    ·
      refine ⟨104234717426469712830425717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69489811617646475220283811 104234717426469712830425717)
      ·
        refine ⟨9772004758731535577852411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104234717426469712830425717 9772004758731535577852411)
        ·
          refine ⟨14658007138097303366778617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9772004758731535577852411 14658007138097303366778617)
          ·
            refine ⟨10993505353572977525083963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14658007138097303366778617 10993505353572977525083963)
            ·
              refine ⟨16490258030359466287625945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10993505353572977525083963 16490258030359466287625945)
              ·
                refine ⟨12367693522769599715719459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16490258030359466287625945 12367693522769599715719459)
                ·
                  refine ⟨18551540284154399573579189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12367693522769599715719459 18551540284154399573579189)
                  ·
                    refine ⟨1739206901639474960023049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18551540284154399573579189 1739206901639474960023049)
                    ·
                      refine ⟨1304405176229606220017287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1739206901639474960023049 1304405176229606220017287)
                      ·
                        rfl

theorem cell23_2540320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_2540320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540320 prefixEnd_2540320 := by exact prefixLift 2540320
  have htrace : WordTrace (prefixWord ++ tailWord_2540320) baseStart_2540320 baseEnd_2540320 := by
    simpa [prefixWord, tailWord_2540320, baseEnd_2540320] using wordTrace_append hprefix tailTrace_2540320
  have hstable : (prefixWord ++ tailWord_2540320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540320).length < 2 ^ (prefixWord ++ tailWord_2540320).sum := by decide
  have hdescent : baseEnd_2540320 < baseStart_2540320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540343 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 6, 4]
def baseStart_2540343 : Nat := 118140960795 + 2540343 * 2 ^ 59
def prefixEnd_2540343 : Nat := 4983230072969 + 3 ^ 40 * 2540343 * 2
def baseEnd_2540343 : Nat := 434805662094886543343227

theorem tailTrace_2540343 : CollatzResearch.WordTrace tailWord_2540343 prefixEnd_2540343 434805662094886543343227 := by
  unfold tailWord_2540343
  simp only [CollatzResearch.WordTrace]
  refine ⟨92653921035778641888465683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61769280690519094592310455 92653921035778641888465683)
  ·
    refine ⟨138980881553667962832698525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92653921035778641888465683 138980881553667962832698525)
    ·
      refine ⟨52117830582625486062261947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138980881553667962832698525 52117830582625486062261947)
      ·
        refine ⟨78176745873938229093392921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52117830582625486062261947 78176745873938229093392921)
        ·
          refine ⟨58632559405453671820044691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78176745873938229093392921 58632559405453671820044691)
          ·
            refine ⟨87948839108180507730067037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58632559405453671820044691 87948839108180507730067037)
            ·
              refine ⟨32980814665567690398775139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87948839108180507730067037 32980814665567690398775139)
              ·
                refine ⟨49471221998351535598162709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32980814665567690398775139 49471221998351535598162709)
                ·
                  refine ⟨2318963531172728231163877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49471221998351535598162709 2318963531172728231163877)
                  ·
                    refine ⟨434805662094886543343227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2318963531172728231163877 434805662094886543343227)
                    ·
                      rfl

theorem cell23_2540343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_2540343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540343 prefixEnd_2540343 := by exact prefixLift 2540343
  have htrace : WordTrace (prefixWord ++ tailWord_2540343) baseStart_2540343 baseEnd_2540343 := by
    simpa [prefixWord, tailWord_2540343, baseEnd_2540343] using wordTrace_append hprefix tailTrace_2540343
  have hstable : (prefixWord ++ tailWord_2540343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540343).length < 2 ^ (prefixWord ++ tailWord_2540343).sum := by decide
  have hdescent : baseEnd_2540343 < baseStart_2540343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540360 : List Nat := [2, 1, 3, 1, 1, 3, 2, 4, 2, 4]
def baseStart_2540360 : Nat := 118140960795 + 2540360 * 2 ^ 59
def prefixEnd_2540360 : Nat := 4983230072969 + 3 ^ 40 * 2540360 * 2
def baseEnd_2540360 : Nat := 434808571818595354505701

theorem tailTrace_2540360 : CollatzResearch.WordTrace tailWord_2540360 prefixEnd_2540360 434808571818595354505701 := by
  unfold tailWord_2540360
  simp only [CollatzResearch.WordTrace]
  refine ⟨46327270538358526895917267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61769694051144702527889689 46327270538358526895917267)
  ·
    refine ⟨69490905807537790343875901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46327270538358526895917267 69490905807537790343875901)
    ·
      refine ⟨26059089677826671378953463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69490905807537790343875901 26059089677826671378953463)
      ·
        refine ⟨39088634516740007068430195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26059089677826671378953463 39088634516740007068430195)
        ·
          refine ⟨58632951775110010602645293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39088634516740007068430195 58632951775110010602645293)
          ·
            refine ⟨21987356915666253975991985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58632951775110010602645293 21987356915666253975991985)
            ·
              refine ⟨16490517686749690481993989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21987356915666253975991985 16490517686749690481993989)
              ·
                refine ⟨3091972066265566965373873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16490517686749690481993989 3091972066265566965373873)
                ·
                  refine ⟨2318979049699175224030405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3091972066265566965373873 2318979049699175224030405)
                  ·
                    refine ⟨434808571818595354505701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2318979049699175224030405 434808571818595354505701)
                    ·
                      rfl

theorem cell23_2540360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_2540360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540360 prefixEnd_2540360 := by exact prefixLift 2540360
  have htrace : WordTrace (prefixWord ++ tailWord_2540360) baseStart_2540360 baseEnd_2540360 := by
    simpa [prefixWord, tailWord_2540360, baseEnd_2540360] using wordTrace_append hprefix tailTrace_2540360
  have hstable : (prefixWord ++ tailWord_2540360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540360).length < 2 ^ (prefixWord ++ tailWord_2540360).sum := by decide
  have hdescent : baseEnd_2540360 < baseStart_2540360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540370 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_2540370 : Nat := 118140960795 + 2540370 * 2 ^ 59
def prefixEnd_2540370 : Nat := 4983230072969 + 3 ^ 40 * 2540370 * 2
def baseEnd_2540370 : Nat := 1304430850262331024392057

theorem tailTrace_2540370 : CollatzResearch.WordTrace tailWord_2540370 prefixEnd_2540370 1304430850262331024392057 := by
  unfold tailWord_2540370
  simp only [CollatzResearch.WordTrace]
  refine ⟨23163726451670206374924641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61769937204453883666465709 23163726451670206374924641)
  ·
    refine ⟨17372794838752654781193481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23163726451670206374924641 17372794838752654781193481)
    ·
      refine ⟨13029596129064491085895111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17372794838752654781193481 13029596129064491085895111)
      ·
        refine ⟨19544394193596736628842667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13029596129064491085895111 19544394193596736628842667)
        ·
          refine ⟨29316591290395104943264001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19544394193596736628842667 29316591290395104943264001)
          ·
            refine ⟨21987443467796328707448001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29316591290395104943264001 21987443467796328707448001)
            ·
              refine ⟨16490582600847246530586001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21987443467796328707448001 16490582600847246530586001)
              ·
                refine ⟨12367936950635434897939501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16490582600847246530586001 12367936950635434897939501)
                ·
                  refine ⟨4637976356488288086727313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12367936950635434897939501 4637976356488288086727313)
                  ·
                    refine ⟨3478482267366216065045485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4637976356488288086727313 3478482267366216065045485)
                    ·
                      refine ⟨1304430850262331024392057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3478482267366216065045485 1304430850262331024392057)
                      ·
                        rfl

theorem cell23_2540370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_2540370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540370 prefixEnd_2540370 := by exact prefixLift 2540370
  have htrace : WordTrace (prefixWord ++ tailWord_2540370) baseStart_2540370 baseEnd_2540370 := by
    simpa [prefixWord, tailWord_2540370, baseEnd_2540370] using wordTrace_append hprefix tailTrace_2540370
  have hstable : (prefixWord ++ tailWord_2540370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540370).length < 2 ^ (prefixWord ++ tailWord_2540370).sum := by decide
  have hdescent : baseEnd_2540370 < baseStart_2540370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540373 : List Nat := [1, 3, 2, 2, 2, 1, 4, 8]
def baseStart_2540373 : Nat := 118140960795 + 2540373 * 2 ^ 59
def prefixEnd_2540373 : Nat := 4983230072969 + 3 ^ 40 * 2540373 * 2
def baseEnd_2540373 : Nat := 48312310766825722690909

theorem tailTrace_2540373 : CollatzResearch.WordTrace tailWord_2540373 prefixEnd_2540373 48312310766825722690909 := by
  unfold tailWord_2540373
  simp only [CollatzResearch.WordTrace]
  refine ⟨92655015225669957012057773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61770010150446638008038515 92655015225669957012057773)
  ·
    refine ⟨34745630709626233879521665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92655015225669957012057773 34745630709626233879521665)
    ·
      refine ⟨26059223032219675409641249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34745630709626233879521665 26059223032219675409641249)
      ·
        refine ⟨19544417274164756557230937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26059223032219675409641249 19544417274164756557230937)
        ·
          refine ⟨14658312955623567417923203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19544417274164756557230937 14658312955623567417923203)
          ·
            refine ⟨21987469433435351126884805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14658312955623567417923203 21987469433435351126884805)
            ·
              refine ⟨4122650518769128336290901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21987469433435351126884805 4122650518769128336290901)
              ·
                refine ⟨48312310766825722690909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4122650518769128336290901 48312310766825722690909)
                ·
                  rfl

theorem cell23_2540373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 8].length) (baseStart_2540373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540373 prefixEnd_2540373 := by exact prefixLift 2540373
  have htrace : WordTrace (prefixWord ++ tailWord_2540373) baseStart_2540373 baseEnd_2540373 := by
    simpa [prefixWord, tailWord_2540373, baseEnd_2540373] using wordTrace_append hprefix tailTrace_2540373
  have hstable : (prefixWord ++ tailWord_2540373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540373).length < 2 ^ (prefixWord ++ tailWord_2540373).sum := by decide
  have hdescent : baseEnd_2540373 < baseStart_2540373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540377 : List Nat := [1, 2, 1, 2, 2, 4, 4, 1, 2, 4]
def baseStart_2540377 : Nat := 118140960795 + 2540377 * 2 ^ 59
def prefixEnd_2540377 : Nat := 4983230072969 + 3 ^ 40 * 2540377 * 2
def baseEnd_2540377 : Nat := 434811481542304165668175

theorem tailTrace_2540377 : CollatzResearch.WordTrace tailWord_2540377 prefixEnd_2540377 434811481542304165668175 := by
  unfold tailWord_2540377
  simp only [CollatzResearch.WordTrace]
  refine ⟨92655161117655465695203385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61770107411770310463468923 92655161117655465695203385)
  ·
    refine ⟨69491370838241599271402539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92655161117655465695203385 69491370838241599271402539)
    ·
      refine ⟨104237056257362398907103809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69491370838241599271402539 104237056257362398907103809)
      ·
        refine ⟨78177792193021799180327857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104237056257362398907103809 78177792193021799180327857)
        ·
          refine ⟨58633344144766349385245893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78177792193021799180327857 58633344144766349385245893)
          ·
            refine ⟨10993752027143690509733605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58633344144766349385245893 10993752027143690509733605)
            ·
              refine ⟨2061328505089441970575051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10993752027143690509733605 2061328505089441970575051)
              ·
                refine ⟨3091992757634162955862577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061328505089441970575051 3091992757634162955862577)
                ·
                  refine ⟨2318994568225622216896933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3091992757634162955862577 2318994568225622216896933)
                  ·
                    refine ⟨434811481542304165668175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2318994568225622216896933 434811481542304165668175)
                    ·
                      rfl

theorem cell23_2540377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 2, 4].length) (baseStart_2540377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540377 prefixEnd_2540377 := by exact prefixLift 2540377
  have htrace : WordTrace (prefixWord ++ tailWord_2540377) baseStart_2540377 baseEnd_2540377 := by
    simpa [prefixWord, tailWord_2540377, baseEnd_2540377] using wordTrace_append hprefix tailTrace_2540377
  have hstable : (prefixWord ++ tailWord_2540377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540377).length < 2 ^ (prefixWord ++ tailWord_2540377).sum := by decide
  have hdescent : baseEnd_2540377 < baseStart_2540377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540380 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2540380 : Nat := 118140960795 + 2540380 * 2 ^ 59
def prefixEnd_2540380 : Nat := 4983230072969 + 3 ^ 40 * 2540380 * 2
def baseEnd_2540380 : Nat := 1304435985068875985267011

theorem tailTrace_2540380 : CollatzResearch.WordTrace tailWord_2540380 prefixEnd_2540380 1304435985068875985267011 := by
  unfold tailWord_2540380
  simp only [CollatzResearch.WordTrace]
  refine ⟨46327635268322298603781297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61770180357763064805041729 46327635268322298603781297)
  ·
    refine ⟨34745726451241723952835973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46327635268322298603781297 34745726451241723952835973)
    ·
      refine ⟨6514823709607823241156745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34745726451241723952835973 6514823709607823241156745)
      ·
        refine ⟨4886117782205867430867559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6514823709607823241156745 4886117782205867430867559)
        ·
          refine ⟨7329176673308801146301339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4886117782205867430867559 7329176673308801146301339)
          ·
            refine ⟨10993765009963201719452009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7329176673308801146301339 10993765009963201719452009)
            ·
              refine ⟨8245323757472401289589007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10993765009963201719452009 8245323757472401289589007)
              ·
                refine ⟨12367985636208601934383511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8245323757472401289589007 12367985636208601934383511)
                ·
                  refine ⟨18551978454312902901575267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12367985636208601934383511 18551978454312902901575267)
                  ·
                    refine ⟨27827967681469354352362901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18551978454312902901575267 27827967681469354352362901)
                    ·
                      refine ⟨1304435985068875985267011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27827967681469354352362901 1304435985068875985267011)
                      ·
                        rfl

theorem cell23_2540380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2540380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540380 prefixEnd_2540380 := by exact prefixLift 2540380
  have htrace : WordTrace (prefixWord ++ tailWord_2540380) baseStart_2540380 baseEnd_2540380 := by
    simpa [prefixWord, tailWord_2540380, baseEnd_2540380] using wordTrace_append hprefix tailTrace_2540380
  have hstable : (prefixWord ++ tailWord_2540380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540380).length < 2 ^ (prefixWord ++ tailWord_2540380).sum := by decide
  have hdescent : baseEnd_2540380 < baseStart_2540380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540387 : List Nat := [1, 1, 1, 5, 3, 1, 3, 2, 1, 2, 3]
def baseStart_2540387 : Nat := 118140960795 + 2540387 * 2 ^ 59
def prefixEnd_2540387 : Nat := 4983230072969 + 3 ^ 40 * 2540387 * 2
def baseEnd_2540387 : Nat := 1304439579433457457879479

theorem tailTrace_2540387 : CollatzResearch.WordTrace tailWord_2540387 prefixEnd_2540387 1304439579433457457879479 := by
  unfold tailWord_2540387
  simp only [CollatzResearch.WordTrace]
  refine ⟨92655525847619237403067415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61770350565079491602044943 92655525847619237403067415)
  ·
    refine ⟨138983288771428856104601123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92655525847619237403067415 138983288771428856104601123)
    ·
      refine ⟨208474933157143284156901685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138983288771428856104601123 208474933157143284156901685)
      ·
        refine ⟨19544524983482182889709533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 208474933157143284156901685 19544524983482182889709533)
        ·
          refine ⟨7329196868805818583641075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19544524983482182889709533 7329196868805818583641075)
          ·
            refine ⟨10993795303208727875461613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7329196868805818583641075 10993795303208727875461613)
            ·
              refine ⟨4122673238703272953298105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10993795303208727875461613 4122673238703272953298105)
              ·
                refine ⟨3092004929027454714973579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4122673238703272953298105 3092004929027454714973579)
                ·
                  refine ⟨4638007393541182072460369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3092004929027454714973579 4638007393541182072460369)
                  ·
                    refine ⟨3478505545155886554345277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4638007393541182072460369 3478505545155886554345277)
                    ·
                      refine ⟨1304439579433457457879479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3478505545155886554345277 1304439579433457457879479)
                      ·
                        rfl

theorem cell23_2540387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_2540387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540387 prefixEnd_2540387 := by exact prefixLift 2540387
  have htrace : WordTrace (prefixWord ++ tailWord_2540387) baseStart_2540387 baseEnd_2540387 := by
    simpa [prefixWord, tailWord_2540387, baseEnd_2540387] using wordTrace_append hprefix tailTrace_2540387
  have hstable : (prefixWord ++ tailWord_2540387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540387).length < 2 ^ (prefixWord ++ tailWord_2540387).sum := by decide
  have hdescent : baseEnd_2540387 < baseStart_2540387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540400 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 6, 1, 3]
def baseStart_2540400 : Nat := 118140960795 + 2540400 * 2 ^ 59
def prefixEnd_2540400 : Nat := 4983230072969 + 3 ^ 40 * 2540400 * 2
def baseEnd_2540400 : Nat := 1304446254681965907016919

theorem tailTrace_2540400 : CollatzResearch.WordTrace tailWord_2540400 prefixEnd_2540400 1304446254681965907016919 := by
  unfold tailWord_2540400
  simp only [CollatzResearch.WordTrace]
  refine ⟨46327999998286070311645327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61770666664381427082193769 46327999998286070311645327)
  ·
    refine ⟨69491999997429105467467991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46327999998286070311645327 69491999997429105467467991)
    ·
      refine ⟨104237999996143658201201987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69491999997429105467467991 104237999996143658201201987)
      ·
        refine ⟨156356999994215487301802981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104237999996143658201201987 156356999994215487301802981)
        ·
          refine ⟨29316937498915403869088059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156356999994215487301802981 29316937498915403869088059)
          ·
            refine ⟨43975406248373105803632089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29316937498915403869088059 43975406248373105803632089)
            ·
              refine ⟨32981554686279829352724067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43975406248373105803632089 32981554686279829352724067)
              ·
                refine ⟨49472332029419744029086101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32981554686279829352724067 49472332029419744029086101)
                ·
                  refine ⟨2319015563879050501363411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49472332029419744029086101 2319015563879050501363411)
                  ·
                    refine ⟨3478523345818575752045117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2319015563879050501363411 3478523345818575752045117)
                    ·
                      refine ⟨1304446254681965907016919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3478523345818575752045117 1304446254681965907016919)
                      ·
                        rfl

theorem cell23_2540400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 6, 1, 3].length) (baseStart_2540400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540400 prefixEnd_2540400 := by exact prefixLift 2540400
  have htrace : WordTrace (prefixWord ++ tailWord_2540400) baseStart_2540400 baseEnd_2540400 := by
    simpa [prefixWord, tailWord_2540400, baseEnd_2540400] using wordTrace_append hprefix tailTrace_2540400
  have hstable : (prefixWord ++ tailWord_2540400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540400).length < 2 ^ (prefixWord ++ tailWord_2540400).sum := by decide
  have hdescent : baseEnd_2540400 < baseStart_2540400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540413 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_2540413 : Nat := 118140960795 + 2540413 * 2 ^ 59
def prefixEnd_2540413 : Nat := 4983230072969 + 3 ^ 40 * 2540413 * 2
def baseEnd_2540413 : Nat := 1304452929930474356154359

theorem tailTrace_2540413 : CollatzResearch.WordTrace tailWord_2540413 prefixEnd_2540413 1304452929930474356154359 := by
  unfold tailWord_2540413
  simp only [CollatzResearch.WordTrace]
  refine ⟨92656474145525043843513893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61770982763683362562342595 92656474145525043843513893)
  ·
    refine ⟨17373088902285945720658855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92656474145525043843513893 17373088902285945720658855)
    ·
      refine ⟨26059633353428918580988283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17373088902285945720658855 26059633353428918580988283)
      ·
        refine ⟨39089450030143377871482425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26059633353428918580988283 39089450030143377871482425)
        ·
          refine ⟨29317087522607533403611819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39089450030143377871482425 29317087522607533403611819)
          ·
            refine ⟨43975631283911300105417729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29317087522607533403611819 43975631283911300105417729)
            ·
              refine ⟨32981723462933475079063297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43975631283911300105417729 32981723462933475079063297)
              ·
                refine ⟨24736292597200106309297473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32981723462933475079063297 24736292597200106309297473)
                ·
                  refine ⟨18552219447900079731973105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24736292597200106309297473 18552219447900079731973105)
                  ·
                    refine ⟨13914164585925059798979829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18552219447900079731973105 13914164585925059798979829)
                    ·
                      refine ⟨1304452929930474356154359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13914164585925059798979829 1304452929930474356154359)
                      ·
                        rfl

theorem cell23_2540413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_2540413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540413 prefixEnd_2540413 := by exact prefixLift 2540413
  have htrace : WordTrace (prefixWord ++ tailWord_2540413) baseStart_2540413 baseEnd_2540413 := by
    simpa [prefixWord, tailWord_2540413, baseEnd_2540413] using wordTrace_append hprefix tailTrace_2540413
  have hstable : (prefixWord ++ tailWord_2540413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540413).length < 2 ^ (prefixWord ++ tailWord_2540413).sum := by decide
  have hdescent : baseEnd_2540413 < baseStart_2540413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540434 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2540434 : Nat := 118140960795 + 2540434 * 2 ^ 59
def prefixEnd_2540434 : Nat := 4983230072969 + 3 ^ 40 * 2540434 * 2
def baseEnd_2540434 : Nat := 1304463713024218773991763

theorem tailTrace_2540434 : CollatzResearch.WordTrace tailWord_2540434 prefixEnd_2540434 1304463713024218773991763 := by
  unfold tailWord_2540434
  simp only [CollatzResearch.WordTrace]
  refine ⟨23164310019612241107507089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61771493385632642953352237 23164310019612241107507089)
  ·
    refine ⟨17373232514709180830630317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23164310019612241107507089 17373232514709180830630317)
    ·
      refine ⟨6514962193015942811486369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17373232514709180830630317 6514962193015942811486369)
      ·
        refine ⟨4886221644761957108614777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6514962193015942811486369 4886221644761957108614777)
        ·
          refine ⟨3664666233571467831461083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4886221644761957108614777 3664666233571467831461083)
          ·
            refine ⟨5496999350357201747191625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3664666233571467831461083 5496999350357201747191625)
            ·
              refine ⟨4122749512767901310393719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5496999350357201747191625 4122749512767901310393719)
              ·
                refine ⟨6184124269151851965590579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4122749512767901310393719 6184124269151851965590579)
                ·
                  refine ⟨9276186403727777948385869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6184124269151851965590579 9276186403727777948385869)
                  ·
                    refine ⟨3478569901397916730644701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9276186403727777948385869 3478569901397916730644701)
                    ·
                      refine ⟨1304463713024218773991763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3478569901397916730644701 1304463713024218773991763)
                      ·
                        rfl

theorem cell23_2540434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2540434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540434 prefixEnd_2540434 := by exact prefixLift 2540434
  have htrace : WordTrace (prefixWord ++ tailWord_2540434) baseStart_2540434 baseEnd_2540434 := by
    simpa [prefixWord, tailWord_2540434, baseEnd_2540434] using wordTrace_append hprefix tailTrace_2540434
  have hstable : (prefixWord ++ tailWord_2540434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540434).length < 2 ^ (prefixWord ++ tailWord_2540434).sum := by decide
  have hdescent : baseEnd_2540434 < baseStart_2540434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540457 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 4, 2, 2]
def baseStart_2540457 : Nat := 118140960795 + 2540457 * 2 ^ 59
def prefixEnd_2540457 : Nat := 4983230072969 + 3 ^ 40 * 2540457 * 2
def baseEnd_2540457 : Nat := 1304475523079272184004157

theorem tailTrace_2540457 : CollatzResearch.WordTrace tailWord_2540457 prefixEnd_2540457 1304475523079272184004157 := by
  unfold tailWord_2540457
  simp only [CollatzResearch.WordTrace]
  refine ⟨92658078957365639358115625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61772052638243759572077083 92658078957365639358115625)
  ·
    refine ⟨69493559218024229518586719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92658078957365639358115625 69493559218024229518586719)
    ·
      refine ⟨104240338827036344277880079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69493559218024229518586719 104240338827036344277880079)
      ·
        refine ⟨156360508240554516416820119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104240338827036344277880079 156360508240554516416820119)
        ·
          refine ⟨234540762360831774625230179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156360508240554516416820119 234540762360831774625230179)
          ·
            refine ⟨351811143541247661937845269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234540762360831774625230179 351811143541247661937845269)
            ·
              refine ⟨16491147353495984153336497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 351811143541247661937845269 16491147353495984153336497)
              ·
                refine ⟨12368360515121988115002373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16491147353495984153336497 12368360515121988115002373)
                ·
                  refine ⟨2319067596585372771562945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12368360515121988115002373 2319067596585372771562945)
                  ·
                    refine ⟨1739300697439029578672209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2319067596585372771562945 1739300697439029578672209)
                    ·
                      refine ⟨1304475523079272184004157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1739300697439029578672209 1304475523079272184004157)
                      ·
                        rfl

theorem cell23_2540457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 2, 2].length) (baseStart_2540457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540457 prefixEnd_2540457 := by exact prefixLift 2540457
  have htrace : WordTrace (prefixWord ++ tailWord_2540457) baseStart_2540457 baseEnd_2540457 := by
    simpa [prefixWord, tailWord_2540457, baseEnd_2540457] using wordTrace_append hprefix tailTrace_2540457
  have hstable : (prefixWord ++ tailWord_2540457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540457).length < 2 ^ (prefixWord ++ tailWord_2540457).sum := by decide
  have hdescent : baseEnd_2540457 < baseStart_2540457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540468 : List Nat := [2, 5, 2, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_2540468 : Nat := 118140960795 + 2540468 * 2 ^ 59
def prefixEnd_2540468 : Nat := 4983230072969 + 3 ^ 40 * 2540468 * 2
def baseEnd_2540468 : Nat := 1304481171366471640966607

theorem tailTrace_2540468 : CollatzResearch.WordTrace tailWord_2540468 prefixEnd_2540468 1304481171366471640966607 := by
  unfold tailWord_2540468
  simp only [CollatzResearch.WordTrace]
  refine ⟨46329240080162894118383029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61772320106883858824510705 46329240080162894118383029)
  ·
    refine ⟨4343366257515271323598409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46329240080162894118383029 4343366257515271323598409)
    ·
      refine ⟨3257524693136453492698807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4343366257515271323598409 3257524693136453492698807)
      ·
        refine ⟨4886287039704680239048211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257524693136453492698807 4886287039704680239048211)
        ·
          refine ⟨7329430559557020358572317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4886287039704680239048211 7329430559557020358572317)
          ·
            refine ⟨2748536459833882634464619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7329430559557020358572317 2748536459833882634464619)
            ·
              refine ⟨4122804689750823951696929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2748536459833882634464619 4122804689750823951696929)
              ·
                refine ⟨3092103517313117963772697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4122804689750823951696929 3092103517313117963772697)
                ·
                  refine ⟨2319077637984838472829523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3092103517313117963772697 2319077637984838472829523)
                  ·
                    refine ⟨3478616456977257709244285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2319077637984838472829523 3478616456977257709244285)
                    ·
                      refine ⟨1304481171366471640966607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3478616456977257709244285 1304481171366471640966607)
                      ·
                        rfl

theorem cell23_2540468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_2540468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540468 prefixEnd_2540468 := by exact prefixLift 2540468
  have htrace : WordTrace (prefixWord ++ tailWord_2540468) baseStart_2540468 baseEnd_2540468 := by
    simpa [prefixWord, tailWord_2540468, baseEnd_2540468] using wordTrace_append hprefix tailTrace_2540468
  have hstable : (prefixWord ++ tailWord_2540468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540468).length < 2 ^ (prefixWord ++ tailWord_2540468).sum := by decide
  have hdescent : baseEnd_2540468 < baseStart_2540468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540480 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 7]
def baseStart_2540480 : Nat := 118140960795 + 2540480 * 2 ^ 59
def prefixEnd_2540480 : Nat := 4983230072969 + 3 ^ 40 * 2540480 * 2
def baseEnd_2540480 : Nat := 144943037014925066001839

theorem tailTrace_2540480 : CollatzResearch.WordTrace tailWord_2540480 prefixEnd_2540480 144943037014925066001839 := by
  unfold tailWord_2540480
  simp only [CollatzResearch.WordTrace]
  refine ⟨46329458918141157143101447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61772611890854876190801929 46329458918141157143101447)
  ·
    refine ⟨69494188377211735714652171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46329458918141157143101447 69494188377211735714652171)
    ·
      refine ⟨104241282565817603571978257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69494188377211735714652171 104241282565817603571978257)
      ·
        refine ⟨78180961924363202678983693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104241282565817603571978257 78180961924363202678983693)
        ·
          refine ⟨29317860721636201004618885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78180961924363202678983693 29317860721636201004618885)
          ·
            refine ⟨5497098885306787688366041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29317860721636201004618885 5497098885306787688366041)
            ·
              refine ⟨4122824163980090766274531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5497098885306787688366041 4122824163980090766274531)
              ·
                refine ⟨6184236245970136149411797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4122824163980090766274531 6184236245970136149411797)
                ·
                  refine ⟨144943037014925066001839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6184236245970136149411797 144943037014925066001839)
                  ·
                    rfl

theorem cell23_2540480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 7].length) (baseStart_2540480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540480 prefixEnd_2540480 := by exact prefixLift 2540480
  have htrace : WordTrace (prefixWord ++ tailWord_2540480) baseStart_2540480 baseEnd_2540480 := by
    simpa [prefixWord, tailWord_2540480, baseEnd_2540480] using wordTrace_append hprefix tailTrace_2540480
  have hstable : (prefixWord ++ tailWord_2540480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540480).length < 2 ^ (prefixWord ++ tailWord_2540480).sum := by decide
  have hdescent : baseEnd_2540480 < baseStart_2540480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540491 : List Nat := [1, 1, 1, 1, 3, 6, 3, 1, 2, 2, 2]
def baseStart_2540491 : Nat := 118140960795 + 2540491 * 2 ^ 59
def prefixEnd_2540491 : Nat := 4983230072969 + 3 ^ 40 * 2540491 * 2
def baseEnd_2540491 : Nat := 1304492981421525050979001

theorem tailTrace_2540491 : CollatzResearch.WordTrace tailWord_2540491 prefixEnd_2540491 1304492981421525050979001 := by
  unfold tailWord_2540491
  simp only [CollatzResearch.WordTrace]
  refine ⟨92659319039242463164853327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61772879359494975443235551 92659319039242463164853327)
  ·
    refine ⟨138988978558863694747279991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92659319039242463164853327 138988978558863694747279991)
    ·
      refine ⟨208483467838295542120919987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138988978558863694747279991 208483467838295542120919987)
      ·
        refine ⟨312725201757443313181379981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208483467838295542120919987 312725201757443313181379981)
        ·
          refine ⟨117271950659041242443017493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312725201757443313181379981 117271950659041242443017493)
          ·
            refine ⟨5497122687142558239516445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117271950659041242443017493 5497122687142558239516445)
            ·
              refine ⟨2061421007678459339818667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5497122687142558239516445 2061421007678459339818667)
              ·
                refine ⟨3092131511517689009728001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061421007678459339818667 3092131511517689009728001)
                ·
                  refine ⟨2319098633638266757296001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3092131511517689009728001 2319098633638266757296001)
                  ·
                    refine ⟨1739323975228700067972001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2319098633638266757296001 1739323975228700067972001)
                    ·
                      refine ⟨1304492981421525050979001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1739323975228700067972001 1304492981421525050979001)
                      ·
                        rfl

theorem cell23_2540491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 2, 2, 2].length) (baseStart_2540491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540491 prefixEnd_2540491 := by exact prefixLift 2540491
  have htrace : WordTrace (prefixWord ++ tailWord_2540491) baseStart_2540491 baseEnd_2540491 := by
    simpa [prefixWord, tailWord_2540491, baseEnd_2540491] using wordTrace_append hprefix tailTrace_2540491
  have hstable : (prefixWord ++ tailWord_2540491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540491).length < 2 ^ (prefixWord ++ tailWord_2540491).sum := by decide
  have hdescent : baseEnd_2540491 < baseStart_2540491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540503 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_2540503 : Nat := 118140960795 + 2540503 * 2 ^ 59
def prefixEnd_2540503 : Nat := 4983230072969 + 3 ^ 40 * 2540503 * 2
def baseEnd_2540503 : Nat := 1304499143189379004028945

theorem tailTrace_2540503 : CollatzResearch.WordTrace tailWord_2540503 prefixEnd_2540503 1304499143189379004028945 := by
  unfold tailWord_2540503
  simp only [CollatzResearch.WordTrace]
  refine ⟨92659756715198989214290163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61773171143465992809526775 92659756715198989214290163)
  ·
    refine ⟨138989635072798483821435245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92659756715198989214290163 138989635072798483821435245)
    ·
      refine ⟨52121113152299431433038217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 138989635072798483821435245 52121113152299431433038217)
      ·
        refine ⟨39090834864224573574778663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52121113152299431433038217 39090834864224573574778663)
        ·
          refine ⟨58636252296336860362167995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39090834864224573574778663 58636252296336860362167995)
          ·
            refine ⟨87954378444505290543251993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58636252296336860362167995 87954378444505290543251993)
            ·
              refine ⟨65965783833378967907438995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87954378444505290543251993 65965783833378967907438995)
              ·
                refine ⟨98948675750068451861158493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65965783833378967907438995 98948675750068451861158493)
                ·
                  refine ⟨37105753406275669447934435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98948675750068451861158493 37105753406275669447934435)
                  ·
                    refine ⟨55658630109413504171901653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37105753406275669447934435 55658630109413504171901653)
                    ·
                      refine ⟨1304499143189379004028945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55658630109413504171901653 1304499143189379004028945)
                      ·
                        rfl

theorem cell23_2540503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_2540503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540503 prefixEnd_2540503 := by exact prefixLift 2540503
  have htrace : WordTrace (prefixWord ++ tailWord_2540503) baseStart_2540503 baseEnd_2540503 := by
    simpa [prefixWord, tailWord_2540503, baseEnd_2540503] using wordTrace_append hprefix tailTrace_2540503
  have hstable : (prefixWord ++ tailWord_2540503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540503).length < 2 ^ (prefixWord ++ tailWord_2540503).sum := by decide
  have hdescent : baseEnd_2540503 < baseStart_2540503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540542 : List Nat := [4, 2, 2, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_2540542 : Nat := 118140960795 + 2540542 * 2 ^ 59
def prefixEnd_2540542 : Nat := 4983230072969 + 3 ^ 40 * 2540542 * 2
def baseEnd_2540542 : Nat := 1304519168934904351441267

theorem tailTrace_2540542 : CollatzResearch.WordTrace tailWord_2540542 prefixEnd_2540542 1304519168934904351441267 := by
  unfold tailWord_2540542
  simp only [CollatzResearch.WordTrace]
  refine ⟨11582647395257212359369985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61774119441371799249973253 11582647395257212359369985)
  ·
    refine ⟨8686985546442909269527489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11582647395257212359369985 8686985546442909269527489)
    ·
      refine ⟨6515239159832181952145617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8686985546442909269527489 6515239159832181952145617)
      ·
        refine ⟨4886429369874136464109213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6515239159832181952145617 4886429369874136464109213)
        ·
          refine ⟨1832411013702801174040955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4886429369874136464109213 1832411013702801174040955)
          ·
            refine ⟨2748616520554201761061433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1832411013702801174040955 2748616520554201761061433)
            ·
              refine ⟨2061462390415651320796075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2748616520554201761061433 2061462390415651320796075)
              ·
                refine ⟨3092193585623476981194113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061462390415651320796075 3092193585623476981194113)
                ·
                  refine ⟨2319145189217607735895585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3092193585623476981194113 2319145189217607735895585)
                  ·
                    refine ⟨1739358891913205801921689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2319145189217607735895585 1739358891913205801921689)
                    ·
                      refine ⟨1304519168934904351441267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1739358891913205801921689 1304519168934904351441267)
                      ·
                        rfl

theorem cell23_2540542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_2540542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540542 prefixEnd_2540542 := by exact prefixLift 2540542
  have htrace : WordTrace (prefixWord ++ tailWord_2540542) baseStart_2540542 baseEnd_2540542 := by
    simpa [prefixWord, tailWord_2540542, baseEnd_2540542] using wordTrace_append hprefix tailTrace_2540542
  have hstable : (prefixWord ++ tailWord_2540542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540542).length < 2 ^ (prefixWord ++ tailWord_2540542).sum := by decide
  have hdescent : baseEnd_2540542 < baseStart_2540542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540607 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 1, 5, 2]
def baseStart_2540607 : Nat := 118140960795 + 2540607 * 2 ^ 59
def prefixEnd_2540607 : Nat := 4983230072969 + 3 ^ 40 * 2540607 * 2
def baseEnd_2540607 : Nat := 1304552545177446597128467

theorem tailTrace_2540607 : CollatzResearch.WordTrace tailWord_2540607 prefixEnd_2540607 1304552545177446597128467 := by
  unfold tailWord_2540607
  simp only [CollatzResearch.WordTrace]
  refine ⟨92663549906822214976076075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61775699937881476650717383 92663549906822214976076075)
  ·
    refine ⟨138995324860233322464114113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92663549906822214976076075 138995324860233322464114113)
    ·
      refine ⟨104246493645174991848085585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138995324860233322464114113 104246493645174991848085585)
      ·
        refine ⟨78184870233881243886064189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104246493645174991848085585 78184870233881243886064189)
        ·
          refine ⟨29319326337705466457274071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78184870233881243886064189 29319326337705466457274071)
          ·
            refine ⟨43978989506558199685911107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29319326337705466457274071 43978989506558199685911107)
            ·
              refine ⟨65968484259837299528866661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43978989506558199685911107 65968484259837299528866661)
              ·
                refine ⟨12369090798719493661662499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65968484259837299528866661 12369090798719493661662499)
                ·
                  refine ⟨18553636198079240492493749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12369090798719493661662499 18553636198079240492493749)
                  ·
                    refine ⟨1739403393569928796171289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18553636198079240492493749 1739403393569928796171289)
                    ·
                      refine ⟨1304552545177446597128467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1739403393569928796171289 1304552545177446597128467)
                      ·
                        rfl

theorem cell23_2540607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 5, 2].length) (baseStart_2540607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540607 prefixEnd_2540607 := by exact prefixLift 2540607
  have htrace : WordTrace (prefixWord ++ tailWord_2540607) baseStart_2540607 baseEnd_2540607 := by
    simpa [prefixWord, tailWord_2540607, baseEnd_2540607] using wordTrace_append hprefix tailTrace_2540607
  have hstable : (prefixWord ++ tailWord_2540607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540607).length < 2 ^ (prefixWord ++ tailWord_2540607).sum := by decide
  have hdescent : baseEnd_2540607 < baseStart_2540607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540638 : List Nat := [4, 4, 1, 1, 1, 3, 1, 2, 6]
def baseStart_2540638 : Nat := 118140960795 + 2540638 * 2 ^ 59
def prefixEnd_2540638 : Nat := 4983230072969 + 3 ^ 40 * 2540638 * 2
def baseEnd_2540638 : Nat := 144952051453081775093425

theorem tailTrace_2540638 : CollatzResearch.WordTrace tailWord_2540638 prefixEnd_2540638 144952051453081775093425 := by
  unfold tailWord_2540638
  simp only [CollatzResearch.WordTrace]
  refine ⟨11583085071213738408806821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61776453713139938180303045 11583085071213738408806821)
  ·
    refine ⟨2171828450852575951651279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11583085071213738408806821 2171828450852575951651279)
    ·
      refine ⟨3257742676278863927476919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2171828450852575951651279 3257742676278863927476919)
      ·
        refine ⟨4886614014418295891215379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257742676278863927476919 4886614014418295891215379)
        ·
          refine ⟨7329921021627443836823069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4886614014418295891215379 7329921021627443836823069)
          ·
            refine ⟨2748720383110291438808651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7329921021627443836823069 2748720383110291438808651)
            ·
              refine ⟨4123080574665437158212977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2748720383110291438808651 4123080574665437158212977)
              ·
                refine ⟨3092310430999077868659733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4123080574665437158212977 3092310430999077868659733)
                ·
                  refine ⟨144952051453081775093425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3092310430999077868659733 144952051453081775093425)
                  ·
                    rfl

theorem cell23_2540638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_2540638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540638 prefixEnd_2540638 := by exact prefixLift 2540638
  have htrace : WordTrace (prefixWord ++ tailWord_2540638) baseStart_2540638 baseEnd_2540638 := by
    simpa [prefixWord, tailWord_2540638, baseEnd_2540638] using wordTrace_append hprefix tailTrace_2540638
  have hstable : (prefixWord ++ tailWord_2540638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540638).length < 2 ^ (prefixWord ++ tailWord_2540638).sum := by decide
  have hdescent : baseEnd_2540638 < baseStart_2540638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540648 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2540648 : Nat := 118140960795 + 2540648 * 2 ^ 59
def prefixEnd_2540648 : Nat := 4983230072969 + 3 ^ 40 * 2540648 * 2
def baseEnd_2540648 : Nat := 1304573597884280936715779

theorem tailTrace_2540648 : CollatzResearch.WordTrace tailWord_2540648 prefixEnd_2540648 1304573597884280936715779 := by
  unfold tailWord_2540648
  simp only [CollatzResearch.WordTrace]
  refine ⟨46332522649836839489159299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61776696866449119318879065 46332522649836839489159299)
  ·
    refine ⟨69498783974755259233738949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46332522649836839489159299 69498783974755259233738949)
    ·
      refine ⟨13031021995266611106326053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69498783974755259233738949 13031021995266611106326053)
      ·
        refine ⟨2443316624112489582436135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13031021995266611106326053 2443316624112489582436135)
        ·
          refine ⟨3664974936168734373654203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2443316624112489582436135 3664974936168734373654203)
          ·
            refine ⟨5497462404253101560481305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3664974936168734373654203 5497462404253101560481305)
            ·
              refine ⟨4123096803189826170360979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5497462404253101560481305 4123096803189826170360979)
              ·
                refine ⟨6184645204784739255541469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4123096803189826170360979 6184645204784739255541469)
                ·
                  refine ⟨2319241951794277220828051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6184645204784739255541469 2319241951794277220828051)
                  ·
                    refine ⟨3478862927691415831242077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2319241951794277220828051 3478862927691415831242077)
                    ·
                      refine ⟨1304573597884280936715779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3478862927691415831242077 1304573597884280936715779)
                      ·
                        rfl

theorem cell23_2540648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2540648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540648 prefixEnd_2540648 := by exact prefixLift 2540648
  have htrace : WordTrace (prefixWord ++ tailWord_2540648) baseStart_2540648 baseEnd_2540648 := by
    simpa [prefixWord, tailWord_2540648, baseEnd_2540648] using wordTrace_append hprefix tailTrace_2540648
  have hstable : (prefixWord ++ tailWord_2540648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540648).length < 2 ^ (prefixWord ++ tailWord_2540648).sum := by decide
  have hdescent : baseEnd_2540648 < baseStart_2540648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540657 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 3, 2, 3]
def baseStart_2540657 : Nat := 118140960795 + 2540657 * 2 ^ 59
def prefixEnd_2540657 : Nat := 4983230072969 + 3 ^ 40 * 2540657 * 2
def baseEnd_2540657 : Nat := 1304578219210171401503237

theorem tailTrace_2540657 : CollatzResearch.WordTrace tailWord_2540657 prefixEnd_2540657 1304578219210171401503237 := by
  unfold tailWord_2540657
  simp only [CollatzResearch.WordTrace]
  refine ⟨92665373556641073515396225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61776915704427382343597483 92665373556641073515396225)
  ·
    refine ⟨69499030167480805136547169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92665373556641073515396225 69499030167480805136547169)
    ·
      refine ⟨52124272625610603852410377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69499030167480805136547169 52124272625610603852410377)
      ·
        refine ⟨39093204469207952889307783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52124272625610603852410377 39093204469207952889307783)
        ·
          refine ⟨58639806703811929333961675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39093204469207952889307783 58639806703811929333961675)
          ·
            refine ⟨87959710055717894000942513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58639806703811929333961675 87959710055717894000942513)
            ·
              refine ⟨65969782541788420500706885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87959710055717894000942513 65969782541788420500706885)
              ·
                refine ⟨12369334226585328843882541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65969782541788420500706885 12369334226585328843882541)
                ·
                  refine ⟨4638500334969498316455953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12369334226585328843882541 4638500334969498316455953)
                  ·
                    refine ⟨3478875251227123737341965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4638500334969498316455953 3478875251227123737341965)
                    ·
                      refine ⟨1304578219210171401503237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3478875251227123737341965 1304578219210171401503237)
                      ·
                        rfl

theorem cell23_2540657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_2540657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540657 prefixEnd_2540657 := by exact prefixLift 2540657
  have htrace : WordTrace (prefixWord ++ tailWord_2540657) baseStart_2540657 baseEnd_2540657 := by
    simpa [prefixWord, tailWord_2540657, baseEnd_2540657] using wordTrace_append hprefix tailTrace_2540657
  have hstable : (prefixWord ++ tailWord_2540657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540657).length < 2 ^ (prefixWord ++ tailWord_2540657).sum := by decide
  have hdescent : baseEnd_2540657 < baseStart_2540657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540677 : List Nat := [1, 3, 1, 1, 6, 1, 1, 9]
def baseStart_2540677 : Nat := 118140960795 + 2540677 * 2 ^ 59
def prefixEnd_2540677 : Nat := 4983230072969 + 3 ^ 40 * 2540677 * 2
def baseEnd_2540677 : Nat := 48318092178639308268635

theorem tailTrace_2540677 : CollatzResearch.WordTrace tailWord_2540677 prefixEnd_2540677 48318092178639308268635 := by
  unfold tailWord_2540677
  simp only [CollatzResearch.WordTrace]
  refine ⟨92666103016568616931124285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61777402011045744620749523 92666103016568616931124285)
  ·
    refine ⟨34749788631213231349171607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92666103016568616931124285 34749788631213231349171607)
    ·
      refine ⟨52124682946819847023757411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34749788631213231349171607 52124682946819847023757411)
      ·
        refine ⟨78187024420229770535636117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52124682946819847023757411 78187024420229770535636117)
        ·
          refine ⟨3665016769698270493857943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78187024420229770535636117 3665016769698270493857943)
          ·
            refine ⟨5497525154547405740786915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665016769698270493857943 5497525154547405740786915)
            ·
              refine ⟨8246287731821108611180373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497525154547405740786915 8246287731821108611180373)
              ·
                refine ⟨48318092178639308268635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8246287731821108611180373 48318092178639308268635)
                ·
                  rfl

theorem cell23_2540677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 9].length) (baseStart_2540677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540677 prefixEnd_2540677 := by exact prefixLift 2540677
  have htrace : WordTrace (prefixWord ++ tailWord_2540677) baseStart_2540677 baseEnd_2540677 := by
    simpa [prefixWord, tailWord_2540677, baseEnd_2540677] using wordTrace_append hprefix tailTrace_2540677
  have hstable : (prefixWord ++ tailWord_2540677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540677).length < 2 ^ (prefixWord ++ tailWord_2540677).sum := by decide
  have hdescent : baseEnd_2540677 < baseStart_2540677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540704 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 4, 1, 3]
def baseStart_2540704 : Nat := 118140960795 + 2540704 * 2 ^ 59
def prefixEnd_2540704 : Nat := 4983230072969 + 3 ^ 40 * 2540704 * 2
def baseEnd_2540704 : Nat := 1304602352800932717615521

theorem tailTrace_2540704 : CollatzResearch.WordTrace tailWord_2540704 prefixEnd_2540704 1304602352800932717615521 := by
  unfold tailWord_2540704
  simp only [CollatzResearch.WordTrace]
  refine ⟨46333543893735400271178583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61778058524980533694904777 46333543893735400271178583)
  ·
    refine ⟨69500315840603100406767875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46333543893735400271178583 69500315840603100406767875)
    ·
      refine ⟨104250473760904650610151813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69500315840603100406767875 104250473760904650610151813)
      ·
        refine ⟨19546963830169621989403465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104250473760904650610151813 19546963830169621989403465)
        ·
          refine ⟨14660222872627216492052599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19546963830169621989403465 14660222872627216492052599)
          ·
            refine ⟨21990334308940824738078899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14660222872627216492052599 21990334308940824738078899)
            ·
              refine ⟨32985501463411237107118349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21990334308940824738078899 32985501463411237107118349)
              ·
                refine ⟨12369563048779213915169381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32985501463411237107118349 12369563048779213915169381)
                ·
                  refine ⟨2319293071646102609094259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12369563048779213915169381 2319293071646102609094259)
                  ·
                    refine ⟨3478939607469153913641389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2319293071646102609094259 3478939607469153913641389)
                    ·
                      refine ⟨1304602352800932717615521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3478939607469153913641389 1304602352800932717615521)
                      ·
                        rfl

theorem cell23_2540704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_2540704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540704 prefixEnd_2540704 := by exact prefixLift 2540704
  have htrace : WordTrace (prefixWord ++ tailWord_2540704) baseStart_2540704 baseEnd_2540704 := by
    simpa [prefixWord, tailWord_2540704, baseEnd_2540704] using wordTrace_append hprefix tailTrace_2540704
  have hstable : (prefixWord ++ tailWord_2540704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540704).length < 2 ^ (prefixWord ++ tailWord_2540704).sum := by decide
  have hdescent : baseEnd_2540704 < baseStart_2540704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540705 : List Nat := [1, 2, 3, 3, 1, 1, 5, 2, 1, 2, 2]
def baseStart_2540705 : Nat := 118140960795 + 2540705 * 2 ^ 59
def prefixEnd_2540705 : Nat := 4983230072969 + 3 ^ 40 * 2540705 * 2
def baseEnd_2540705 : Nat := 1304602866281587213703017

theorem tailTrace_2540705 : CollatzResearch.WordTrace tailWord_2540705 prefixEnd_2540705 1304602866281587213703017 := by
  unfold tailWord_2540705
  simp only [CollatzResearch.WordTrace]
  refine ⟨92667124260467177713143569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61778082840311451808762379 92667124260467177713143569)
  ·
    refine ⟨69500343195350383284857677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92667124260467177713143569 69500343195350383284857677)
    ·
      refine ⟨26062628698256393731821629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69500343195350383284857677 26062628698256393731821629)
      ·
        refine ⟨9773485761846147649433111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26062628698256393731821629 9773485761846147649433111)
        ·
          refine ⟨14660228642769221474149667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9773485761846147649433111 14660228642769221474149667)
          ·
            refine ⟨21990342964153832211224501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14660228642769221474149667 21990342964153832211224501)
            ·
              refine ⟨2061594652889421769802297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21990342964153832211224501 2061594652889421769802297)
              ·
                refine ⟨1546195989667066327351723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061594652889421769802297 1546195989667066327351723)
                ·
                  refine ⟨2319293984500599491027585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1546195989667066327351723 2319293984500599491027585)
                  ·
                    refine ⟨1739470488375449618270689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2319293984500599491027585 1739470488375449618270689)
                    ·
                      refine ⟨1304602866281587213703017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1739470488375449618270689 1304602866281587213703017)
                      ·
                        rfl

theorem cell23_2540705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_2540705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540705 prefixEnd_2540705 := by exact prefixLift 2540705
  have htrace : WordTrace (prefixWord ++ tailWord_2540705) baseStart_2540705 baseEnd_2540705 := by
    simpa [prefixWord, tailWord_2540705, baseEnd_2540705] using wordTrace_append hprefix tailTrace_2540705
  have hstable : (prefixWord ++ tailWord_2540705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540705).length < 2 ^ (prefixWord ++ tailWord_2540705).sum := by decide
  have hdescent : baseEnd_2540705 < baseStart_2540705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540742 : List Nat := [6, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_2540742 : Nat := 118140960795 + 2540742 * 2 ^ 59
def prefixEnd_2540742 : Nat := 4983230072969 + 3 ^ 40 * 2540742 * 2
def baseEnd_2540742 : Nat := 1304621865065803568940347

theorem tailTrace_2540742 : CollatzResearch.WordTrace tailWord_2540742 prefixEnd_2540742 1304621865065803568940347 := by
  unfold tailWord_2540742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2895889805041660407257515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61778982507555422021493653 2895889805041660407257515)
  ·
    refine ⟨4343834707562490610886273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2895889805041660407257515 4343834707562490610886273)
    ·
      refine ⟨3257876030671867958164705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4343834707562490610886273 3257876030671867958164705)
      ·
        refine ⟨2443407023003900968623529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3257876030671867958164705 2443407023003900968623529)
        ·
          refine ⟨1832555267252925726467647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2443407023003900968623529 1832555267252925726467647)
          ·
            refine ⟨2748832900879388589701471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1832555267252925726467647 2748832900879388589701471)
            ·
              refine ⟨4123249351319082884552207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2748832900879388589701471 4123249351319082884552207)
              ·
                refine ⟨6184874026978624326828311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4123249351319082884552207 6184874026978624326828311)
                ·
                  refine ⟨9277311040467936490242467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6184874026978624326828311 9277311040467936490242467)
                  ·
                    refine ⟨13915966560701904735363701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9277311040467936490242467 13915966560701904735363701)
                    ·
                      refine ⟨1304621865065803568940347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13915966560701904735363701 1304621865065803568940347)
                      ·
                        rfl

theorem cell23_2540742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_2540742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540742 prefixEnd_2540742 := by exact prefixLift 2540742
  have htrace : WordTrace (prefixWord ++ tailWord_2540742) baseStart_2540742 baseEnd_2540742 := by
    simpa [prefixWord, tailWord_2540742, baseEnd_2540742] using wordTrace_append hprefix tailTrace_2540742
  have hstable : (prefixWord ++ tailWord_2540742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540742).length < 2 ^ (prefixWord ++ tailWord_2540742).sum := by decide
  have hdescent : baseEnd_2540742 < baseStart_2540742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540744 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 3, 4, 2]
def baseStart_2540744 : Nat := 118140960795 + 2540744 * 2 ^ 59
def prefixEnd_2540744 : Nat := 4983230072969 + 3 ^ 40 * 2540744 * 2
def baseEnd_2540744 : Nat := 1304622892027112561115337

theorem tailTrace_2540744 : CollatzResearch.WordTrace tailWord_2540744 prefixEnd_2540744 1304622892027112561115337 := by
  unfold tailWord_2540744
  simp only [CollatzResearch.WordTrace]
  refine ⟨46334273353662943686906643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61779031138217258249208857 46334273353662943686906643)
  ·
    refine ⟨69501410030494415530359965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46334273353662943686906643 69501410030494415530359965)
    ·
      refine ⟨26063028761435405823884987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69501410030494415530359965 26063028761435405823884987)
      ·
        refine ⟨39094543142153108735827481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26063028761435405823884987 39094543142153108735827481)
        ·
          refine ⟨29320907356614831551870611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39094543142153108735827481 29320907356614831551870611)
          ·
            refine ⟨43981361034922247327805917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29320907356614831551870611 43981361034922247327805917)
            ·
              refine ⟨16493010388095842747927219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43981361034922247327805917 16493010388095842747927219)
              ·
                refine ⟨24739515582143764121890829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16493010388095842747927219 24739515582143764121890829)
                ·
                  refine ⟨9277318343303911545709061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24739515582143764121890829 9277318343303911545709061)
                  ·
                    refine ⟨1739497189369483414820449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9277318343303911545709061 1739497189369483414820449)
                    ·
                      refine ⟨1304622892027112561115337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1739497189369483414820449 1304622892027112561115337)
                      ·
                        rfl

theorem cell23_2540744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_2540744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540744 prefixEnd_2540744 := by exact prefixLift 2540744
  have htrace : WordTrace (prefixWord ++ tailWord_2540744) baseStart_2540744 baseEnd_2540744 := by
    simpa [prefixWord, tailWord_2540744, baseEnd_2540744] using wordTrace_append hprefix tailTrace_2540744
  have hstable : (prefixWord ++ tailWord_2540744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540744).length < 2 ^ (prefixWord ++ tailWord_2540744).sum := by decide
  have hdescent : baseEnd_2540744 < baseStart_2540744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540756 : List Nat := [2, 4, 1, 4, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2540756 : Nat := 118140960795 + 2540756 * 2 ^ 59
def prefixEnd_2540756 : Nat := 4983230072969 + 3 ^ 40 * 2540756 * 2
def baseEnd_2540756 : Nat := 1304629053794966514165283

theorem tailTrace_2540756 : CollatzResearch.WordTrace tailWord_2540756 prefixEnd_2540756 1304629053794966514165283 := by
  unfold tailWord_2540756
  simp only [CollatzResearch.WordTrace]
  refine ⟨46334492191641206711625061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61779322922188275615500081 46334492191641206711625061)
  ·
    refine ⟨8687717285932726258429699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46334492191641206711625061 8687717285932726258429699)
    ·
      refine ⟨13031575928899089387644549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8687717285932726258429699 13031575928899089387644549)
      ·
        refine ⟨2443420486668579260183353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13031575928899089387644549 2443420486668579260183353)
        ·
          refine ⟨1832565365001434445137515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2443420486668579260183353 1832565365001434445137515)
          ·
            refine ⟨2748848047502151667706273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1832565365001434445137515 2748848047502151667706273)
            ·
              refine ⟨2061636035626613750779705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2748848047502151667706273 2061636035626613750779705)
              ·
                refine ⟨1546227026719960313084779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061636035626613750779705 1546227026719960313084779)
                ·
                  refine ⟨2319340540079940469627169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1546227026719960313084779 2319340540079940469627169)
                  ·
                    refine ⟨1739505405059955352220377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2319340540079940469627169 1739505405059955352220377)
                    ·
                      refine ⟨1304629053794966514165283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1739505405059955352220377 1304629053794966514165283)
                      ·
                        rfl

theorem cell23_2540756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2540756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540756 prefixEnd_2540756 := by exact prefixLift 2540756
  have htrace : WordTrace (prefixWord ++ tailWord_2540756) baseStart_2540756 baseEnd_2540756 := by
    simpa [prefixWord, tailWord_2540756, baseEnd_2540756] using wordTrace_append hprefix tailTrace_2540756
  have hstable : (prefixWord ++ tailWord_2540756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540756).length < 2 ^ (prefixWord ++ tailWord_2540756).sum := by decide
  have hdescent : baseEnd_2540756 < baseStart_2540756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540778 : List Nat := [3, 1, 3, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_2540778 : Nat := 118140960795 + 2540778 * 2 ^ 59
def prefixEnd_2540778 : Nat := 4983230072969 + 3 ^ 40 * 2540778 * 2
def baseEnd_2540778 : Nat := 1304640350369365428090181

theorem tailTrace_2540778 : CollatzResearch.WordTrace tailWord_2540778 prefixEnd_2540778 1304640350369365428090181 := by
  unfold tailWord_2540778
  simp only [CollatzResearch.WordTrace]
  refine ⟨23167446697300677795137747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61779857859468474120367325 23167446697300677795137747)
  ·
    refine ⟨34751170045951016692706621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23167446697300677795137747 34751170045951016692706621)
    ·
      refine ⟨13031688767231631259764983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34751170045951016692706621 13031688767231631259764983)
      ·
        refine ⟨19547533150847446889647475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13031688767231631259764983 19547533150847446889647475)
        ·
          refine ⟨29321299726271170334471213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19547533150847446889647475 29321299726271170334471213)
          ·
            refine ⟨10995487397351688875426705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29321299726271170334471213 10995487397351688875426705)
            ·
              refine ⟨8246615548013766656570029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10995487397351688875426705 8246615548013766656570029)
              ·
                refine ⟨3092480830505162496213761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8246615548013766656570029 3092480830505162496213761)
                ·
                  refine ⟨2319360622878871872160321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3092480830505162496213761 2319360622878871872160321)
                  ·
                    refine ⟨1739520467159153904120241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2319360622878871872160321 1739520467159153904120241)
                    ·
                      refine ⟨1304640350369365428090181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1739520467159153904120241 1304640350369365428090181)
                      ·
                        rfl

theorem cell23_2540778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_2540778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540778 prefixEnd_2540778 := by exact prefixLift 2540778
  have htrace : WordTrace (prefixWord ++ tailWord_2540778) baseStart_2540778 baseEnd_2540778 := by
    simpa [prefixWord, tailWord_2540778, baseEnd_2540778] using wordTrace_append hprefix tailTrace_2540778
  have hstable : (prefixWord ++ tailWord_2540778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540778).length < 2 ^ (prefixWord ++ tailWord_2540778).sum := by decide
  have hdescent : baseEnd_2540778 < baseStart_2540778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540801 : List Nat := [1, 2, 4, 1, 1, 4, 2, 3, 5]
def baseStart_2540801 : Nat := 118140960795 + 2540801 * 2 ^ 59
def prefixEnd_2540801 : Nat := 4983230072969 + 3 ^ 40 * 2540801 * 2
def baseEnd_2540801 : Nat := 144961351158268759789175

theorem tailTrace_2540801 : CollatzResearch.WordTrace tailWord_2540801 prefixEnd_2540801 144961351158268759789175 := by
  unfold tailWord_2540801
  simp only [CollatzResearch.WordTrace]
  refine ⟨92670625668119386108638257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61780417112079590739092171 92670625668119386108638257)
  ·
    refine ⟨69502969251089539581478693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92670625668119386108638257 69502969251089539581478693)
    ·
      refine ⟨13031806734579288671527255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69502969251089539581478693 13031806734579288671527255)
      ·
        refine ⟨19547710101868933007290883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13031806734579288671527255 19547710101868933007290883)
        ·
          refine ⟨29321565152803399510936325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19547710101868933007290883 29321565152803399510936325)
          ·
            refine ⟨5497793466150637408300561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29321565152803399510936325 5497793466150637408300561)
            ·
              refine ⟨4123345099612978056225421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5497793466150637408300561 4123345099612978056225421)
              ·
                refine ⟨1546254412354866771084533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4123345099612978056225421 1546254412354866771084533)
                ·
                  refine ⟨144961351158268759789175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1546254412354866771084533 144961351158268759789175)
                  ·
                    rfl

theorem cell23_2540801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 5].length) (baseStart_2540801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540801 prefixEnd_2540801 := by exact prefixLift 2540801
  have htrace : WordTrace (prefixWord ++ tailWord_2540801) baseStart_2540801 baseEnd_2540801 := by
    simpa [prefixWord, tailWord_2540801, baseEnd_2540801] using wordTrace_append hprefix tailTrace_2540801
  have hstable : (prefixWord ++ tailWord_2540801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540801).length < 2 ^ (prefixWord ++ tailWord_2540801).sum := by decide
  have hdescent : baseEnd_2540801 < baseStart_2540801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540818 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 7]
def baseStart_2540818 : Nat := 118140960795 + 2540818 * 2 ^ 59
def prefixEnd_2540818 : Nat := 4983230072969 + 3 ^ 40 * 2540818 * 2
def baseEnd_2540818 : Nat := 144962321066171696843333

theorem tailTrace_2540818 : CollatzResearch.WordTrace tailWord_2540818 prefixEnd_2540818 144962321066171696843333 := by
  unfold tailWord_2540818
  simp only [CollatzResearch.WordTrace]
  refine ⟨23167811427264449503001777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61780830472705198674671405 23167811427264449503001777)
  ·
    refine ⟨17375858570448337127251333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23167811427264449503001777 17375858570448337127251333)
    ·
      refine ⟨3257973481959063211359625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17375858570448337127251333 3257973481959063211359625)
      ·
        refine ⟨2443480111469297408519719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3257973481959063211359625 2443480111469297408519719)
        ·
          refine ⟨3665220167203946112779579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2443480111469297408519719 3665220167203946112779579)
          ·
            refine ⟨5497830250805919169169369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665220167203946112779579 5497830250805919169169369)
            ·
              refine ⟨4123372688104439376877027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5497830250805919169169369 4123372688104439376877027)
              ·
                refine ⟨6185059032156659065315541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4123372688104439376877027 6185059032156659065315541)
                ·
                  refine ⟨144962321066171696843333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6185059032156659065315541 144962321066171696843333)
                  ·
                    rfl

theorem cell23_2540818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_2540818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540818 prefixEnd_2540818 := by exact prefixLift 2540818
  have htrace : WordTrace (prefixWord ++ tailWord_2540818) baseStart_2540818 baseEnd_2540818 := by
    simpa [prefixWord, tailWord_2540818, baseEnd_2540818] using wordTrace_append hprefix tailTrace_2540818
  have hstable : (prefixWord ++ tailWord_2540818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540818).length < 2 ^ (prefixWord ++ tailWord_2540818).sum := by decide
  have hdescent : baseEnd_2540818 < baseStart_2540818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540847 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 4]
def baseStart_2540847 : Nat := 118140960795 + 2540847 * 2 ^ 59
def prefixEnd_2540847 : Nat := 4983230072969 + 3 ^ 40 * 2540847 * 2
def baseEnd_2540847 : Nat := 1304675780534525658127363

theorem tailTrace_2540847 : CollatzResearch.WordTrace tailWord_2540847 prefixEnd_2540847 1304675780534525658127363 := by
  unfold tailWord_2540847
  simp only [CollatzResearch.WordTrace]
  refine ⟨92672303425952735964812795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61781535617301823976541863 92672303425952735964812795)
  ·
    refine ⟨139008455138929103947219193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92672303425952735964812795 139008455138929103947219193)
    ·
      refine ⟨104256341354196827960414395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139008455138929103947219193 104256341354196827960414395)
      ·
        refine ⟨156384512031295241940621593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104256341354196827960414395 156384512031295241940621593)
        ·
          refine ⟨117288384023471431455466195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156384512031295241940621593 117288384023471431455466195)
          ·
            refine ⟨175932576035207147183199293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117288384023471431455466195 175932576035207147183199293)
            ·
              refine ⟨65974716013202680193699735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175932576035207147183199293 65974716013202680193699735)
              ·
                refine ⟨98962074019804020290549603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65974716013202680193699735 98962074019804020290549603)
                ·
                  refine ⟨148443111029706030435824405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98962074019804020290549603 148443111029706030435824405)
                  ·
                    refine ⟨6958270829517470176679269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 148443111029706030435824405 6958270829517470176679269)
                    ·
                      refine ⟨1304675780534525658127363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6958270829517470176679269 1304675780534525658127363)
                      ·
                        rfl

theorem cell23_2540847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_2540847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540847 prefixEnd_2540847 := by exact prefixLift 2540847
  have htrace : WordTrace (prefixWord ++ tailWord_2540847) baseStart_2540847 baseEnd_2540847 := by
    simpa [prefixWord, tailWord_2540847, baseEnd_2540847] using wordTrace_append hprefix tailTrace_2540847
  have hstable : (prefixWord ++ tailWord_2540847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540847).length < 2 ^ (prefixWord ++ tailWord_2540847).sum := by decide
  have hdescent : baseEnd_2540847 < baseStart_2540847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540868 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2540868 : Nat := 118140960795 + 2540868 * 2 ^ 59
def prefixEnd_2540868 : Nat := 4983230072969 + 3 ^ 40 * 2540868 * 2
def baseEnd_2540868 : Nat := 1304686563628270075964767

theorem tailTrace_2540868 : CollatzResearch.WordTrace tailWord_2540868 prefixEnd_2540868 1304686563628270075964767 := by
  unfold tailWord_2540868
  simp only [CollatzResearch.WordTrace]
  refine ⟨46336534679438328275663629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61782046239251104367551505 46336534679438328275663629)
  ·
    refine ⟨17376200504789373103373861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46336534679438328275663629 17376200504789373103373861)
    ·
      refine ⟨3258037594648007456882599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17376200504789373103373861 3258037594648007456882599)
      ·
        refine ⟨4887056391972011185323899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3258037594648007456882599 4887056391972011185323899)
        ·
          refine ⟨7330584587958016777985849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4887056391972011185323899 7330584587958016777985849)
          ·
            refine ⟨5497938440968512583489387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7330584587958016777985849 5497938440968512583489387)
            ·
              refine ⟨8246907661452768875234081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497938440968512583489387 8246907661452768875234081)
              ·
                refine ⟨6185180746089576656425561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8246907661452768875234081 6185180746089576656425561)
                ·
                  refine ⟨4638885559567182492319171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6185180746089576656425561 4638885559567182492319171)
                  ·
                    refine ⟨6958328339350773738478757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4638885559567182492319171 6958328339350773738478757)
                    ·
                      refine ⟨1304686563628270075964767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6958328339350773738478757 1304686563628270075964767)
                      ·
                        rfl

theorem cell23_2540868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2540868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540868 prefixEnd_2540868 := by exact prefixLift 2540868
  have htrace : WordTrace (prefixWord ++ tailWord_2540868) baseStart_2540868 baseEnd_2540868 := by
    simpa [prefixWord, tailWord_2540868, baseEnd_2540868] using wordTrace_append hprefix tailTrace_2540868
  have hstable : (prefixWord ++ tailWord_2540868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540868).length < 2 ^ (prefixWord ++ tailWord_2540868).sum := by decide
  have hdescent : baseEnd_2540868 < baseStart_2540868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540871 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_2540871 : Nat := 118140960795 + 2540871 * 2 ^ 59
def prefixEnd_2540871 : Nat := 4983230072969 + 3 ^ 40 * 2540871 * 2
def baseEnd_2540871 : Nat := 1304688104070233564227253

theorem tailTrace_2540871 : CollatzResearch.WordTrace tailWord_2540871 prefixEnd_2540871 1304688104070233564227253 := by
  unfold tailWord_2540871
  simp only [CollatzResearch.WordTrace]
  refine ⟨92673178777865788063686467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61782119185243858709124311 92673178777865788063686467)
  ·
    refine ⟨139009768166798682095529701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92673178777865788063686467 139009768166798682095529701)
    ·
      refine ⟨26064331531274752892911819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139009768166798682095529701 26064331531274752892911819)
      ·
        refine ⟨39096497296912129339367729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26064331531274752892911819 39096497296912129339367729)
        ·
          refine ⟨29322372972684097004525797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39096497296912129339367729 29322372972684097004525797)
          ·
            refine ⟨5497944932378268188348587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29322372972684097004525797 5497944932378268188348587)
            ·
              refine ⟨8246917398567402282522881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497944932378268188348587 8246917398567402282522881)
              ·
                refine ⟨6185188048925551711892161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8246917398567402282522881 6185188048925551711892161)
                ·
                  refine ⟨4638891036694163783919121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6185188048925551711892161 4638891036694163783919121)
                  ·
                    refine ⟨3479168277520622837939341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4638891036694163783919121 3479168277520622837939341)
                    ·
                      refine ⟨1304688104070233564227253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3479168277520622837939341 1304688104070233564227253)
                      ·
                        rfl

theorem cell23_2540871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_2540871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540871 prefixEnd_2540871 := by exact prefixLift 2540871
  have htrace : WordTrace (prefixWord ++ tailWord_2540871) baseStart_2540871 baseEnd_2540871 := by
    simpa [prefixWord, tailWord_2540871, baseEnd_2540871] using wordTrace_append hprefix tailTrace_2540871
  have hstable : (prefixWord ++ tailWord_2540871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540871).length < 2 ^ (prefixWord ++ tailWord_2540871).sum := by decide
  have hdescent : baseEnd_2540871 < baseStart_2540871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540901 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 5, 1, 3]
def baseStart_2540901 : Nat := 118140960795 + 2540901 * 2 ^ 59
def prefixEnd_2540901 : Nat := 4983230072969 + 3 ^ 40 * 2540901 * 2
def baseEnd_2540901 : Nat := 1304703508489868446852115

theorem tailTrace_2540901 : CollatzResearch.WordTrace tailWord_2540901 prefixEnd_2540901 1304703508489868446852115 := by
  unfold tailWord_2540901
  simp only [CollatzResearch.WordTrace]
  refine ⟨92674272967757103187278557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61782848645171402124852371 92674272967757103187278557)
  ·
    refine ⟨34752852362908913695229459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92674272967757103187278557 34752852362908913695229459)
    ·
      refine ⟨52129278544363370542844189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34752852362908913695229459 52129278544363370542844189)
      ·
        refine ⟨19548479454136263953566571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52129278544363370542844189 19548479454136263953566571)
        ·
          refine ⟨29322719181204395930349857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19548479454136263953566571 29322719181204395930349857)
          ·
            refine ⟨21992039385903296947762393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29322719181204395930349857 21992039385903296947762393)
            ·
              refine ⟨16494029539427472710821795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21992039385903296947762393 16494029539427472710821795)
              ·
                refine ⟨24741044309141209066232693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16494029539427472710821795 24741044309141209066232693)
                ·
                  refine ⟨2319472903981988349959315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24741044309141209066232693 2319472903981988349959315)
                  ·
                    refine ⟨3479209355972982524938973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2319472903981988349959315 3479209355972982524938973)
                    ·
                      refine ⟨1304703508489868446852115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3479209355972982524938973 1304703508489868446852115)
                      ·
                        rfl

theorem cell23_2540901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_2540901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540901 prefixEnd_2540901 := by exact prefixLift 2540901
  have htrace : WordTrace (prefixWord ++ tailWord_2540901) baseStart_2540901 baseEnd_2540901 := by
    simpa [prefixWord, tailWord_2540901, baseEnd_2540901] using wordTrace_append hprefix tailTrace_2540901
  have hstable : (prefixWord ++ tailWord_2540901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540901).length < 2 ^ (prefixWord ++ tailWord_2540901).sum := by decide
  have hdescent : baseEnd_2540901 < baseStart_2540901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540929 : List Nat := [1, 2, 4, 3, 3, 1, 2, 2, 1, 4]
def baseStart_2540929 : Nat := 118140960795 + 2540929 * 2 ^ 59
def prefixEnd_2540929 : Nat := 4983230072969 + 3 ^ 40 * 2540929 * 2
def baseEnd_2540929 : Nat := 434905961982731445767329

theorem tailTrace_2540929 : CollatzResearch.WordTrace tailWord_2540929 prefixEnd_2540929 434905961982731445767329 := by
  unfold tailWord_2540929
  simp only [CollatzResearch.WordTrace]
  refine ⟨92675294211655663969297841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61783529474437109312865227 92675294211655663969297841)
  ·
    refine ⟨69506470658741747976973381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92675294211655663969297841 69506470658741747976973381)
    ·
      refine ⟨13032463248514077745682509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69506470658741747976973381 13032463248514077745682509)
      ·
        refine ⟨4887173718192779154630941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13032463248514077745682509 4887173718192779154630941)
        ·
          refine ⟨1832690144322292182986603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4887173718192779154630941 1832690144322292182986603)
          ·
            refine ⟨2749035216483438274479905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1832690144322292182986603 2749035216483438274479905)
            ·
              refine ⟨2061776412362578705859929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2749035216483438274479905 2061776412362578705859929)
              ·
                refine ⟨1546332309271934029394947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061776412362578705859929 1546332309271934029394947)
                ·
                  refine ⟨2319498463907901044092421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1546332309271934029394947 2319498463907901044092421)
                  ·
                    refine ⟨434905961982731445767329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2319498463907901044092421 434905961982731445767329)
                    ·
                      rfl

theorem cell23_2540929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_2540929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540929 prefixEnd_2540929 := by exact prefixLift 2540929
  have htrace : WordTrace (prefixWord ++ tailWord_2540929) baseStart_2540929 baseEnd_2540929 := by
    simpa [prefixWord, tailWord_2540929, baseEnd_2540929] using wordTrace_append hprefix tailTrace_2540929
  have hstable : (prefixWord ++ tailWord_2540929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540929).length < 2 ^ (prefixWord ++ tailWord_2540929).sum := by decide
  have hdescent : baseEnd_2540929 < baseStart_2540929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540935 : List Nat := [1, 1, 4, 2, 2, 3, 1, 4, 1, 1, 3]
def baseStart_2540935 : Nat := 118140960795 + 2540935 * 2 ^ 59
def prefixEnd_2540935 : Nat := 4983230072969 + 3 ^ 40 * 2540935 * 2
def baseEnd_2540935 : Nat := 1304720966832121313826959

theorem tailTrace_2540935 : CollatzResearch.WordTrace tailWord_2540935 prefixEnd_2540935 1304720966832121313826959 := by
  unfold tailWord_2540935
  simp only [CollatzResearch.WordTrace]
  refine ⟨92675513049633926994016259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61783675366422617996010839 92675513049633926994016259)
  ·
    refine ⟨139013269574450890491024389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92675513049633926994016259 139013269574450890491024389)
    ·
      refine ⟨26064988045209541967067073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139013269574450890491024389 26064988045209541967067073)
      ·
        refine ⟨19548741033907156475300305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26064988045209541967067073 19548741033907156475300305)
        ·
          refine ⟨14661555775430367356475229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19548741033907156475300305 14661555775430367356475229)
          ·
            refine ⟨5498083415786387758678211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14661555775430367356475229 5498083415786387758678211)
            ·
              refine ⟨8247125123679581638017317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5498083415786387758678211 8247125123679581638017317)
              ·
                refine ⟨1546335960689921557128247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8247125123679581638017317 1546335960689921557128247)
                ·
                  refine ⟨2319503941034882335692371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1546335960689921557128247 2319503941034882335692371)
                  ·
                    refine ⟨3479255911552323503538557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2319503941034882335692371 3479255911552323503538557)
                    ·
                      refine ⟨1304720966832121313826959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3479255911552323503538557 1304720966832121313826959)
                      ·
                        rfl

theorem cell23_2540935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_2540935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540935 prefixEnd_2540935 := by exact prefixLift 2540935
  have htrace : WordTrace (prefixWord ++ tailWord_2540935) baseStart_2540935 baseEnd_2540935 := by
    simpa [prefixWord, tailWord_2540935, baseEnd_2540935] using wordTrace_append hprefix tailTrace_2540935
  have hstable : (prefixWord ++ tailWord_2540935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540935).length < 2 ^ (prefixWord ++ tailWord_2540935).sum := by decide
  have hdescent : baseEnd_2540935 < baseStart_2540935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2540985 : List Nat := [1, 2, 1, 4, 4, 2, 1, 2, 2, 4]
def baseStart_2540985 : Nat := 118140960795 + 2540985 * 2 ^ 59
def prefixEnd_2540985 : Nat := 4983230072969 + 3 ^ 40 * 2540985 * 2
def baseEnd_2540985 : Nat := 434915546954948706067243

theorem tailTrace_2540985 : CollatzResearch.WordTrace tailWord_2540985 prefixEnd_2540985 434915546954948706067243 := by
  unfold tailWord_2540985
  simp only [CollatzResearch.WordTrace]
  refine ⟨92677336699452785533336409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61784891132968523688890939 92677336699452785533336409)
  ·
    refine ⟨69508002524589589150002307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92677336699452785533336409 69508002524589589150002307)
    ·
      refine ⟨104262003786884383725003461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69508002524589589150002307 104262003786884383725003461)
      ·
        refine ⟨19549125710040821948438149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104262003786884383725003461 19549125710040821948438149)
        ·
          refine ⟨3665461070632654115332153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19549125710040821948438149 3665461070632654115332153)
          ·
            refine ⟨2749095802974490586499115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3665461070632654115332153 2749095802974490586499115)
            ·
              refine ⟨4123643704461735879748673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2749095802974490586499115 4123643704461735879748673)
              ·
                refine ⟨3092732778346301909811505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4123643704461735879748673 3092732778346301909811505)
                ·
                  refine ⟨2319549583759726432358629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3092732778346301909811505 2319549583759726432358629)
                  ·
                    refine ⟨434915546954948706067243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2319549583759726432358629 434915546954948706067243)
                    ·
                      rfl

theorem cell23_2540985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 4].length) (baseStart_2540985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2540985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2540985 prefixEnd_2540985 := by exact prefixLift 2540985
  have htrace : WordTrace (prefixWord ++ tailWord_2540985) baseStart_2540985 baseEnd_2540985 := by
    simpa [prefixWord, tailWord_2540985, baseEnd_2540985] using wordTrace_append hprefix tailTrace_2540985
  have hstable : (prefixWord ++ tailWord_2540985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2540985).length < 2 ^ (prefixWord ++ tailWord_2540985).sum := by decide
  have hdescent : baseEnd_2540985 < baseStart_2540985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2540985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541021 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2541021 : Nat := 118140960795 + 2541021 * 2 ^ 59
def prefixEnd_2541021 : Nat := 4983230072969 + 3 ^ 40 * 2541021 * 2
def baseEnd_2541021 : Nat := 1304765126168407977351563

theorem tailTrace_2541021 : CollatzResearch.WordTrace tailWord_2541021 prefixEnd_2541021 1304765126168407977351563 := by
  unfold tailWord_2541021
  simp only [CollatzResearch.WordTrace]
  refine ⟨92678649727322363681646917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61785766484881575787764611 92678649727322363681646917)
  ·
    refine ⟨17377246823872943190308797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92678649727322363681646917 17377246823872943190308797)
    ·
      refine ⟨6516467558952353696365799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17377246823872943190308797 6516467558952353696365799)
      ·
        refine ⟨9774701338428530544548699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6516467558952353696365799 9774701338428530544548699)
        ·
          refine ⟨14662052007642795816823049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9774701338428530544548699 14662052007642795816823049)
          ·
            refine ⟨10996539005732096862617287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14662052007642795816823049 10996539005732096862617287)
            ·
              refine ⟨16494808508598145293925931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10996539005732096862617287 16494808508598145293925931)
              ·
                refine ⟨24742212762897217940888897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16494808508598145293925931 24742212762897217940888897)
                ·
                  refine ⟨18556659572172913455666673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24742212762897217940888897 18556659572172913455666673)
                  ·
                    refine ⟨13917494679129685091750005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18556659572172913455666673 13917494679129685091750005)
                    ·
                      refine ⟨1304765126168407977351563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13917494679129685091750005 1304765126168407977351563)
                      ·
                        rfl

theorem cell23_2541021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2541021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541021 prefixEnd_2541021 := by exact prefixLift 2541021
  have htrace : WordTrace (prefixWord ++ tailWord_2541021) baseStart_2541021 baseEnd_2541021 := by
    simpa [prefixWord, tailWord_2541021, baseEnd_2541021] using wordTrace_append hprefix tailTrace_2541021
  have hstable : (prefixWord ++ tailWord_2541021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541021).length < 2 ^ (prefixWord ++ tailWord_2541021).sum := by decide
  have hdescent : baseEnd_2541021 < baseStart_2541021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541024 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 4, 6]
def baseStart_2541024 : Nat := 118140960795 + 2541024 * 2 ^ 59
def prefixEnd_2541024 : Nat := 4983230072969 + 3 ^ 40 * 2541024 * 2
def baseEnd_2541024 : Nat := 434922222203457155204683

theorem tailTrace_2541024 : CollatzResearch.WordTrace tailWord_2541024 prefixEnd_2541024 434922222203457155204683 := by
  unfold tailWord_2541024
  simp only [CollatzResearch.WordTrace]
  refine ⟨46339379573155747597003063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61785839430874330129337417 46339379573155747597003063)
  ·
    refine ⟨69509069359733621395504595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46339379573155747597003063 69509069359733621395504595)
    ·
      refine ⟨104263604039600432093256893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69509069359733621395504595 104263604039600432093256893)
      ·
        refine ⟨39098851514850162034971335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104263604039600432093256893 39098851514850162034971335)
        ·
          refine ⟨58648277272275243052457003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39098851514850162034971335 58648277272275243052457003)
          ·
            refine ⟨87972415908412864578685505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58648277272275243052457003 87972415908412864578685505)
            ·
              refine ⟨65979311931309648434014129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87972415908412864578685505 65979311931309648434014129)
              ·
                refine ⟨49484483948482236325510597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65979311931309648434014129 49484483948482236325510597)
                ·
                  refine ⟨9278340740340419311033237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49484483948482236325510597 9278340740340419311033237)
                  ·
                    refine ⟨434922222203457155204683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9278340740340419311033237 434922222203457155204683)
                    ·
                      rfl

theorem cell23_2541024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4, 6].length) (baseStart_2541024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541024 prefixEnd_2541024 := by exact prefixLift 2541024
  have htrace : WordTrace (prefixWord ++ tailWord_2541024) baseStart_2541024 baseEnd_2541024 := by
    simpa [prefixWord, tailWord_2541024, baseEnd_2541024] using wordTrace_append hprefix tailTrace_2541024
  have hstable : (prefixWord ++ tailWord_2541024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541024).length < 2 ^ (prefixWord ++ tailWord_2541024).sum := by decide
  have hdescent : baseEnd_2541024 < baseStart_2541024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541065 : List Nat := [1, 2, 1, 1, 3, 1, 5, 3, 2, 2, 2]
def baseStart_2541065 : Nat := 118140960795 + 2541065 * 2 ^ 59
def prefixEnd_2541065 : Nat := 4983230072969 + 3 ^ 40 * 2541065 * 2
def baseEnd_2541065 : Nat := 1304787719317205805201361

theorem tailTrace_2541065 : CollatzResearch.WordTrace tailWord_2541065 prefixEnd_2541065 1304787719317205805201361 := by
  unfold tailWord_2541065
  simp only [CollatzResearch.WordTrace]
  refine ⟨92680254539162959196248649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61786836359441972797499099 92680254539162959196248649)
  ·
    refine ⟨69510190904372219397186487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92680254539162959196248649 69510190904372219397186487)
    ·
      refine ⟨104265286356558329095779731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69510190904372219397186487 104265286356558329095779731)
      ·
        refine ⟨156397929534837493643669597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104265286356558329095779731 156397929534837493643669597)
        ·
          refine ⟨58649223575564060116376099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156397929534837493643669597 58649223575564060116376099)
          ·
            refine ⟨87973835363346090174564149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58649223575564060116376099 87973835363346090174564149)
            ·
              refine ⟨8247547065313695953865389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87973835363346090174564149 8247547065313695953865389)
              ·
                refine ⟨3092830149492635982699521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8247547065313695953865389 3092830149492635982699521)
                ·
                  refine ⟨2319622612119476987024641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3092830149492635982699521 2319622612119476987024641)
                  ·
                    refine ⟨1739716959089607740268481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2319622612119476987024641 1739716959089607740268481)
                    ·
                      refine ⟨1304787719317205805201361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1739716959089607740268481 1304787719317205805201361)
                      ·
                        rfl

theorem cell23_2541065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 2, 2].length) (baseStart_2541065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541065 prefixEnd_2541065 := by exact prefixLift 2541065
  have htrace : WordTrace (prefixWord ++ tailWord_2541065) baseStart_2541065 baseEnd_2541065 := by
    simpa [prefixWord, tailWord_2541065, baseEnd_2541065] using wordTrace_append hprefix tailTrace_2541065
  have hstable : (prefixWord ++ tailWord_2541065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541065).length < 2 ^ (prefixWord ++ tailWord_2541065).sum := by decide
  have hdescent : baseEnd_2541065 < baseStart_2541065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541069 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_2541069 : Nat := 118140960795 + 2541069 * 2 ^ 59
def prefixEnd_2541069 : Nat := 4983230072969 + 3 ^ 40 * 2541069 * 2
def baseEnd_2541069 : Nat := 1304789773239823789551343

theorem tailTrace_2541069 : CollatzResearch.WordTrace tailWord_2541069 prefixEnd_2541069 1304789773239823789551343 := by
  unfold tailWord_2541069
  simp only [CollatzResearch.WordTrace]
  refine ⟨92680400431148467879394261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61786933620765645252929507 92680400431148467879394261)
  ·
    refine ⟨2172196885105042215923303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 92680400431148467879394261 2172196885105042215923303)
    ·
      refine ⟨3258295327657563323884955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2172196885105042215923303 3258295327657563323884955)
      ·
        refine ⟨4887442991486344985827433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3258295327657563323884955 4887442991486344985827433)
        ·
          refine ⟨3665582243614758739370575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4887442991486344985827433 3665582243614758739370575)
          ·
            refine ⟨5498373365422138109055863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665582243614758739370575 5498373365422138109055863)
            ·
              refine ⟨8247560048133207163583795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5498373365422138109055863 8247560048133207163583795)
              ·
                refine ⟨12371340072199810745375693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8247560048133207163583795 12371340072199810745375693)
                ·
                  refine ⟨4639252527074929029515885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12371340072199810745375693 4639252527074929029515885)
                  ·
                    refine ⟨1739719697653098386068457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4639252527074929029515885 1739719697653098386068457)
                    ·
                      refine ⟨1304789773239823789551343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1739719697653098386068457 1304789773239823789551343)
                      ·
                        rfl

theorem cell23_2541069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_2541069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541069 prefixEnd_2541069 := by exact prefixLift 2541069
  have htrace : WordTrace (prefixWord ++ tailWord_2541069) baseStart_2541069 baseEnd_2541069 := by
    simpa [prefixWord, tailWord_2541069, baseEnd_2541069] using wordTrace_append hprefix tailTrace_2541069
  have hstable : (prefixWord ++ tailWord_2541069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541069).length < 2 ^ (prefixWord ++ tailWord_2541069).sum := by decide
  have hdescent : baseEnd_2541069 < baseStart_2541069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541098 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_2541098 : Nat := 118140960795 + 2541098 * 2 ^ 59
def prefixEnd_2541098 : Nat := 4983230072969 + 3 ^ 40 * 2541098 * 2
def baseEnd_2541098 : Nat := 1304804664178804176088709

theorem tailTrace_2541098 : CollatzResearch.WordTrace tailWord_2541098 prefixEnd_2541098 1304804664178804176088709 := by
  unfold tailWord_2541098
  simp only [CollatzResearch.WordTrace]
  refine ⟨23170364537010851458049987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61787638765362270554799965 23170364537010851458049987)
  ·
    refine ⟨34755546805516277187074981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23170364537010851458049987 34755546805516277187074981)
    ·
      refine ⟨6516665026034301972576559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34755546805516277187074981 6516665026034301972576559)
      ·
        refine ⟨9774997539051452958864839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6516665026034301972576559 9774997539051452958864839)
        ·
          refine ⟨14662496308577179438297259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9774997539051452958864839 14662496308577179438297259)
          ·
            refine ⟨21993744462865769157445889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14662496308577179438297259 21993744462865769157445889)
            ·
              refine ⟨16495308347149326868084417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21993744462865769157445889 16495308347149326868084417)
              ·
                refine ⟨12371481260361995151063313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16495308347149326868084417 12371481260361995151063313)
                ·
                  refine ⟨9278610945271496363297485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12371481260361995151063313 9278610945271496363297485)
                  ·
                    refine ⟨3479479104476811136236557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9278610945271496363297485 3479479104476811136236557)
                    ·
                      refine ⟨1304804664178804176088709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3479479104476811136236557 1304804664178804176088709)
                      ·
                        rfl

theorem cell23_2541098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_2541098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541098 prefixEnd_2541098 := by exact prefixLift 2541098
  have htrace : WordTrace (prefixWord ++ tailWord_2541098) baseStart_2541098 baseEnd_2541098 := by
    simpa [prefixWord, tailWord_2541098, baseEnd_2541098] using wordTrace_append hprefix tailTrace_2541098
  have hstable : (prefixWord ++ tailWord_2541098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541098).length < 2 ^ (prefixWord ++ tailWord_2541098).sum := by decide
  have hdescent : baseEnd_2541098 < baseStart_2541098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541111 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_2541111 : Nat := 118140960795 + 2541111 * 2 ^ 59
def prefixEnd_2541111 : Nat := 4983230072969 + 3 ^ 40 * 2541111 * 2
def baseEnd_2541111 : Nat := 1304811339427312625226149

theorem tailTrace_2541111 : CollatzResearch.WordTrace tailWord_2541111 prefixEnd_2541111 1304811339427312625226149 := by
  unfold tailWord_2541111
  simp only [CollatzResearch.WordTrace]
  refine ⟨92681932296996309052423187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61787954864664206034948791 92681932296996309052423187)
  ·
    refine ⟨139022898445494463578634781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92681932296996309052423187 139022898445494463578634781)
    ·
      refine ⟨52133586917060423841988043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139022898445494463578634781 52133586917060423841988043)
      ·
        refine ⟨78200380375590635762982065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52133586917060423841988043 78200380375590635762982065)
        ·
          refine ⟨58650285281692976822236549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78200380375590635762982065 58650285281692976822236549)
          ·
            refine ⟨10996928490317433154169353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58650285281692976822236549 10996928490317433154169353)
            ·
              refine ⟨8247696367738074865627015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10996928490317433154169353 8247696367738074865627015)
              ·
                refine ⟨12371544551607112298440523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8247696367738074865627015 12371544551607112298440523)
                ·
                  refine ⟨18557316827410668447660785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12371544551607112298440523 18557316827410668447660785)
                  ·
                    refine ⟨13917987620558001335745589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18557316827410668447660785 13917987620558001335745589)
                    ·
                      refine ⟨1304811339427312625226149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13917987620558001335745589 1304811339427312625226149)
                      ·
                        rfl

theorem cell23_2541111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_2541111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541111 prefixEnd_2541111 := by exact prefixLift 2541111
  have htrace : WordTrace (prefixWord ++ tailWord_2541111) baseStart_2541111 baseEnd_2541111 := by
    simpa [prefixWord, tailWord_2541111, baseEnd_2541111] using wordTrace_append hprefix tailTrace_2541111
  have hstable : (prefixWord ++ tailWord_2541111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541111).length < 2 ^ (prefixWord ++ tailWord_2541111).sum := by decide
  have hdescent : baseEnd_2541111 < baseStart_2541111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541138 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_2541138 : Nat := 118140960795 + 2541138 * 2 ^ 59
def prefixEnd_2541138 : Nat := 4983230072969 + 3 ^ 40 * 2541138 * 2
def baseEnd_2541138 : Nat := 1304825203404984019588525

theorem tailTrace_2541138 : CollatzResearch.WordTrace tailWord_2541138 prefixEnd_2541138 1304825203404984019588525 := by
  unfold tailWord_2541138
  simp only [CollatzResearch.WordTrace]
  refine ⟨23170729266974623165914017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61788611378598995109104045 23170729266974623165914017)
  ·
    refine ⟨17378046950230967374435513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23170729266974623165914017 17378046950230967374435513)
    ·
      refine ⟨13033535212673225530826635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17378046950230967374435513 13033535212673225530826635)
      ·
        refine ⟨19550302819009838296239953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13033535212673225530826635 19550302819009838296239953)
        ·
          refine ⟨14662727114257378722179965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19550302819009838296239953 14662727114257378722179965)
          ·
            refine ⟨5498522667846517020817487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14662727114257378722179965 5498522667846517020817487)
            ·
              refine ⟨8247784001769775531226231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5498522667846517020817487 8247784001769775531226231)
              ·
                refine ⟨12371676002654663296839347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8247784001769775531226231 12371676002654663296839347)
                ·
                  refine ⟨18557514003981994945259021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12371676002654663296839347 18557514003981994945259021)
                  ·
                    refine ⟨6959067751493248104472133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18557514003981994945259021 6959067751493248104472133)
                    ·
                      refine ⟨1304825203404984019588525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6959067751493248104472133 1304825203404984019588525)
                      ·
                        rfl

theorem cell23_2541138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_2541138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541138 prefixEnd_2541138 := by exact prefixLift 2541138
  have htrace : WordTrace (prefixWord ++ tailWord_2541138) baseStart_2541138 baseEnd_2541138 := by
    simpa [prefixWord, tailWord_2541138, baseEnd_2541138] using wordTrace_append hprefix tailTrace_2541138
  have hstable : (prefixWord ++ tailWord_2541138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541138).length < 2 ^ (prefixWord ++ tailWord_2541138).sum := by decide
  have hdescent : baseEnd_2541138 < baseStart_2541138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541262 : List Nat := [4, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4]
def baseStart_2541262 : Nat := 118140960795 + 2541262 * 2 ^ 59
def prefixEnd_2541262 : Nat := 4983230072969 + 3 ^ 40 * 2541262 * 2
def baseEnd_2541262 : Nat := 1304888875006141534437955

theorem tailTrace_2541262 : CollatzResearch.WordTrace tailWord_2541262 prefixEnd_2541262 1304888875006141534437955 := by
  unfold tailWord_2541262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11585929964931157730146255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61791626479632841227446693 11585929964931157730146255)
  ·
    refine ⟨17378894947396736595219383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11585929964931157730146255 17378894947396736595219383)
    ·
      refine ⟨26068342421095104892829075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17378894947396736595219383 26068342421095104892829075)
      ·
        refine ⟨39102513631642657339243613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26068342421095104892829075 39102513631642657339243613)
        ·
          refine ⟨14663442611865996502216355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39102513631642657339243613 14663442611865996502216355)
          ·
            refine ⟨21995163917798994753324533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14663442611865996502216355 21995163917798994753324533)
            ·
              refine ⟨2062046617293655758124175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21995163917798994753324533 2062046617293655758124175)
              ·
                refine ⟨3093069925940483637186263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062046617293655758124175 3093069925940483637186263)
                ·
                  refine ⟨4639604888910725455779395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3093069925940483637186263 4639604888910725455779395)
                  ·
                    refine ⟨6959407333366088183669093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4639604888910725455779395 6959407333366088183669093)
                    ·
                      refine ⟨1304888875006141534437955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6959407333366088183669093 1304888875006141534437955)
                      ·
                        rfl

theorem cell23_2541262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_2541262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541262 prefixEnd_2541262 := by exact prefixLift 2541262
  have htrace : WordTrace (prefixWord ++ tailWord_2541262) baseStart_2541262 baseEnd_2541262 := by
    simpa [prefixWord, tailWord_2541262, baseEnd_2541262] using wordTrace_append hprefix tailTrace_2541262
  have hstable : (prefixWord ++ tailWord_2541262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541262).length < 2 ^ (prefixWord ++ tailWord_2541262).sum := by decide
  have hdescent : baseEnd_2541262 < baseStart_2541262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541265 : List Nat := [1, 2, 2, 1, 2, 6, 1, 1, 1, 1, 5]
def baseStart_2541265 : Nat := 118140960795 + 2541265 * 2 ^ 59
def prefixEnd_2541265 : Nat := 4983230072969 + 3 ^ 40 * 2541265 * 2
def baseEnd_2541265 : Nat := 1304890415448105022700441

theorem tailTrace_2541265 : CollatzResearch.WordTrace tailWord_2541265 prefixEnd_2541265 1304890415448105022700441 := by
  unfold tailWord_2541265
  simp only [CollatzResearch.WordTrace]
  refine ⟨92687549138438393353529249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61791699425625595569019499 92687549138438393353529249)
  ·
    refine ⟨69515661853828795015146937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92687549138438393353529249 69515661853828795015146937)
    ·
      refine ⟨52136746390371596261360203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69515661853828795015146937 52136746390371596261360203)
      ·
        refine ⟨78205119585557394392040305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52136746390371596261360203 78205119585557394392040305)
        ·
          refine ⟨58653839689168045794030229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78205119585557394392040305 58653839689168045794030229)
          ·
            refine ⟨2749398735429752146595167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58653839689168045794030229 2749398735429752146595167)
            ·
              refine ⟨4124098103144628219892751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2749398735429752146595167 4124098103144628219892751)
              ·
                refine ⟨6186147154716942329839127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4124098103144628219892751 6186147154716942329839127)
                ·
                  refine ⟨9279220732075413494758691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6186147154716942329839127 9279220732075413494758691)
                  ·
                    refine ⟨13918831098113120242138037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9279220732075413494758691 13918831098113120242138037)
                    ·
                      refine ⟨1304890415448105022700441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13918831098113120242138037 1304890415448105022700441)
                      ·
                        rfl

theorem cell23_2541265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_2541265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541265 prefixEnd_2541265 := by exact prefixLift 2541265
  have htrace : WordTrace (prefixWord ++ tailWord_2541265) baseStart_2541265 baseEnd_2541265 := by
    simpa [prefixWord, tailWord_2541265, baseEnd_2541265] using wordTrace_append hprefix tailTrace_2541265
  have hstable : (prefixWord ++ tailWord_2541265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541265).length < 2 ^ (prefixWord ++ tailWord_2541265).sum := by decide
  have hdescent : baseEnd_2541265 < baseStart_2541265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541268 : List Nat := [2, 4, 1, 3, 1, 12]
def baseStart_2541268 : Nat := 118140960795 + 2541268 * 2 ^ 59
def prefixEnd_2541268 : Nat := 4983230072969 + 3 ^ 40 * 2541268 * 2
def baseEnd_2541268 : Nat := 5369925744403574119189

theorem tailTrace_2541268 : CollatzResearch.WordTrace tailWord_2541268 prefixEnd_2541268 5369925744403574119189 := by
  unfold tailWord_2541268
  simp only [CollatzResearch.WordTrace]
  refine ⟨46343829278713762432944229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61791772371618349910592305 46343829278713762432944229)
  ·
    refine ⟨8689467989758830456177043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46343829278713762432944229 8689467989758830456177043)
    ·
      refine ⟨13034201984638245684265565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8689467989758830456177043 13034201984638245684265565)
      ·
        refine ⟨4887825744239342131599587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13034201984638245684265565 4887825744239342131599587)
        ·
          refine ⟨7331738616359013197399381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4887825744239342131599587 7331738616359013197399381)
          ·
            refine ⟨5369925744403574119189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 7331738616359013197399381 5369925744403574119189)
            ·
              rfl

theorem cell23_2541268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 12].length) (baseStart_2541268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541268 prefixEnd_2541268 := by exact prefixLift 2541268
  have htrace : WordTrace (prefixWord ++ tailWord_2541268) baseStart_2541268 baseEnd_2541268 := by
    simpa [prefixWord, tailWord_2541268, baseEnd_2541268] using wordTrace_append hprefix tailTrace_2541268
  have hstable : (prefixWord ++ tailWord_2541268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541268).length < 2 ^ (prefixWord ++ tailWord_2541268).sum := by decide
  have hdescent : baseEnd_2541268 < baseStart_2541268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541279 : List Nat := [1, 1, 2, 3, 2, 2, 3, 4, 1, 2, 2]
def baseStart_2541279 : Nat := 118140960795 + 2541279 * 2 ^ 59
def prefixEnd_2541279 : Nat := 4983230072969 + 3 ^ 40 * 2541279 * 2
def baseEnd_2541279 : Nat := 1304897604177267967925377

theorem tailTrace_2541279 : CollatzResearch.WordTrace tailWord_2541279 prefixEnd_2541279 1304897604177267967925377 := by
  unfold tailWord_2541279
  simp only [CollatzResearch.WordTrace]
  refine ⟨92688059760387673744538891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61792039840258449163025927 92688059760387673744538891)
  ·
    refine ⟨139032089640581510616808337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92688059760387673744538891 139032089640581510616808337)
    ·
      refine ⟨104274067230436132962606253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139032089640581510616808337 104274067230436132962606253)
      ·
        refine ⟨39102775211413549860977345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104274067230436132962606253 39102775211413549860977345)
        ·
          refine ⟨29327081408560162395733009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39102775211413549860977345 29327081408560162395733009)
          ·
            refine ⟨21995311056420121796799757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29327081408560162395733009 21995311056420121796799757)
            ·
              refine ⟨8248241646157545673799909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21995311056420121796799757 8248241646157545673799909)
              ·
                refine ⟨1546545308654539813837483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8248241646157545673799909 1546545308654539813837483)
                ·
                  refine ⟨2319817962981809720756225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1546545308654539813837483 2319817962981809720756225)
                  ·
                    refine ⟨1739863472236357290567169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2319817962981809720756225 1739863472236357290567169)
                    ·
                      refine ⟨1304897604177267967925377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1739863472236357290567169 1304897604177267967925377)
                      ·
                        rfl

theorem cell23_2541279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_2541279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541279 prefixEnd_2541279 := by exact prefixLift 2541279
  have htrace : WordTrace (prefixWord ++ tailWord_2541279) baseStart_2541279 baseEnd_2541279 := by
    simpa [prefixWord, tailWord_2541279, baseEnd_2541279] using wordTrace_append hprefix tailTrace_2541279
  have hstable : (prefixWord ++ tailWord_2541279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541279).length < 2 ^ (prefixWord ++ tailWord_2541279).sum := by decide
  have hdescent : baseEnd_2541279 < baseStart_2541279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541295 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 3]
def baseStart_2541295 : Nat := 118140960795 + 2541295 * 2 ^ 59
def prefixEnd_2541295 : Nat := 4983230072969 + 3 ^ 40 * 2541295 * 2
def baseEnd_2541295 : Nat := 1304905819867739905325303

theorem tailTrace_2541295 : CollatzResearch.WordTrace tailWord_2541295 prefixEnd_2541295 1304905819867739905325303 := by
  unfold tailWord_2541295
  simp only [CollatzResearch.WordTrace]
  refine ⟨92688643328329708477121339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61792428885553138984747559 92688643328329708477121339)
  ·
    refine ⟨139032964992494562715682009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92688643328329708477121339 139032964992494562715682009)
    ·
      refine ⟨104274723744370922036761507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139032964992494562715682009 104274723744370922036761507)
      ·
        refine ⟨156412085616556383055142261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104274723744370922036761507 156412085616556383055142261)
        ·
          refine ⟨14663633026552160911419587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 156412085616556383055142261 14663633026552160911419587)
          ·
            refine ⟨21995449539828241367129381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14663633026552160911419587 21995449539828241367129381)
            ·
              refine ⟨4124146788717795256336759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21995449539828241367129381 4124146788717795256336759)
              ·
                refine ⟨6186220183076692884505139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4124146788717795256336759 6186220183076692884505139)
                ·
                  refine ⟨9279330274615039326757709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6186220183076692884505139 9279330274615039326757709)
                  ·
                    refine ⟨3479748852980639747534141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9279330274615039326757709 3479748852980639747534141)
                    ·
                      refine ⟨1304905819867739905325303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3479748852980639747534141 1304905819867739905325303)
                      ·
                        rfl

theorem cell23_2541295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 3].length) (baseStart_2541295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541295 prefixEnd_2541295 := by exact prefixLift 2541295
  have htrace : WordTrace (prefixWord ++ tailWord_2541295) baseStart_2541295 baseEnd_2541295 := by
    simpa [prefixWord, tailWord_2541295, baseEnd_2541295] using wordTrace_append hprefix tailTrace_2541295
  have hstable : (prefixWord ++ tailWord_2541295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541295).length < 2 ^ (prefixWord ++ tailWord_2541295).sum := by decide
  have hdescent : baseEnd_2541295 < baseStart_2541295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541298 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_2541298 : Nat := 118140960795 + 2541298 * 2 ^ 59
def prefixEnd_2541298 : Nat := 4983230072969 + 3 ^ 40 * 2541298 * 2
def baseEnd_2541298 : Nat := 434969120103234464529263

theorem tailTrace_2541298 : CollatzResearch.WordTrace tailWord_2541298 prefixEnd_2541298 434969120103234464529263 := by
  unfold tailWord_2541298
  simp only [CollatzResearch.WordTrace]
  refine ⟨23172188186829709997370137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61792501831545893326320365 23172188186829709997370137)
  ·
    refine ⟨17379141140122282498027603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23172188186829709997370137 17379141140122282498027603)
    ·
      refine ⟨26068711710183423747041405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17379141140122282498027603 26068711710183423747041405)
      ·
        refine ⟨9775766891318783905140527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26068711710183423747041405 9775766891318783905140527)
        ·
          refine ⟨14663650336978175857710791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9775766891318783905140527 14663650336978175857710791)
          ·
            refine ⟨21995475505467263786566187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14663650336978175857710791 21995475505467263786566187)
            ·
              refine ⟨32993213258200895679849281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21995475505467263786566187 32993213258200895679849281)
              ·
                refine ⟨24744909943650671759886961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32993213258200895679849281 24744909943650671759886961)
                ·
                  refine ⟨18558682457738003819915221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24744909943650671759886961 18558682457738003819915221)
                  ·
                    refine ⟨434969120103234464529263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18558682457738003819915221 434969120103234464529263)
                    ·
                      rfl

theorem cell23_2541298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_2541298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541298 prefixEnd_2541298 := by exact prefixLift 2541298
  have htrace : WordTrace (prefixWord ++ tailWord_2541298) baseStart_2541298 baseEnd_2541298 := by
    simpa [prefixWord, tailWord_2541298, baseEnd_2541298] using wordTrace_append hprefix tailTrace_2541298
  have hstable : (prefixWord ++ tailWord_2541298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541298).length < 2 ^ (prefixWord ++ tailWord_2541298).sum := by decide
  have hdescent : baseEnd_2541298 < baseStart_2541298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541308 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_2541308 : Nat := 118140960795 + 2541308 * 2 ^ 59
def prefixEnd_2541308 : Nat := 4983230072969 + 3 ^ 40 * 2541308 * 2
def baseEnd_2541308 : Nat := 1304912495116248354462743

theorem tailTrace_2541308 : CollatzResearch.WordTrace tailWord_2541308 prefixEnd_2541308 1304912495116248354462743 := by
  unfold tailWord_2541308
  simp only [CollatzResearch.WordTrace]
  refine ⟨46344558738641305848672289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61792744984855074464896385 46344558738641305848672289)
  ·
    refine ⟨34758419053980979386504217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46344558738641305848672289 34758419053980979386504217)
    ·
      refine ⟨26068814290485734539878163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34758419053980979386504217 26068814290485734539878163)
      ·
        refine ⟨39103221435728601809817245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26068814290485734539878163 39103221435728601809817245)
        ·
          refine ⟨14663708038398225678681467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39103221435728601809817245 14663708038398225678681467)
          ·
            refine ⟨21995562057597338518022201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14663708038398225678681467 21995562057597338518022201)
            ·
              refine ⟨16496671543198003888516651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21995562057597338518022201 16496671543198003888516651)
              ·
                refine ⟨24745007314797005832774977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16496671543198003888516651 24745007314797005832774977)
                ·
                  refine ⟨18558755486097754374581233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24745007314797005832774977 18558755486097754374581233)
                  ·
                    refine ⟨13919066614573315780935925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18558755486097754374581233 13919066614573315780935925)
                    ·
                      refine ⟨1304912495116248354462743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13919066614573315780935925 1304912495116248354462743)
                      ·
                        rfl

theorem cell23_2541308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_2541308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541308 prefixEnd_2541308 := by exact prefixLift 2541308
  have htrace : WordTrace (prefixWord ++ tailWord_2541308) baseStart_2541308 baseEnd_2541308 := by
    simpa [prefixWord, tailWord_2541308, baseEnd_2541308] using wordTrace_append hprefix tailTrace_2541308
  have hstable : (prefixWord ++ tailWord_2541308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541308).length < 2 ^ (prefixWord ++ tailWord_2541308).sum := by decide
  have hdescent : baseEnd_2541308 < baseStart_2541308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541422 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_2541422 : Nat := 118140960795 + 2541422 * 2 ^ 59
def prefixEnd_2541422 : Nat := 4983230072969 + 3 ^ 40 * 2541422 * 2
def baseEnd_2541422 : Nat := 434990343970286969479073

theorem tailTrace_2541422 : CollatzResearch.WordTrace tailWord_2541422 prefixEnd_2541422 434990343970286969479073 := by
  unfold tailWord_2541422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11586659424858701145874315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61795516932579739444663013 11586659424858701145874315)
  ·
    refine ⟨17379989137288051718811473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11586659424858701145874315 17379989137288051718811473)
    ·
      refine ⟨13034991852966038789108605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17379989137288051718811473 13034991852966038789108605)
      ·
        refine ⟨4888121944862264545915727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13034991852966038789108605 4888121944862264545915727)
        ·
          refine ⟨7332182917293396818873591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4888121944862264545915727 7332182917293396818873591)
          ·
            refine ⟨10998274375940095228310387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7332182917293396818873591 10998274375940095228310387)
            ·
              refine ⟨16497411563910142842465581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10998274375940095228310387 16497411563910142842465581)
              ·
                refine ⟨6186529336466303565924593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16497411563910142842465581 6186529336466303565924593)
                ·
                  refine ⟨4639897002349727674443445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6186529336466303565924593 4639897002349727674443445)
                  ·
                    refine ⟨434990343970286969479073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4639897002349727674443445 434990343970286969479073)
                    ·
                      rfl

theorem cell23_2541422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_2541422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541422 prefixEnd_2541422 := by exact prefixLift 2541422
  have htrace : WordTrace (prefixWord ++ tailWord_2541422) baseStart_2541422 baseEnd_2541422 := by
    simpa [prefixWord, tailWord_2541422, baseEnd_2541422] using wordTrace_append hprefix tailTrace_2541422
  have hstable : (prefixWord ++ tailWord_2541422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541422).length < 2 ^ (prefixWord ++ tailWord_2541422).sum := by decide
  have hdescent : baseEnd_2541422 < baseStart_2541422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541465 : List Nat := [1, 2, 1, 2, 1, 3, 4, 3, 6]
def baseStart_2541465 : Nat := 118140960795 + 2541465 * 2 ^ 59
def prefixEnd_2541465 : Nat := 4983230072969 + 3 ^ 40 * 2541465 * 2
def baseEnd_2541465 : Nat := 144999234619889360022169

theorem tailTrace_2541465 : CollatzResearch.WordTrace tailWord_2541465 prefixEnd_2541465 144999234619889360022169 := by
  unfold tailWord_2541465
  simp only [CollatzResearch.WordTrace]
  refine ⟨92694843737713827510809849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61796562491809218340539899 92694843737713827510809849)
  ·
    refine ⟨69521132803285370633107387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92694843737713827510809849 69521132803285370633107387)
    ·
      refine ⟨104281699204928055949661081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69521132803285370633107387 104281699204928055949661081)
      ·
        refine ⟨78211274403696041962245811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104281699204928055949661081 78211274403696041962245811)
        ·
          refine ⟨117316911605544062943368717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78211274403696041962245811 117316911605544062943368717)
          ·
            refine ⟨43993841852079023603763269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117316911605544062943368717 43993841852079023603763269)
            ·
              refine ⟨8248845347264816925705613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43993841852079023603763269 8248845347264816925705613)
              ·
                refine ⟨3093317005224306347139605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8248845347264816925705613 3093317005224306347139605)
                ·
                  refine ⟨144999234619889360022169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3093317005224306347139605 144999234619889360022169)
                  ·
                    rfl

theorem cell23_2541465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 6].length) (baseStart_2541465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541465 prefixEnd_2541465 := by exact prefixLift 2541465
  have htrace : WordTrace (prefixWord ++ tailWord_2541465) baseStart_2541465 baseEnd_2541465 := by
    simpa [prefixWord, tailWord_2541465, baseEnd_2541465] using wordTrace_append hprefix tailTrace_2541465
  have hstable : (prefixWord ++ tailWord_2541465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541465).length < 2 ^ (prefixWord ++ tailWord_2541465).sum := by decide
  have hdescent : baseEnd_2541465 < baseStart_2541465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541479 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_2541479 : Nat := 118140960795 + 2541479 * 2 ^ 59
def prefixEnd_2541479 : Nat := 4983230072969 + 3 ^ 40 * 2541479 * 2
def baseEnd_2541479 : Nat := 1305000300308167185424457

theorem tailTrace_2541479 : CollatzResearch.WordTrace tailWord_2541479 prefixEnd_2541479 1305000300308167185424457 := by
  unfold tailWord_2541479
  simp only [CollatzResearch.WordTrace]
  refine ⟨92695354359663107901819491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61796902906442071934546327 92695354359663107901819491)
  ·
    refine ⟨139043031539494661852729237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92695354359663107901819491 139043031539494661852729237)
    ·
      refine ⟨6517642103413812274346683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139043031539494661852729237 6517642103413812274346683)
      ·
        refine ⟨9776463155120718411520025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6517642103413812274346683 9776463155120718411520025)
        ·
          refine ⟨7332347366340538808640019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9776463155120718411520025 7332347366340538808640019)
          ·
            refine ⟨10998521049510808212960029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7332347366340538808640019 10998521049510808212960029)
            ·
              refine ⟨4124445393566553079860011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10998521049510808212960029 4124445393566553079860011)
              ·
                refine ⟨6186668090349829619790017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4124445393566553079860011 6186668090349829619790017)
                ·
                  refine ⟨4640001067762372214842513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6186668090349829619790017 4640001067762372214842513)
                  ·
                    refine ⟨3480000800821779161131885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4640001067762372214842513 3480000800821779161131885)
                    ·
                      refine ⟨1305000300308167185424457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3480000800821779161131885 1305000300308167185424457)
                      ·
                        rfl

theorem cell23_2541479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_2541479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541479 prefixEnd_2541479 := by exact prefixLift 2541479
  have htrace : WordTrace (prefixWord ++ tailWord_2541479) baseStart_2541479 baseEnd_2541479 := by
    simpa [prefixWord, tailWord_2541479, baseEnd_2541479] using wordTrace_append hprefix tailTrace_2541479
  have hstable : (prefixWord ++ tailWord_2541479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541479).length < 2 ^ (prefixWord ++ tailWord_2541479).sum := by decide
  have hdescent : baseEnd_2541479 < baseStart_2541479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541529 : List Nat := [1, 2, 1, 2, 6, 1, 2, 2, 1, 5]
def baseStart_2541529 : Nat := 118140960795 + 2541529 * 2 ^ 59
def prefixEnd_2541529 : Nat := 4983230072969 + 3 ^ 40 * 2541529 * 2
def baseEnd_2541529 : Nat := 435008658113630663266409

theorem tailTrace_2541529 : CollatzResearch.WordTrace tailWord_2541529 prefixEnd_2541529 435008658113630663266409 := by
  unfold tailWord_2541529
  simp only [CollatzResearch.WordTrace]
  refine ⟨92697178009481966441139641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61798118672987977627426427 92697178009481966441139641)
  ·
    refine ⟨69522883507111474830854731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92697178009481966441139641 69522883507111474830854731)
    ·
      refine ⟨104284325260667212246282097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69522883507111474830854731 104284325260667212246282097)
      ·
        refine ⟨78213243945500409184711573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104284325260667212246282097 78213243945500409184711573)
        ·
          refine ⟨3666245809945331680533355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78213243945500409184711573 3666245809945331680533355)
          ·
            refine ⟨5499368714917997520800033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666245809945331680533355 5499368714917997520800033)
            ·
              refine ⟨4124526536188498140600025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5499368714917997520800033 4124526536188498140600025)
              ·
                refine ⟨3093394902141373605450019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4124526536188498140600025 3093394902141373605450019)
                ·
                  refine ⟨4640092353212060408175029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3093394902141373605450019 4640092353212060408175029)
                  ·
                    refine ⟨435008658113630663266409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4640092353212060408175029 435008658113630663266409)
                    ·
                      rfl

theorem cell23_2541529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 5].length) (baseStart_2541529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541529 prefixEnd_2541529 := by exact prefixLift 2541529
  have htrace : WordTrace (prefixWord ++ tailWord_2541529) baseStart_2541529 baseEnd_2541529 := by
    simpa [prefixWord, tailWord_2541529, baseEnd_2541529] using wordTrace_append hprefix tailTrace_2541529
  have hstable : (prefixWord ++ tailWord_2541529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541529).length < 2 ^ (prefixWord ++ tailWord_2541529).sum := by decide
  have hdescent : baseEnd_2541529 < baseStart_2541529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541595 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 5]
def baseStart_2541595 : Nat := 118140960795 + 2541595 * 2 ^ 59
def prefixEnd_2541595 : Nat := 4983230072969 + 3 ^ 40 * 2541595 * 2
def baseEnd_2541595 : Nat := 1305059864064088731573923

theorem tailTrace_2541595 : CollatzResearch.WordTrace tailWord_2541595 prefixEnd_2541595 1305059864064088731573923 := by
  unfold tailWord_2541595
  simp only [CollatzResearch.WordTrace]
  refine ⟨92699585227242859713042239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61799723484828573142028159 92699585227242859713042239)
  ·
    refine ⟨139049377840864289569563359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92699585227242859713042239 139049377840864289569563359)
    ·
      refine ⟨208574066761296434354345039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139049377840864289569563359 208574066761296434354345039)
      ·
        refine ⟨312861100141944651531517559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208574066761296434354345039 312861100141944651531517559)
        ·
          refine ⟨469291650212916977297276339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312861100141944651531517559 469291650212916977297276339)
          ·
            refine ⟨703937475319375465945914509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469291650212916977297276339 703937475319375465945914509)
            ·
              refine ⟨263976553244765799729717941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 703937475319375465945914509 263976553244765799729717941)
              ·
                refine ⟨24747801866696793724661057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 263976553244765799729717941 24747801866696793724661057)
                ·
                  refine ⟨18560851400022595293495793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24747801866696793724661057 18560851400022595293495793)
                  ·
                    refine ⟨13920638550016946470121845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18560851400022595293495793 13920638550016946470121845)
                    ·
                      refine ⟨1305059864064088731573923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13920638550016946470121845 1305059864064088731573923)
                      ·
                        rfl

theorem cell23_2541595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 5].length) (baseStart_2541595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541595 prefixEnd_2541595 := by exact prefixLift 2541595
  have htrace : WordTrace (prefixWord ++ tailWord_2541595) baseStart_2541595 baseEnd_2541595 := by
    simpa [prefixWord, tailWord_2541595, baseEnd_2541595] using wordTrace_append hprefix tailTrace_2541595
  have hstable : (prefixWord ++ tailWord_2541595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541595).length < 2 ^ (prefixWord ++ tailWord_2541595).sum := by decide
  have hdescent : baseEnd_2541595 < baseStart_2541595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541616 : List Nat := [2, 1, 1, 1, 2, 6, 2, 2, 2, 1, 3]
def baseStart_2541616 : Nat := 118140960795 + 2541616 * 2 ^ 59
def prefixEnd_2541616 : Nat := 4983230072969 + 3 ^ 40 * 2541616 * 2
def baseEnd_2541616 : Nat := 1305070647157833149411327

theorem tailTrace_2541616 : CollatzResearch.WordTrace tailWord_2541616 prefixEnd_2541616 1305070647157833149411327 := by
  unfold tailWord_2541616
  simp only [CollatzResearch.WordTrace]
  refine ⟨46350175580083390149778351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61800234106777853533037801 46350175580083390149778351)
  ·
    refine ⟨69525263370125085224667527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46350175580083390149778351 69525263370125085224667527)
    ·
      refine ⟨104287895055187627837001291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69525263370125085224667527 104287895055187627837001291)
      ·
        refine ⟨156431842582781441755501937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104287895055187627837001291 156431842582781441755501937)
        ·
          refine ⟨117323881937086081316626453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156431842582781441755501937 117323881937086081316626453)
          ·
            refine ⟨5499556965800910061716865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117323881937086081316626453 5499556965800910061716865)
            ·
              refine ⟨4124667724350682546287649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5499556965800910061716865 4124667724350682546287649)
              ·
                refine ⟨3093500793263011909715737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4124667724350682546287649 3093500793263011909715737)
                ·
                  refine ⟨2320125594947258932286803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3093500793263011909715737 2320125594947258932286803)
                  ·
                    refine ⟨3480188392420888398430205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2320125594947258932286803 3480188392420888398430205)
                    ·
                      refine ⟨1305070647157833149411327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3480188392420888398430205 1305070647157833149411327)
                      ·
                        rfl

theorem cell23_2541616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 2, 1, 3].length) (baseStart_2541616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541616 prefixEnd_2541616 := by exact prefixLift 2541616
  have htrace : WordTrace (prefixWord ++ tailWord_2541616) baseStart_2541616 baseEnd_2541616 := by
    simpa [prefixWord, tailWord_2541616, baseEnd_2541616] using wordTrace_append hprefix tailTrace_2541616
  have hstable : (prefixWord ++ tailWord_2541616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541616).length < 2 ^ (prefixWord ++ tailWord_2541616).sum := by decide
  have hdescent : baseEnd_2541616 < baseStart_2541616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541632 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 2, 6]
def baseStart_2541632 : Nat := 118140960795 + 2541632 * 2 ^ 59
def prefixEnd_2541632 : Nat := 4983230072969 + 3 ^ 40 * 2541632 * 2
def baseEnd_2541632 : Nat := 435026287616101695603751

theorem tailTrace_2541632 : CollatzResearch.WordTrace tailWord_2541632 prefixEnd_2541632 435026287616101695603751 := by
  unfold tailWord_2541632
  simp only [CollatzResearch.WordTrace]
  refine ⟨46350467364054407516069575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61800623152072543354759433 46350467364054407516069575)
  ·
    refine ⟨69525701046081611274104363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46350467364054407516069575 69525701046081611274104363)
    ·
      refine ⟨104288551569122416911156545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69525701046081611274104363 104288551569122416911156545)
      ·
        refine ⟨78216413676841812683367409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104288551569122416911156545 78216413676841812683367409)
        ·
          refine ⟨58662310257631359512525557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78216413676841812683367409 58662310257631359512525557)
          ·
            refine ⟨5499591586652939954299271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58662310257631359512525557 5499591586652939954299271)
            ·
              refine ⟨8249387379979409931448907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5499591586652939954299271 8249387379979409931448907)
              ·
                refine ⟨12374081069969114897173361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8249387379979409931448907 12374081069969114897173361)
                ·
                  refine ⟨9280560802476836172880021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12374081069969114897173361 9280560802476836172880021)
                  ·
                    refine ⟨435026287616101695603751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9280560802476836172880021 435026287616101695603751)
                    ·
                      rfl

theorem cell23_2541632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 2, 6].length) (baseStart_2541632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541632 prefixEnd_2541632 := by exact prefixLift 2541632
  have htrace : WordTrace (prefixWord ++ tailWord_2541632) baseStart_2541632 baseEnd_2541632 := by
    simpa [prefixWord, tailWord_2541632, baseEnd_2541632] using wordTrace_append hprefix tailTrace_2541632
  have hstable : (prefixWord ++ tailWord_2541632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541632).length < 2 ^ (prefixWord ++ tailWord_2541632).sum := by decide
  have hdescent : baseEnd_2541632 < baseStart_2541632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541642 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_2541642 : Nat := 118140960795 + 2541642 * 2 ^ 59
def prefixEnd_2541642 : Nat := 4983230072969 + 3 ^ 40 * 2541642 * 2
def baseEnd_2541642 : Nat := 1305083997654850047686207

theorem tailTrace_2541642 : CollatzResearch.WordTrace tailWord_2541642 prefixEnd_2541642 1305083997654850047686207 := by
  unfold tailWord_2541642
  simp only [CollatzResearch.WordTrace]
  refine ⟨23175324864518146685000795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61800866305381724493335453 23175324864518146685000795)
  ·
    refine ⟨34762987296777220027501193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23175324864518146685000795 34762987296777220027501193)
    ·
      refine ⟨26072240472582915020625895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34762987296777220027501193 26072240472582915020625895)
      ·
        refine ⟨39108360708874372530938843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26072240472582915020625895 39108360708874372530938843)
        ·
          refine ⟨58662541063311558796408265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39108360708874372530938843 58662541063311558796408265)
          ·
            refine ⟨43996905797483669097306199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58662541063311558796408265 43996905797483669097306199)
            ·
              refine ⟨65995358696225503645959299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43996905797483669097306199 65995358696225503645959299)
              ·
                refine ⟨98993038044338255468938949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65995358696225503645959299 98993038044338255468938949)
                ·
                  refine ⟨18561194633313422900426053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98993038044338255468938949 18561194633313422900426053)
                  ·
                    refine ⟨3480223993746266793829885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18561194633313422900426053 3480223993746266793829885)
                    ·
                      refine ⟨1305083997654850047686207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3480223993746266793829885 1305083997654850047686207)
                      ·
                        rfl

theorem cell23_2541642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_2541642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541642 prefixEnd_2541642 := by exact prefixLift 2541642
  have htrace : WordTrace (prefixWord ++ tailWord_2541642) baseStart_2541642 baseEnd_2541642 := by
    simpa [prefixWord, tailWord_2541642, baseEnd_2541642] using wordTrace_append hprefix tailTrace_2541642
  have hstable : (prefixWord ++ tailWord_2541642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541642).length < 2 ^ (prefixWord ++ tailWord_2541642).sum := by decide
  have hdescent : baseEnd_2541642 < baseStart_2541642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541652 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_2541652 : Nat := 118140960795 + 2541652 * 2 ^ 59
def prefixEnd_2541652 : Nat := 4983230072969 + 3 ^ 40 * 2541652 * 2
def baseEnd_2541652 : Nat := 1305089132461395008561161

theorem tailTrace_2541652 : CollatzResearch.WordTrace tailWord_2541652 prefixEnd_2541652 1305089132461395008561161 := by
  unfold tailWord_2541652
  simp only [CollatzResearch.WordTrace]
  refine ⟨46350832094018179223933605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61801109458690905631911473 46350832094018179223933605)
  ·
    refine ⟨8690781017628408604487551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46350832094018179223933605 8690781017628408604487551)
    ·
      refine ⟨13036171526442612906731327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8690781017628408604487551 13036171526442612906731327)
      ·
        refine ⟨19554257289663919360096991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13036171526442612906731327 19554257289663919360096991)
        ·
          refine ⟨29331385934495879040145487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19554257289663919360096991 29331385934495879040145487)
          ·
            refine ⟨43997078901743818560218231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29331385934495879040145487 43997078901743818560218231)
            ·
              refine ⟨65995618352615727840327347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43997078901743818560218231 65995618352615727840327347)
              ·
                refine ⟨98993427528923591760491021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65995618352615727840327347 98993427528923591760491021)
                ·
                  refine ⟨37122535323346346910184133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98993427528923591760491021 37122535323346346910184133)
                  ·
                    refine ⟨6960475373127440045659525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37122535323346346910184133 6960475373127440045659525)
                    ·
                      refine ⟨1305089132461395008561161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6960475373127440045659525 1305089132461395008561161)
                      ·
                        rfl

theorem cell23_2541652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_2541652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541652 prefixEnd_2541652 := by exact prefixLift 2541652
  have htrace : WordTrace (prefixWord ++ tailWord_2541652) baseStart_2541652 baseEnd_2541652 := by
    simpa [prefixWord, tailWord_2541652, baseEnd_2541652] using wordTrace_append hprefix tailTrace_2541652
  have hstable : (prefixWord ++ tailWord_2541652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541652).length < 2 ^ (prefixWord ++ tailWord_2541652).sum := by decide
  have hdescent : baseEnd_2541652 < baseStart_2541652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541660 : List Nat := [2, 2, 4, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_2541660 : Nat := 118140960795 + 2541660 * 2 ^ 59
def prefixEnd_2541660 : Nat := 4983230072969 + 3 ^ 40 * 2541660 * 2
def baseEnd_2541660 : Nat := 1305093240306630977261125

theorem tailTrace_2541660 : CollatzResearch.WordTrace tailWord_2541660 prefixEnd_2541660 1305093240306630977261125 := by
  unfold tailWord_2541660
  simp only [CollatzResearch.WordTrace]
  refine ⟨46350977986003687907079217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61801303981338250542772289 46350977986003687907079217)
  ·
    refine ⟨34763233489502765930309413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46350977986003687907079217 34763233489502765930309413)
    ·
      refine ⟨6518106279281768611933015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34763233489502765930309413 6518106279281768611933015)
      ·
        refine ⟨9777159418922652917899523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6518106279281768611933015 9777159418922652917899523)
        ·
          refine ⟨14665739128383979376849285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9777159418922652917899523 14665739128383979376849285)
          ·
            refine ⟨2749826086571996133159241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14665739128383979376849285 2749826086571996133159241)
            ·
              refine ⟨2062369564928997099869431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2749826086571996133159241 2062369564928997099869431)
              ·
                refine ⟨3093554347393495649804147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062369564928997099869431 3093554347393495649804147)
                ·
                  refine ⟨4640331521090243474706221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3093554347393495649804147 4640331521090243474706221)
                  ·
                    refine ⟨1740124320408841303014833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4640331521090243474706221 1740124320408841303014833)
                    ·
                      refine ⟨1305093240306630977261125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1740124320408841303014833 1305093240306630977261125)
                      ·
                        rfl

theorem cell23_2541660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_2541660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541660 prefixEnd_2541660 := by exact prefixLift 2541660
  have htrace : WordTrace (prefixWord ++ tailWord_2541660) baseStart_2541660 baseEnd_2541660 := by
    simpa [prefixWord, tailWord_2541660, baseEnd_2541660] using wordTrace_append hprefix tailTrace_2541660
  have hstable : (prefixWord ++ tailWord_2541660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541660).length < 2 ^ (prefixWord ++ tailWord_2541660).sum := by decide
  have hdescent : baseEnd_2541660 < baseStart_2541660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541679 : List Nat := [1, 1, 2, 1, 3, 4, 2, 4, 5]
def baseStart_2541679 : Nat := 118140960795 + 2541679 * 2 ^ 59
def prefixEnd_2541679 : Nat := 4983230072969 + 3 ^ 40 * 2541679 * 2
def baseEnd_2541679 : Nat := 145011444048785155880393

theorem tailTrace_2541679 : CollatzResearch.WordTrace tailWord_2541679 prefixEnd_2541679 145011444048785155880393 := by
  unfold tailWord_2541679
  simp only [CollatzResearch.WordTrace]
  refine ⟨92702648958938542059100091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61801765972625694706066727 92702648958938542059100091)
  ·
    refine ⟨139053973438407813088650137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92702648958938542059100091 139053973438407813088650137)
    ·
      refine ⟨104290480078805859816487603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139053973438407813088650137 104290480078805859816487603)
      ·
        refine ⟨156435720118208789724731405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104290480078805859816487603 156435720118208789724731405)
        ·
          refine ⟨58663395044328296146774277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156435720118208789724731405 58663395044328296146774277)
          ·
            refine ⟨10999386570811555527520177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58663395044328296146774277 10999386570811555527520177)
            ·
              refine ⟨8249539928108666645640133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10999386570811555527520177 8249539928108666645640133)
              ·
                refine ⟨1546788736520374996057525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8249539928108666645640133 1546788736520374996057525)
                ·
                  refine ⟨145011444048785155880393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1546788736520374996057525 145011444048785155880393)
                  ·
                    rfl

theorem cell23_2541679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 5].length) (baseStart_2541679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541679 prefixEnd_2541679 := by exact prefixLift 2541679
  have htrace : WordTrace (prefixWord ++ tailWord_2541679) baseStart_2541679 baseEnd_2541679 := by
    simpa [prefixWord, tailWord_2541679, baseEnd_2541679] using wordTrace_append hprefix tailTrace_2541679
  have hstable : (prefixWord ++ tailWord_2541679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541679).length < 2 ^ (prefixWord ++ tailWord_2541679).sum := by decide
  have hdescent : baseEnd_2541679 < baseStart_2541679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541689 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 2, 3, 3]
def baseStart_2541689 : Nat := 118140960795 + 2541689 * 2 ^ 59
def prefixEnd_2541689 : Nat := 4983230072969 + 3 ^ 40 * 2541689 * 2
def baseEnd_2541689 : Nat := 1305108131245611363798491

theorem tailTrace_2541689 : CollatzResearch.WordTrace tailWord_2541689 prefixEnd_2541689 1305108131245611363798491 := by
  unfold tailWord_2541689
  simp only [CollatzResearch.WordTrace]
  refine ⟨92703013688902313766964121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61802009125934875844642747 92703013688902313766964121)
  ·
    refine ⟨69527260266676735325223091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92703013688902313766964121 69527260266676735325223091)
    ·
      refine ⟨104290890400015102987834637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69527260266676735325223091 104290890400015102987834637)
      ·
        refine ⟨39109083900005663620437989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104290890400015102987834637 39109083900005663620437989)
        ·
          refine ⟨7332953231251061928832123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39109083900005663620437989 7332953231251061928832123)
          ·
            refine ⟨10999429846876592893248185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7332953231251061928832123 10999429846876592893248185)
            ·
              refine ⟨8249572385157444669936139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10999429846876592893248185 8249572385157444669936139)
              ·
                refine ⟨12374358577736167004904209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8249572385157444669936139 12374358577736167004904209)
                ·
                  refine ⟨9280768933302125253678157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12374358577736167004904209 9280768933302125253678157)
                  ·
                    refine ⟨3480288349988296970129309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9280768933302125253678157 3480288349988296970129309)
                    ·
                      refine ⟨1305108131245611363798491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3480288349988296970129309 1305108131245611363798491)
                      ·
                        rfl

theorem cell23_2541689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_2541689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541689 prefixEnd_2541689 := by exact prefixLift 2541689
  have htrace : WordTrace (prefixWord ++ tailWord_2541689) baseStart_2541689 baseEnd_2541689 := by
    simpa [prefixWord, tailWord_2541689, baseEnd_2541689] using wordTrace_append hprefix tailTrace_2541689
  have hstable : (prefixWord ++ tailWord_2541689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541689).length < 2 ^ (prefixWord ++ tailWord_2541689).sum := by decide
  have hdescent : baseEnd_2541689 < baseStart_2541689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541692 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 1, 7]
def baseStart_2541692 : Nat := 118140960795 + 2541692 * 2 ^ 59
def prefixEnd_2541692 : Nat := 4983230072969 + 3 ^ 40 * 2541692 * 2
def baseEnd_2541692 : Nat := 435036557229191617353659

theorem tailTrace_2541692 : CollatzResearch.WordTrace tailWord_2541692 prefixEnd_2541692 435036557229191617353659 := by
  unfold tailWord_2541692
  simp only [CollatzResearch.WordTrace]
  refine ⟨46351561553945722639661665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61802082071927630186215553 46351561553945722639661665)
  ·
    refine ⟨34763671165459291979746249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46351561553945722639661665 34763671165459291979746249)
    ·
      refine ⟨26072753374094468984809687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34763671165459291979746249 26072753374094468984809687)
      ·
        refine ⟨39109130061141703477214531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26072753374094468984809687 39109130061141703477214531)
        ·
          refine ⟨58663695091712555215821797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39109130061141703477214531 58663695091712555215821797)
          ·
            refine ⟨10999442829696104102966587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58663695091712555215821797 10999442829696104102966587)
            ·
              refine ⟨16499164244544156154449881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10999442829696104102966587 16499164244544156154449881)
              ·
                refine ⟨12374373183408117115837411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16499164244544156154449881 12374373183408117115837411)
                ·
                  refine ⟨18561559775112175673756117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12374373183408117115837411 18561559775112175673756117)
                  ·
                    refine ⟨435036557229191617353659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18561559775112175673756117 435036557229191617353659)
                    ·
                      rfl

theorem cell23_2541692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_2541692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541692 prefixEnd_2541692 := by exact prefixLift 2541692
  have htrace : WordTrace (prefixWord ++ tailWord_2541692) baseStart_2541692 baseEnd_2541692 := by
    simpa [prefixWord, tailWord_2541692, baseEnd_2541692] using wordTrace_append hprefix tailTrace_2541692
  have hstable : (prefixWord ++ tailWord_2541692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541692).length < 2 ^ (prefixWord ++ tailWord_2541692).sum := by decide
  have hdescent : baseEnd_2541692 < baseStart_2541692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541712 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 4]
def baseStart_2541712 : Nat := 118140960795 + 2541712 * 2 ^ 59
def prefixEnd_2541712 : Nat := 4983230072969 + 3 ^ 40 * 2541712 * 2
def baseEnd_2541712 : Nat := 1305119941300664773810885

theorem tailTrace_2541712 : CollatzResearch.WordTrace tailWord_2541712 prefixEnd_2541712 1305119941300664773810885 := by
  unfold tailWord_2541712
  simp only [CollatzResearch.WordTrace]
  refine ⟨46351926283909494347525695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61802568378545992463367593 46351926283909494347525695)
  ·
    refine ⟨69527889425864241521288543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46351926283909494347525695 69527889425864241521288543)
    ·
      refine ⟨104291834138796362281932815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69527889425864241521288543 104291834138796362281932815)
      ·
        refine ⟨156437751208194543422899223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104291834138796362281932815 156437751208194543422899223)
        ·
          refine ⟨234656626812291815134348835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156437751208194543422899223 234656626812291815134348835)
          ·
            refine ⟨351984940218437722701523253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234656626812291815134348835 351984940218437722701523253)
            ·
              refine ⟨32998588145478536503267805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 351984940218437722701523253 32998588145478536503267805)
              ·
                refine ⟨12374470554554451188725427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32998588145478536503267805 12374470554554451188725427)
                ·
                  refine ⟨18561705831831676783088141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12374470554554451188725427 18561705831831676783088141)
                  ·
                    refine ⟨6960639686936878793658053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18561705831831676783088141 6960639686936878793658053)
                    ·
                      refine ⟨1305119941300664773810885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6960639686936878793658053 1305119941300664773810885)
                      ·
                        rfl

theorem cell23_2541712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_2541712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541712 prefixEnd_2541712 := by exact prefixLift 2541712
  have htrace : WordTrace (prefixWord ++ tailWord_2541712) baseStart_2541712 baseEnd_2541712 := by
    simpa [prefixWord, tailWord_2541712, baseEnd_2541712] using wordTrace_append hprefix tailTrace_2541712
  have hstable : (prefixWord ++ tailWord_2541712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541712).length < 2 ^ (prefixWord ++ tailWord_2541712).sum := by decide
  have hdescent : baseEnd_2541712 < baseStart_2541712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541729 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2541729 : Nat := 118140960795 + 2541729 * 2 ^ 59
def prefixEnd_2541729 : Nat := 4983230072969 + 3 ^ 40 * 2541729 * 2
def baseEnd_2541729 : Nat := 1305128670471791207298307

theorem tailTrace_2541729 : CollatzResearch.WordTrace tailWord_2541729 prefixEnd_2541729 1305128670471791207298307 := by
  unfold tailWord_2541729
  simp only [CollatzResearch.WordTrace]
  refine ⟨92704472608757400598420241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61802981739171600398946827 92704472608757400598420241)
  ·
    refine ⟨69528354456568050448815181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92704472608757400598420241 69528354456568050448815181)
    ·
      refine ⟨26073132921213018918305693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69528354456568050448815181 26073132921213018918305693)
      ·
        refine ⟨9777424845454882094364635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26073132921213018918305693 9777424845454882094364635)
        ·
          refine ⟨14666137268182323141546953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9777424845454882094364635 14666137268182323141546953)
          ·
            refine ⟨10999602951136742356160215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14666137268182323141546953 10999602951136742356160215)
            ·
              refine ⟨16499404426705113534240323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10999602951136742356160215 16499404426705113534240323)
              ·
                refine ⟨24749106640057670301360485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16499404426705113534240323 24749106640057670301360485)
                ·
                  refine ⟨4640457495010813181505091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24749106640057670301360485 4640457495010813181505091)
                  ·
                    refine ⟨6960686242516219772257637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4640457495010813181505091 6960686242516219772257637)
                    ·
                      refine ⟨1305128670471791207298307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6960686242516219772257637 1305128670471791207298307)
                      ·
                        rfl

theorem cell23_2541729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2541729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541729 prefixEnd_2541729 := by exact prefixLift 2541729
  have htrace : WordTrace (prefixWord ++ tailWord_2541729) baseStart_2541729 baseEnd_2541729 := by
    simpa [prefixWord, tailWord_2541729, baseEnd_2541729] using wordTrace_append hprefix tailTrace_2541729
  have hstable : (prefixWord ++ tailWord_2541729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541729).length < 2 ^ (prefixWord ++ tailWord_2541729).sum := by decide
  have hdescent : baseEnd_2541729 < baseStart_2541729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541796 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 3, 1, 3]
def baseStart_2541796 : Nat := 118140960795 + 2541796 * 2 ^ 59
def prefixEnd_2541796 : Nat := 4983230072969 + 3 ^ 40 * 2541796 * 2
def baseEnd_2541796 : Nat := 1305163073675642445160499

theorem tailTrace_2541796 : CollatzResearch.WordTrace tailWord_2541796 prefixEnd_2541796 1305163073675642445160499 := by
  unfold tailWord_2541796
  simp only [CollatzResearch.WordTrace]
  refine ⟨46353458149757335520554621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61804610866343114027406161 46353458149757335520554621)
  ·
    refine ⟨17382546806159000820207983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46353458149757335520554621 17382546806159000820207983)
    ·
      refine ⟨26073820209238501230311975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17382546806159000820207983 26073820209238501230311975)
      ·
        refine ⟨39110730313857751845467963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26073820209238501230311975 39110730313857751845467963)
        ·
          refine ⟨58666095470786627768201945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39110730313857751845467963 58666095470786627768201945)
          ·
            refine ⟨43999571603089970826151459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58666095470786627768201945 43999571603089970826151459)
            ·
              refine ⟨65999357404634956239227189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43999571603089970826151459 65999357404634956239227189)
              ·
                refine ⟨6187439756684527147427549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65999357404634956239227189 6187439756684527147427549)
                ·
                  refine ⟨2320289908756697680285331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6187439756684527147427549 2320289908756697680285331)
                  ·
                    refine ⟨3480434863135046520427997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2320289908756697680285331 3480434863135046520427997)
                    ·
                      refine ⟨1305163073675642445160499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3480434863135046520427997 1305163073675642445160499)
                      ·
                        rfl

theorem cell23_2541796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_2541796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541796 prefixEnd_2541796 := by exact prefixLift 2541796
  have htrace : WordTrace (prefixWord ++ tailWord_2541796) baseStart_2541796 baseEnd_2541796 := by
    simpa [prefixWord, tailWord_2541796, baseEnd_2541796] using wordTrace_append hprefix tailTrace_2541796
  have hstable : (prefixWord ++ tailWord_2541796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541796).length < 2 ^ (prefixWord ++ tailWord_2541796).sum := by decide
  have hdescent : baseEnd_2541796 < baseStart_2541796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541806 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_2541806 : Nat := 118140960795 + 2541806 * 2 ^ 59
def prefixEnd_2541806 : Nat := 4983230072969 + 3 ^ 40 * 2541806 * 2
def baseEnd_2541806 : Nat := 1305168208482187406035453

theorem tailTrace_2541806 : CollatzResearch.WordTrace tailWord_2541806 prefixEnd_2541806 1305168208482187406035453 := by
  unfold tailWord_2541806
  simp only [CollatzResearch.WordTrace]
  refine ⟨11588410128684805343621659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61804854019652295165982181 11588410128684805343621659)
  ·
    refine ⟨17382615193027208015432489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11588410128684805343621659 17382615193027208015432489)
    ·
      refine ⟨13036961394770406011574367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17382615193027208015432489 13036961394770406011574367)
      ·
        refine ⟨19555442092155609017361551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13036961394770406011574367 19555442092155609017361551)
        ·
          refine ⟨29333163138233413526042327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19555442092155609017361551 29333163138233413526042327)
          ·
            refine ⟨43999744707350120289063491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29333163138233413526042327 43999744707350120289063491)
            ·
              refine ⟨65999617061025180433595237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43999744707350120289063491 65999617061025180433595237)
              ·
                refine ⟨12374928198942221331299107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65999617061025180433595237 12374928198942221331299107)
                ·
                  refine ⟨18562392298413331996948661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12374928198942221331299107 18562392298413331996948661)
                  ·
                    refine ⟨1740224277976249874713937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18562392298413331996948661 1740224277976249874713937)
                    ·
                      refine ⟨1305168208482187406035453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1740224277976249874713937 1305168208482187406035453)
                      ·
                        rfl

theorem cell23_2541806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_2541806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541806 prefixEnd_2541806 := by exact prefixLift 2541806
  have htrace : WordTrace (prefixWord ++ tailWord_2541806) baseStart_2541806 baseEnd_2541806 := by
    simpa [prefixWord, tailWord_2541806, baseEnd_2541806] using wordTrace_append hprefix tailTrace_2541806
  have hstable : (prefixWord ++ tailWord_2541806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541806).length < 2 ^ (prefixWord ++ tailWord_2541806).sum := by decide
  have hdescent : baseEnd_2541806 < baseStart_2541806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541833 : List Nat := [1, 2, 1, 1, 3, 6, 2, 1, 1, 5]
def baseStart_2541833 : Nat := 118140960795 + 2541833 * 2 ^ 59
def prefixEnd_2541833 : Nat := 4983230072969 + 3 ^ 40 * 2541833 * 2
def baseEnd_2541833 : Nat := 435060690819952933465943

theorem tailTrace_2541833 : CollatzResearch.WordTrace tailWord_2541833 prefixEnd_2541833 435060690819952933465943 := by
  unfold tailWord_2541833
  simp only [CollatzResearch.WordTrace]
  refine ⟨92708265800380626360206153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61805510533587084240137435 92708265800380626360206153)
  ·
    refine ⟨69531199350285469770154615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92708265800380626360206153 69531199350285469770154615)
    ·
      refine ⟨104296799025428204655231923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69531199350285469770154615 104296799025428204655231923)
      ·
        refine ⟨156445198538142306982847885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104296799025428204655231923 156445198538142306982847885)
        ·
          refine ⟨58666949451803365118567957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156445198538142306982847885 58666949451803365118567957)
          ·
            refine ⟨2750013255553282739932873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58666949451803365118567957 2750013255553282739932873)
            ·
              refine ⟨2062509941664962054949655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2750013255553282739932873 2062509941664962054949655)
              ·
                refine ⟨3093764912497443082424483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062509941664962054949655 3093764912497443082424483)
                ·
                  refine ⟨4640647368746164623636725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3093764912497443082424483 4640647368746164623636725)
                  ·
                    refine ⟨435060690819952933465943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4640647368746164623636725 435060690819952933465943)
                    ·
                      rfl

theorem cell23_2541833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 1, 5].length) (baseStart_2541833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541833 prefixEnd_2541833 := by exact prefixLift 2541833
  have htrace : WordTrace (prefixWord ++ tailWord_2541833) baseStart_2541833 baseEnd_2541833 := by
    simpa [prefixWord, tailWord_2541833, baseEnd_2541833] using wordTrace_append hprefix tailTrace_2541833
  have hstable : (prefixWord ++ tailWord_2541833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541833).length < 2 ^ (prefixWord ++ tailWord_2541833).sum := by decide
  have hdescent : baseEnd_2541833 < baseStart_2541833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541836 : List Nat := [2, 2, 1, 2, 2, 2, 3, 3, 1, 1, 4]
def baseStart_2541836 : Nat := 118140960795 + 2541836 * 2 ^ 59
def prefixEnd_2541836 : Nat := 4983230072969 + 3 ^ 40 * 2541836 * 2
def baseEnd_2541836 : Nat := 1305183612901822288660315

theorem tailTrace_2541836 : CollatzResearch.WordTrace tailWord_2541836 prefixEnd_2541836 1305183612901822288660315 := by
  unfold tailWord_2541836
  simp only [CollatzResearch.WordTrace]
  refine ⟨46354187609684878936282681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61805583479579838581710241 46354187609684878936282681)
  ·
    refine ⟨34765640707263659202212011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46354187609684878936282681 34765640707263659202212011)
    ·
      refine ⟨52148461060895488803318017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34765640707263659202212011 52148461060895488803318017)
      ·
        refine ⟨39111345795671616602488513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52148461060895488803318017 39111345795671616602488513)
        ·
          refine ⟨29333509346753712451866385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39111345795671616602488513 29333509346753712451866385)
          ·
            refine ⟨22000132010065284338899789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29333509346753712451866385 22000132010065284338899789)
            ·
              refine ⟨8250049503774481627087421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22000132010065284338899789 8250049503774481627087421)
              ·
                refine ⟨3093768563915430610157783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8250049503774481627087421 3093768563915430610157783)
                ·
                  refine ⟨4640652845873145915236675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3093768563915430610157783 4640652845873145915236675)
                  ·
                    refine ⟨6960979268809718872855013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4640652845873145915236675 6960979268809718872855013)
                    ·
                      refine ⟨1305183612901822288660315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6960979268809718872855013 1305183612901822288660315)
                      ·
                        rfl

theorem cell23_2541836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_2541836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541836 prefixEnd_2541836 := by exact prefixLift 2541836
  have htrace : WordTrace (prefixWord ++ tailWord_2541836) baseStart_2541836 baseEnd_2541836 := by
    simpa [prefixWord, tailWord_2541836, baseEnd_2541836] using wordTrace_append hprefix tailTrace_2541836
  have hstable : (prefixWord ++ tailWord_2541836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541836).length < 2 ^ (prefixWord ++ tailWord_2541836).sum := by decide
  have hdescent : baseEnd_2541836 < baseStart_2541836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541856 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2541856 : Nat := 118140960795 + 2541856 * 2 ^ 59
def prefixEnd_2541856 : Nat := 4983230072969 + 3 ^ 40 * 2541856 * 2
def baseEnd_2541856 : Nat := 1305193882514912210410223

theorem tailTrace_2541856 : CollatzResearch.WordTrace tailWord_2541856 prefixEnd_2541856 1305193882514912210410223 := by
  unfold tailWord_2541856
  simp only [CollatzResearch.WordTrace]
  refine ⟨46354552339648650644146711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61806069786198200858862281 46354552339648650644146711)
  ·
    refine ⟨69531828509472975966220067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46354552339648650644146711 69531828509472975966220067)
    ·
      refine ⟨104297742764209463949330101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69531828509472975966220067 104297742764209463949330101)
      ·
        refine ⟨9777913384144637245249697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104297742764209463949330101 9777913384144637245249697)
        ·
          refine ⟨7333435038108477933937273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9777913384144637245249697 7333435038108477933937273)
          ·
            refine ⟨5500076278581358450452955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7333435038108477933937273 5500076278581358450452955)
            ·
              refine ⟨8250114417872037675679433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5500076278581358450452955 8250114417872037675679433)
              ·
                refine ⟨6187585813404028256759575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8250114417872037675679433 6187585813404028256759575)
                ·
                  refine ⟨9281378720106042385139363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6187585813404028256759575 9281378720106042385139363)
                  ·
                    refine ⟨13922068080159063577709045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9281378720106042385139363 13922068080159063577709045)
                    ·
                      refine ⟨1305193882514912210410223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13922068080159063577709045 1305193882514912210410223)
                      ·
                        rfl

theorem cell23_2541856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2541856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541856 prefixEnd_2541856 := by exact prefixLift 2541856
  have htrace : WordTrace (prefixWord ++ tailWord_2541856) baseStart_2541856 baseEnd_2541856 := by
    simpa [prefixWord, tailWord_2541856, baseEnd_2541856] using wordTrace_append hprefix tailTrace_2541856
  have hstable : (prefixWord ++ tailWord_2541856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541856).length < 2 ^ (prefixWord ++ tailWord_2541856).sum := by decide
  have hdescent : baseEnd_2541856 < baseStart_2541856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541876 : List Nat := [2, 5, 1, 1, 1, 3, 1, 9]
def baseStart_2541876 : Nat := 118140960795 + 2541876 * 2 ^ 59
def prefixEnd_2541876 : Nat := 4983230072969 + 3 ^ 40 * 2541876 * 2
def baseEnd_2541876 : Nat := 48340894523259338228153

theorem tailTrace_2541876 : CollatzResearch.WordTrace tailWord_2541876 prefixEnd_2541876 48340894523259338228153 := by
  unfold tailWord_2541876
  simp only [CollatzResearch.WordTrace]
  refine ⟨46354917069612422352010741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61806556092816563136014321 46354917069612422352010741)
  ·
    refine ⟨4345773475276164595501007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46354917069612422352010741 4345773475276164595501007)
    ·
      refine ⟨6518660212914246893251511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4345773475276164595501007 6518660212914246893251511)
      ·
        refine ⟨9777990319371370339877267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6518660212914246893251511 9777990319371370339877267)
        ·
          refine ⟨14666985479057055509815901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9777990319371370339877267 14666985479057055509815901)
          ·
            refine ⟨5500119554646395816180963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14666985479057055509815901 5500119554646395816180963)
            ·
              refine ⟨8250179331969593724271445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5500119554646395816180963 8250179331969593724271445)
              ·
                refine ⟨48340894523259338228153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8250179331969593724271445 48340894523259338228153)
                ·
                  rfl

theorem cell23_2541876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 9].length) (baseStart_2541876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541876 prefixEnd_2541876 := by exact prefixLift 2541876
  have htrace : WordTrace (prefixWord ++ tailWord_2541876) baseStart_2541876 baseEnd_2541876 := by
    simpa [prefixWord, tailWord_2541876, baseEnd_2541876] using wordTrace_append hprefix tailTrace_2541876
  have hstable : (prefixWord ++ tailWord_2541876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541876).length < 2 ^ (prefixWord ++ tailWord_2541876).sum := by decide
  have hdescent : baseEnd_2541876 < baseStart_2541876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541919 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 2, 6]
def baseStart_2541919 : Nat := 118140960795 + 2541919 * 2 ^ 59
def prefixEnd_2541919 : Nat := 4983230072969 + 3 ^ 40 * 2541919 * 2
def baseEnd_2541919 : Nat := 435075410598715154640811

theorem tailTrace_2541919 : CollatzResearch.WordTrace tailWord_2541919 prefixEnd_2541919 435075410598715154640811 := by
  unfold tailWord_2541919
  simp only [CollatzResearch.WordTrace]
  refine ⟨92711402478069063047836811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61807601652046042031891207 92711402478069063047836811)
  ·
    refine ⟨139067103717103594571755217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92711402478069063047836811 139067103717103594571755217)
    ·
      refine ⟨104300327787827695928816413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139067103717103594571755217 104300327787827695928816413)
      ·
        refine ⟨39112622920435385973306155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104300327787827695928816413 39112622920435385973306155)
        ·
          refine ⟨58668934380653078959959233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39112622920435385973306155 58668934380653078959959233)
          ·
            refine ⟨44001700785489809219969425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58668934380653078959959233 44001700785489809219969425)
            ·
              refine ⟨33001275589117356914977069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44001700785489809219969425 33001275589117356914977069)
              ·
                refine ⟨12375478345919008843116401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33001275589117356914977069 12375478345919008843116401)
                ·
                  refine ⟨9281608759439256632337301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12375478345919008843116401 9281608759439256632337301)
                  ·
                    refine ⟨435075410598715154640811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9281608759439256632337301 435075410598715154640811)
                    ·
                      rfl

theorem cell23_2541919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 6].length) (baseStart_2541919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541919 prefixEnd_2541919 := by exact prefixLift 2541919
  have htrace : WordTrace (prefixWord ++ tailWord_2541919) baseStart_2541919 baseEnd_2541919 := by
    simpa [prefixWord, tailWord_2541919, baseEnd_2541919] using wordTrace_append hprefix tailTrace_2541919
  have hstable : (prefixWord ++ tailWord_2541919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541919).length < 2 ^ (prefixWord ++ tailWord_2541919).sum := by decide
  have hdescent : baseEnd_2541919 < baseStart_2541919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541920 : List Nat := [2, 1, 1, 3, 5, 1, 1, 3, 2, 1, 3]
def baseStart_2541920 : Nat := 118140960795 + 2541920 * 2 ^ 59
def prefixEnd_2541920 : Nat := 4983230072969 + 3 ^ 40 * 2541920 * 2
def baseEnd_2541920 : Nat := 1305226745276799960009929

theorem tailTrace_2541920 : CollatzResearch.WordTrace tailWord_2541920 prefixEnd_2541920 1305226745276799960009929 := by
  unfold tailWord_2541920
  simp only [CollatzResearch.WordTrace]
  refine ⟨46355719475532720109311607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61807625967376960145748809 46355719475532720109311607)
  ·
    refine ⟨69533579213299080163967411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46355719475532720109311607 69533579213299080163967411)
    ·
      refine ⟨104300368819948620245951117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69533579213299080163967411 104300368819948620245951117)
      ·
        refine ⟨39112638307480732592231669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104300368819948620245951117 39112638307480732592231669)
        ·
          refine ⟨3666809841326318680521719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39112638307480732592231669 3666809841326318680521719)
          ·
            refine ⟨5500214761989478020782579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666809841326318680521719 5500214761989478020782579)
            ·
              refine ⟨8250322142984217031173869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5500214761989478020782579 8250322142984217031173869)
              ·
                refine ⟨3093870803619081386690201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8250322142984217031173869 3093870803619081386690201)
                ·
                  refine ⟨2320403102714311040017651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3093870803619081386690201 2320403102714311040017651)
                  ·
                    refine ⟨3480604654071466560026477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2320403102714311040017651 3480604654071466560026477)
                    ·
                      refine ⟨1305226745276799960009929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3480604654071466560026477 1305226745276799960009929)
                      ·
                        rfl

theorem cell23_2541920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_2541920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541920 prefixEnd_2541920 := by exact prefixLift 2541920
  have htrace : WordTrace (prefixWord ++ tailWord_2541920) baseStart_2541920 baseEnd_2541920 := by
    simpa [prefixWord, tailWord_2541920, baseEnd_2541920] using wordTrace_append hprefix tailTrace_2541920
  have hstable : (prefixWord ++ tailWord_2541920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541920).length < 2 ^ (prefixWord ++ tailWord_2541920).sum := by decide
  have hdescent : baseEnd_2541920 < baseStart_2541920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541929 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 4, 1, 5]
def baseStart_2541929 : Nat := 118140960795 + 2541929 * 2 ^ 59
def prefixEnd_2541929 : Nat := 4983230072969 + 3 ^ 40 * 2541929 * 2
def baseEnd_2541929 : Nat := 1305231366602690424797387

theorem tailTrace_2541929 : CollatzResearch.WordTrace tailWord_2541929 prefixEnd_2541929 1305231366602690424797387 := by
  unfold tailWord_2541929
  simp only [CollatzResearch.WordTrace]
  refine ⟨92711767208032834755700841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61807844805355223170467227 92711767208032834755700841)
  ·
    refine ⟨69533825406024626066775631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92711767208032834755700841 69533825406024626066775631)
    ·
      refine ⟨104300738109036939100163447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69533825406024626066775631 104300738109036939100163447)
      ·
        refine ⟨156451107163555408650245171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104300738109036939100163447 156451107163555408650245171)
        ·
          refine ⟨234676660745333112975367757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156451107163555408650245171 234676660745333112975367757)
          ·
            refine ⟨88003747779499917365762909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234676660745333112975367757 88003747779499917365762909)
            ·
              refine ⟨33001405417312469012161091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88003747779499917365762909 33001405417312469012161091)
              ·
                refine ⟨49502108125968703518241637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33001405417312469012161091 49502108125968703518241637)
                ·
                  refine ⟨9281645273619131909670307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49502108125968703518241637 9281645273619131909670307)
                  ·
                    refine ⟨13922467910428697864505461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9281645273619131909670307 13922467910428697864505461)
                    ·
                      refine ⟨1305231366602690424797387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13922467910428697864505461 1305231366602690424797387)
                      ·
                        rfl

theorem cell23_2541929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_2541929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541929 prefixEnd_2541929 := by exact prefixLift 2541929
  have htrace : WordTrace (prefixWord ++ tailWord_2541929) baseStart_2541929 baseEnd_2541929 := by
    simpa [prefixWord, tailWord_2541929, baseEnd_2541929] using wordTrace_append hprefix tailTrace_2541929
  have hstable : (prefixWord ++ tailWord_2541929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541929).length < 2 ^ (prefixWord ++ tailWord_2541929).sum := by decide
  have hdescent : baseEnd_2541929 < baseStart_2541929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541930 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_2541930 : Nat := 118140960795 + 2541930 * 2 ^ 59
def prefixEnd_2541930 : Nat := 4983230072969 + 3 ^ 40 * 2541930 * 2
def baseEnd_2541930 : Nat := 1305231880083344920884883

theorem tailTrace_2541930 : CollatzResearch.WordTrace tailWord_2541930 prefixEnd_2541930 1305231880083344920884883 := by
  unfold tailWord_2541930
  simp only [CollatzResearch.WordTrace]
  refine ⟨23177950920257302981621811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61807869120686141284324829 23177950920257302981621811)
  ·
    refine ⟨34766926380385954472432717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23177950920257302981621811 34766926380385954472432717)
    ·
      refine ⟨13037597392644732927162269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34766926380385954472432717 13037597392644732927162269)
      ·
        refine ⟨4889099022241774847685851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13037597392644732927162269 4889099022241774847685851)
        ·
          refine ⟨7333648533362662271528777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4889099022241774847685851 7333648533362662271528777)
          ·
            refine ⟨5500236400021996703646583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7333648533362662271528777 5500236400021996703646583)
            ·
              refine ⟨8250354600032995055469875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5500236400021996703646583 8250354600032995055469875)
              ·
                refine ⟨12375531900049492583204813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8250354600032995055469875 12375531900049492583204813)
                ·
                  refine ⟨4640824462518559718701805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12375531900049492583204813 4640824462518559718701805)
                  ·
                    refine ⟨1740309173444459894513177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4640824462518559718701805 1740309173444459894513177)
                    ·
                      refine ⟨1305231880083344920884883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1740309173444459894513177 1305231880083344920884883)
                      ·
                        rfl

theorem cell23_2541930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_2541930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541930 prefixEnd_2541930 := by exact prefixLift 2541930
  have htrace : WordTrace (prefixWord ++ tailWord_2541930) baseStart_2541930 baseEnd_2541930 := by
    simpa [prefixWord, tailWord_2541930, baseEnd_2541930] using wordTrace_append hprefix tailTrace_2541930
  have hstable : (prefixWord ++ tailWord_2541930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541930).length < 2 ^ (prefixWord ++ tailWord_2541930).sum := by decide
  have hdescent : baseEnd_2541930 < baseStart_2541930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541939 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 4]
def baseStart_2541939 : Nat := 118140960795 + 2541939 * 2 ^ 59
def prefixEnd_2541939 : Nat := 4983230072969 + 3 ^ 40 * 2541939 * 2
def baseEnd_2541939 : Nat := 1305236501409235385672341

theorem tailTrace_2541939 : CollatzResearch.WordTrace tailWord_2541939 prefixEnd_2541939 1305236501409235385672341 := by
  unfold tailWord_2541939
  simp only [CollatzResearch.WordTrace]
  refine ⟨92712131937996606463564871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61808087958664404309043247 92712131937996606463564871)
  ·
    refine ⟨139068197906994909695347307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92712131937996606463564871 139068197906994909695347307)
    ·
      refine ⟨208602296860492364543020961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139068197906994909695347307 208602296860492364543020961)
      ·
        refine ⟨156451722645369273407265721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208602296860492364543020961 156451722645369273407265721)
        ·
          refine ⟨117338791984026955055449291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156451722645369273407265721 117338791984026955055449291)
          ·
            refine ⟨176008187976040432583173937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117338791984026955055449291 176008187976040432583173937)
            ·
              refine ⟨132006140982030324437380453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176008187976040432583173937 132006140982030324437380453)
              ·
                refine ⟨24751151434130685832008835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132006140982030324437380453 24751151434130685832008835)
                ·
                  refine ⟨37126727151196028748013253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24751151434130685832008835 37126727151196028748013253)
                  ·
                    refine ⟨6961261340849255390252485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37126727151196028748013253 6961261340849255390252485)
                    ·
                      refine ⟨1305236501409235385672341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6961261340849255390252485 1305236501409235385672341)
                      ·
                        rfl

theorem cell23_2541939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_2541939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541939 prefixEnd_2541939 := by exact prefixLift 2541939
  have htrace : WordTrace (prefixWord ++ tailWord_2541939) baseStart_2541939 baseEnd_2541939 := by
    simpa [prefixWord, tailWord_2541939, baseEnd_2541939] using wordTrace_append hprefix tailTrace_2541939
  have hstable : (prefixWord ++ tailWord_2541939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541939).length < 2 ^ (prefixWord ++ tailWord_2541939).sum := by decide
  have hdescent : baseEnd_2541939 < baseStart_2541939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541943 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 4, 2, 2]
def baseStart_2541943 : Nat := 118140960795 + 2541943 * 2 ^ 59
def prefixEnd_2541943 : Nat := 4983230072969 + 3 ^ 40 * 2541943 * 2
def baseEnd_2541943 : Nat := 1305238555331853370022323

theorem tailTrace_2541943 : CollatzResearch.WordTrace tailWord_2541943 prefixEnd_2541943 1305238555331853370022323 := by
  unfold tailWord_2541943
  simp only [CollatzResearch.WordTrace]
  refine ⟨92712277829982115146710483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61808185219988076764473655 92712277829982115146710483)
  ·
    refine ⟨139068416744973172720065725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92712277829982115146710483 139068416744973172720065725)
    ·
      refine ⟨52150656279364939770024647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139068416744973172720065725 52150656279364939770024647)
      ·
        refine ⟨78225984419047409655036971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52150656279364939770024647 78225984419047409655036971)
        ·
          refine ⟨117338976628571114482555457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78225984419047409655036971 117338976628571114482555457)
          ·
            refine ⟨88004232471428335861916593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117338976628571114482555457 88004232471428335861916593)
            ·
              refine ⟨66003174353571251896437445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88004232471428335861916593 66003174353571251896437445)
              ·
                refine ⟨12375595191294609730582021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66003174353571251896437445 12375595191294609730582021)
                ·
                  refine ⟨2320424098367739324484129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12375595191294609730582021 2320424098367739324484129)
                  ·
                    refine ⟨1740318073775804493363097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2320424098367739324484129 1740318073775804493363097)
                    ·
                      refine ⟨1305238555331853370022323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1740318073775804493363097 1305238555331853370022323)
                      ·
                        rfl

theorem cell23_2541943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 2, 2].length) (baseStart_2541943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541943 prefixEnd_2541943 := by exact prefixLift 2541943
  have htrace : WordTrace (prefixWord ++ tailWord_2541943) baseStart_2541943 baseEnd_2541943 := by
    simpa [prefixWord, tailWord_2541943, baseEnd_2541943] using wordTrace_append hprefix tailTrace_2541943
  have hstable : (prefixWord ++ tailWord_2541943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541943).length < 2 ^ (prefixWord ++ tailWord_2541943).sum := by decide
  have hdescent : baseEnd_2541943 < baseStart_2541943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541954 : List Nat := [3, 4, 2, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_2541954 : Nat := 118140960795 + 2541954 * 2 ^ 59
def prefixEnd_2541954 : Nat := 4983230072969 + 3 ^ 40 * 2541954 * 2
def baseEnd_2541954 : Nat := 1305244203619052826984773

theorem tailTrace_2541954 : CollatzResearch.WordTrace tailWord_2541954 prefixEnd_2541954 1305244203619052826984773 := by
  unfold tailWord_2541954
  simp only [CollatzResearch.WordTrace]
  refine ⟨23178169758235566006340229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61808452688628176016907277 23178169758235566006340229)
  ·
    refine ⟨4345906829669168626188793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23178169758235566006340229 4345906829669168626188793)
    ·
      refine ⟨3259430122251876469641595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4345906829669168626188793 3259430122251876469641595)
      ·
        refine ⟨4889145183377814704462393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3259430122251876469641595 4889145183377814704462393)
        ·
          refine ⟨3666858887533361028346795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4889145183377814704462393 3666858887533361028346795)
          ·
            refine ⟨5500288331300041542520193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666858887533361028346795 5500288331300041542520193)
            ·
              refine ⟨4125216248475031156890145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5500288331300041542520193 4125216248475031156890145)
              ·
                refine ⟨3093912186356273367667609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4125216248475031156890145 3093912186356273367667609)
                ·
                  refine ⟨2320434139767205025750707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3093912186356273367667609 2320434139767205025750707)
                  ·
                    refine ⟨3480651209650807538626061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2320434139767205025750707 3480651209650807538626061)
                    ·
                      refine ⟨1305244203619052826984773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3480651209650807538626061 1305244203619052826984773)
                      ·
                        rfl

theorem cell23_2541954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_2541954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541954 prefixEnd_2541954 := by exact prefixLift 2541954
  have htrace : WordTrace (prefixWord ++ tailWord_2541954) baseStart_2541954 baseEnd_2541954 := by
    simpa [prefixWord, tailWord_2541954, baseEnd_2541954] using wordTrace_append hprefix tailTrace_2541954
  have hstable : (prefixWord ++ tailWord_2541954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541954).length < 2 ^ (prefixWord ++ tailWord_2541954).sum := by decide
  have hdescent : baseEnd_2541954 < baseStart_2541954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2541956 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_2541956 : Nat := 118140960795 + 2541956 * 2 ^ 59
def prefixEnd_2541956 : Nat := 4983230072969 + 3 ^ 40 * 2541956 * 2
def baseEnd_2541956 : Nat := 1305245230580361819159763

theorem tailTrace_2541956 : CollatzResearch.WordTrace tailWord_2541956 prefixEnd_2541956 1305245230580361819159763 := by
  unfold tailWord_2541956
  simp only [CollatzResearch.WordTrace]
  refine ⟨46356375989467509183466861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61808501319290012244622481 46356375989467509183466861)
  ·
    refine ⟨17383640996050315943800073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46356375989467509183466861 17383640996050315943800073)
    ·
      refine ⟨13037730747037736957850055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17383640996050315943800073 13037730747037736957850055)
      ·
        refine ⟨19556596120556605436775083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13037730747037736957850055 19556596120556605436775083)
        ·
          refine ⟨29334894180834908155162625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19556596120556605436775083 29334894180834908155162625)
          ·
            refine ⟨22001170635626181116371969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29334894180834908155162625 22001170635626181116371969)
            ·
              refine ⟨16500877976719635837278977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22001170635626181116371969 16500877976719635837278977)
              ·
                refine ⟨12375658482539726877959233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16500877976719635837278977 12375658482539726877959233)
                ·
                  refine ⟨9281743861904795158469425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12375658482539726877959233 9281743861904795158469425)
                  ·
                    refine ⟨6961307896428596368852069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9281743861904795158469425 6961307896428596368852069)
                    ·
                      refine ⟨1305245230580361819159763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6961307896428596368852069 1305245230580361819159763)
                      ·
                        rfl

theorem cell23_2541956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_2541956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2541956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2541956 prefixEnd_2541956 := by exact prefixLift 2541956
  have htrace : WordTrace (prefixWord ++ tailWord_2541956) baseStart_2541956 baseEnd_2541956 := by
    simpa [prefixWord, tailWord_2541956, baseEnd_2541956] using wordTrace_append hprefix tailTrace_2541956
  have hstable : (prefixWord ++ tailWord_2541956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2541956).length < 2 ^ (prefixWord ++ tailWord_2541956).sum := by decide
  have hdescent : baseEnd_2541956 < baseStart_2541956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2541956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542016 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 4]
def baseStart_2542016 : Nat := 118140960795 + 2542016 * 2 ^ 59
def prefixEnd_2542016 : Nat := 4983230072969 + 3 ^ 40 * 2542016 * 2
def baseEnd_2542016 : Nat := 1305276039419631584409487

theorem tailTrace_2542016 : CollatzResearch.WordTrace tailWord_2542016 prefixEnd_2542016 1305276039419631584409487 := by
  unfold tailWord_2542016
  simp only [CollatzResearch.WordTrace]
  refine ⟨46357470179358824307058951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61809960239145099076078601 46357470179358824307058951)
  ·
    refine ⟨69536205269038236460588427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46357470179358824307058951 69536205269038236460588427)
    ·
      refine ⟨104304307903557354690882641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69536205269038236460588427 104304307903557354690882641)
      ·
        refine ⟨78228230927668016018161981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104304307903557354690882641 78228230927668016018161981)
        ·
          refine ⟨29335586597875506006810743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78228230927668016018161981 29335586597875506006810743)
          ·
            refine ⟨44003379896813259010216115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29335586597875506006810743 44003379896813259010216115)
            ·
              refine ⟨66005069845219888515324173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44003379896813259010216115 66005069845219888515324173)
              ·
                refine ⟨24751901191957458193246565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66005069845219888515324173 24751901191957458193246565)
                ·
                  refine ⟨4640981473492023411233731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24751901191957458193246565 4640981473492023411233731)
                  ·
                    refine ⟨6961472210238035116850597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4640981473492023411233731 6961472210238035116850597)
                    ·
                      refine ⟨1305276039419631584409487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6961472210238035116850597 1305276039419631584409487)
                      ·
                        rfl

theorem cell23_2542016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_2542016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542016 prefixEnd_2542016 := by exact prefixLift 2542016
  have htrace : WordTrace (prefixWord ++ tailWord_2542016) baseStart_2542016 baseEnd_2542016 := by
    simpa [prefixWord, tailWord_2542016, baseEnd_2542016] using wordTrace_append hprefix tailTrace_2542016
  have hstable : (prefixWord ++ tailWord_2542016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542016).length < 2 ^ (prefixWord ++ tailWord_2542016).sum := by decide
  have hdescent : baseEnd_2542016 < baseStart_2542016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542017 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 7]
def baseStart_2542017 : Nat := 118140960795 + 2542017 * 2 ^ 59
def prefixEnd_2542017 : Nat := 4983230072969 + 3 ^ 40 * 2542017 * 2
def baseEnd_2542017 : Nat := 145030728100031786721887

theorem tailTrace_2542017 : CollatzResearch.WordTrace tailWord_2542017 prefixEnd_2542017 145030728100031786721887 := by
  unfold tailWord_2542017
  simp only [CollatzResearch.WordTrace]
  refine ⟨92714976831714025784904305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61809984554476017189936203 92714976831714025784904305)
  ·
    refine ⟨69536232623785519338678229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92714976831714025784904305 69536232623785519338678229)
    ·
      refine ⟨1629755452119973109500271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 69536232623785519338678229 1629755452119973109500271)
      ·
        refine ⟨2444633178179959664250407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1629755452119973109500271 2444633178179959664250407)
        ·
          refine ⟨3666949767269939496375611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2444633178179959664250407 3666949767269939496375611)
          ·
            refine ⟨5500424650904909244563417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666949767269939496375611 5500424650904909244563417)
            ·
              refine ⟨4125318488178681933422563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5500424650904909244563417 4125318488178681933422563)
              ·
                refine ⟨6187977732268022900133845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4125318488178681933422563 6187977732268022900133845)
                ·
                  refine ⟨145030728100031786721887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6187977732268022900133845 145030728100031786721887)
                  ·
                    rfl

theorem cell23_2542017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 7].length) (baseStart_2542017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542017 prefixEnd_2542017 := by exact prefixLift 2542017
  have htrace : WordTrace (prefixWord ++ tailWord_2542017) baseStart_2542017 baseEnd_2542017 := by
    simpa [prefixWord, tailWord_2542017, baseEnd_2542017] using wordTrace_append hprefix tailTrace_2542017
  have hstable : (prefixWord ++ tailWord_2542017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542017).length < 2 ^ (prefixWord ++ tailWord_2542017).sum := by decide
  have hdescent : baseEnd_2542017 < baseStart_2542017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542056 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 8]
def baseStart_2542056 : Nat := 118140960795 + 2542056 * 2 ^ 59
def prefixEnd_2542056 : Nat := 4983230072969 + 3 ^ 40 * 2542056 * 2
def baseEnd_2542056 : Nat := 145032953182867936434367

theorem tailTrace_2542056 : CollatzResearch.WordTrace tailWord_2542056 prefixEnd_2542056 145032953182867936434367 := by
  unfold tailWord_2542056
  simp only [CollatzResearch.WordTrace]
  refine ⟨46358199639286367722787011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61810932852381823630382681 46358199639286367722787011)
  ·
    refine ⟨69537299458929551584180517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46358199639286367722787011 69537299458929551584180517)
    ·
      refine ⟨13038243648549290922033847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69537299458929551584180517 13038243648549290922033847)
      ·
        refine ⟨19557365472823936383050771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13038243648549290922033847 19557365472823936383050771)
        ·
          refine ⟨29336048209235904574576157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19557365472823936383050771 29336048209235904574576157)
          ·
            refine ⟨11001018078463464215466059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29336048209235904574576157 11001018078463464215466059)
            ·
              refine ⟨16501527117695196323199089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11001018078463464215466059 16501527117695196323199089)
              ·
                refine ⟨12376145338271397242399317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16501527117695196323199089 12376145338271397242399317)
                ·
                  refine ⟨145032953182867936434367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12376145338271397242399317 145032953182867936434367)
                  ·
                    rfl

theorem cell23_2542056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 8].length) (baseStart_2542056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542056 prefixEnd_2542056 := by exact prefixLift 2542056
  have htrace : WordTrace (prefixWord ++ tailWord_2542056) baseStart_2542056 baseEnd_2542056 := by
    simpa [prefixWord, tailWord_2542056, baseEnd_2542056] using wordTrace_append hprefix tailTrace_2542056
  have hstable : (prefixWord ++ tailWord_2542056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542056).length < 2 ^ (prefixWord ++ tailWord_2542056).sum := by decide
  have hdescent : baseEnd_2542056 < baseStart_2542056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542070 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_2542070 : Nat := 118140960795 + 2542070 * 2 ^ 59
def prefixEnd_2542070 : Nat := 4983230072969 + 3 ^ 40 * 2542070 * 2
def baseEnd_2542070 : Nat := 1305303767374974373134239

theorem tailTrace_2542070 : CollatzResearch.WordTrace tailWord_2542070 prefixEnd_2542070 1305303767374974373134239 := by
  unfold tailWord_2542070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5794806868782625989786479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61811273267014677224389109 5794806868782625989786479)
  ·
    refine ⟨8692210303173938984679719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5794806868782625989786479 8692210303173938984679719)
    ·
      refine ⟨13038315454760908477019579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8692210303173938984679719 13038315454760908477019579)
      ·
        refine ⟨19557473182141362715529369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13038315454760908477019579 19557473182141362715529369)
        ·
          refine ⟨14668104886606022036647027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19557473182141362715529369 14668104886606022036647027)
          ·
            refine ⟨22002157329909033054970541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14668104886606022036647027 22002157329909033054970541)
            ·
              refine ⟨8250808998715887395613953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22002157329909033054970541 8250808998715887395613953)
              ·
                refine ⟨6188106749036915546710465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8250808998715887395613953 6188106749036915546710465)
                ·
                  refine ⟨4641080061777686660032849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6188106749036915546710465 4641080061777686660032849)
                  ·
                    refine ⟨3480810046333264995024637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4641080061777686660032849 3480810046333264995024637)
                    ·
                      refine ⟨1305303767374974373134239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3480810046333264995024637 1305303767374974373134239)
                      ·
                        rfl

theorem cell23_2542070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_2542070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542070 prefixEnd_2542070 := by exact prefixLift 2542070
  have htrace : WordTrace (prefixWord ++ tailWord_2542070) baseStart_2542070 baseEnd_2542070 := by
    simpa [prefixWord, tailWord_2542070, baseEnd_2542070] using wordTrace_append hprefix tailTrace_2542070
  have hstable : (prefixWord ++ tailWord_2542070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542070).length < 2 ^ (prefixWord ++ tailWord_2542070).sum := by decide
  have hdescent : baseEnd_2542070 < baseStart_2542070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542077 : List Nat := [1, 4, 1, 1, 1, 3, 5, 2, 1, 4]
def baseStart_2542077 : Nat := 118140960795 + 2542077 * 2 ^ 59
def prefixEnd_2542077 : Nat := 4983230072969 + 3 ^ 40 * 2542077 * 2
def baseEnd_2542077 : Nat := 435102453913185281915569

theorem tailTrace_2542077 : CollatzResearch.WordTrace tailWord_2542077 prefixEnd_2542077 435102453913185281915569 := by
  unfold tailWord_2542077
  simp only [CollatzResearch.WordTrace]
  refine ⟨92717165211496656032088485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61811443474331104021392323 92717165211496656032088485)
  ·
    refine ⟨17384468477155623006016591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92717165211496656032088485 17384468477155623006016591)
    ·
      refine ⟨26076702715733434509024887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17384468477155623006016591 26076702715733434509024887)
      ·
        refine ⟨39115054073600151763537331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26076702715733434509024887 39115054073600151763537331)
        ·
          refine ⟨58672581110400227645305997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39115054073600151763537331 58672581110400227645305997)
          ·
            refine ⟨22002217916400085366989749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58672581110400227645305997 22002217916400085366989749)
            ·
              refine ⟨2062707929662508003155289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22002217916400085366989749 2062707929662508003155289)
              ·
                refine ⟨1547030947246881002366467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2062707929662508003155289 1547030947246881002366467)
                ·
                  refine ⟨2320546420870321503549701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547030947246881002366467 2320546420870321503549701)
                  ·
                    refine ⟨435102453913185281915569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2320546420870321503549701 435102453913185281915569)
                    ·
                      rfl

theorem cell23_2542077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_2542077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542077 prefixEnd_2542077 := by exact prefixLift 2542077
  have htrace : WordTrace (prefixWord ++ tailWord_2542077) baseStart_2542077 baseEnd_2542077 := by
    simpa [prefixWord, tailWord_2542077, baseEnd_2542077] using wordTrace_append hprefix tailTrace_2542077
  have hstable : (prefixWord ++ tailWord_2542077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542077).length < 2 ^ (prefixWord ++ tailWord_2542077).sum := by decide
  have hdescent : baseEnd_2542077 < baseStart_2542077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542123 : List Nat := [1, 1, 1, 1, 2, 1, 3, 7, 1, 1, 4]
def baseStart_2542123 : Nat := 118140960795 + 2542123 * 2 ^ 59
def prefixEnd_2542123 : Nat := 4983230072969 + 3 ^ 40 * 2542123 * 2
def baseEnd_2542123 : Nat := 1305330981849662665771495

theorem tailTrace_2542123 : CollatzResearch.WordTrace tailWord_2542123 prefixEnd_2542123 1305330981849662665771495 := by
  unfold tailWord_2542123
  simp only [CollatzResearch.WordTrace]
  refine ⟨92718842969330005888263023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61812561979553337258842015 92718842969330005888263023)
  ·
    refine ⟨139078264453995008832394535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92718842969330005888263023 139078264453995008832394535)
    ·
      refine ⟨208617396680992513248591803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139078264453995008832394535 208617396680992513248591803)
      ·
        refine ⟨312926095021488769872887705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208617396680992513248591803 312926095021488769872887705)
        ·
          refine ⟨234694571266116577404665779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312926095021488769872887705 234694571266116577404665779)
          ·
            refine ⟨352041856899174866106998669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234694571266116577404665779 352041856899174866106998669)
            ·
              refine ⟨132015696337190574790124501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 352041856899174866106998669 132015696337190574790124501)
              ·
                refine ⟨3094117882902904096643543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 132015696337190574790124501 3094117882902904096643543)
                ·
                  refine ⟨4641176824354356144965315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094117882902904096643543 4641176824354356144965315)
                  ·
                    refine ⟨6961765236531534217447973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4641176824354356144965315 6961765236531534217447973)
                    ·
                      refine ⟨1305330981849662665771495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6961765236531534217447973 1305330981849662665771495)
                      ·
                        rfl

theorem cell23_2542123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 1, 4].length) (baseStart_2542123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542123 prefixEnd_2542123 := by exact prefixLift 2542123
  have htrace : WordTrace (prefixWord ++ tailWord_2542123) baseStart_2542123 baseEnd_2542123 := by
    simpa [prefixWord, tailWord_2542123, baseEnd_2542123] using wordTrace_append hprefix tailTrace_2542123
  have hstable : (prefixWord ++ tailWord_2542123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542123).length < 2 ^ (prefixWord ++ tailWord_2542123).sum := by decide
  have hdescent : baseEnd_2542123 < baseStart_2542123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542143 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 3]
def baseStart_2542143 : Nat := 118140960795 + 2542143 * 2 ^ 59
def prefixEnd_2542143 : Nat := 4983230072969 + 3 ^ 40 * 2542143 * 2
def baseEnd_2542143 : Nat := 1305341251462752587521403

theorem tailTrace_2542143 : CollatzResearch.WordTrace tailWord_2542143 prefixEnd_2542143 1305341251462752587521403 := by
  unfold tailWord_2542143
  simp only [CollatzResearch.WordTrace]
  refine ⟨92719572429257549303991083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61813048286171699535994055 92719572429257549303991083)
  ·
    refine ⟨139079358643886323955986625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92719572429257549303991083 139079358643886323955986625)
    ·
      refine ⟨104309518982914742966989969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139079358643886323955986625 104309518982914742966989969)
      ·
        refine ⟨78232139237186057225242477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104309518982914742966989969 78232139237186057225242477)
        ·
          refine ⟨29337052213944771459465929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78232139237186057225242477 29337052213944771459465929)
          ·
            refine ⟨22002789160458578594599447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29337052213944771459465929 22002789160458578594599447)
            ·
              refine ⟨33004183740687867891899171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22002789160458578594599447 33004183740687867891899171)
              ·
                refine ⟨49506275611031801837848757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33004183740687867891899171 49506275611031801837848757)
                ·
                  refine ⟨4641213338534231422298321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49506275611031801837848757 4641213338534231422298321)
                  ·
                    refine ⟨3480910003900673566723741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4641213338534231422298321 3480910003900673566723741)
                    ·
                      refine ⟨1305341251462752587521403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3480910003900673566723741 1305341251462752587521403)
                      ·
                        rfl

theorem cell23_2542143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_2542143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542143 prefixEnd_2542143 := by exact prefixLift 2542143
  have htrace : WordTrace (prefixWord ++ tailWord_2542143) baseStart_2542143 baseEnd_2542143 := by
    simpa [prefixWord, tailWord_2542143, baseEnd_2542143] using wordTrace_append hprefix tailTrace_2542143
  have hstable : (prefixWord ++ tailWord_2542143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542143).length < 2 ^ (prefixWord ++ tailWord_2542143).sum := by decide
  have hdescent : baseEnd_2542143 < baseStart_2542143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542177 : List Nat := [1, 2, 3, 1, 1, 4, 4, 1, 1, 2, 3]
def baseStart_2542177 : Nat := 118140960795 + 2542177 * 2 ^ 59
def prefixEnd_2542177 : Nat := 4983230072969 + 3 ^ 40 * 2542177 * 2
def baseEnd_2542177 : Nat := 1305358709805005454496247

theorem tailTrace_2542177 : CollatzResearch.WordTrace tailWord_2542177 prefixEnd_2542177 1305358709805005454496247 := by
  unfold tailWord_2542177
  simp only [CollatzResearch.WordTrace]
  refine ⟨92720812511134373110728785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61813875007422915407152523 92720812511134373110728785)
  ·
    refine ⟨69540609383350779833046589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92720812511134373110728785 69540609383350779833046589)
    ·
      refine ⟨26077728518756542437392471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69540609383350779833046589 26077728518756542437392471)
      ·
        refine ⟨39116592778134813656088707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26077728518756542437392471 39116592778134813656088707)
        ·
          refine ⟨58674889167202220484133061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39116592778134813656088707 58674889167202220484133061)
          ·
            refine ⟨11001541718850416340774949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58674889167202220484133061 11001541718850416340774949)
            ·
              refine ⟨2062789072284453063895303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11001541718850416340774949 2062789072284453063895303)
              ·
                refine ⟨3094183608426679595842955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062789072284453063895303 3094183608426679595842955)
                ·
                  refine ⟨4641275412640019393764433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094183608426679595842955 4641275412640019393764433)
                  ·
                    refine ⟨3480956559480014545323325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4641275412640019393764433 3480956559480014545323325)
                    ·
                      refine ⟨1305358709805005454496247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3480956559480014545323325 1305358709805005454496247)
                      ·
                        rfl

theorem cell23_2542177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_2542177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542177 prefixEnd_2542177 := by exact prefixLift 2542177
  have htrace : WordTrace (prefixWord ++ tailWord_2542177) baseStart_2542177 baseEnd_2542177 := by
    simpa [prefixWord, tailWord_2542177, baseEnd_2542177] using wordTrace_append hprefix tailTrace_2542177
  have hstable : (prefixWord ++ tailWord_2542177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542177).length < 2 ^ (prefixWord ++ tailWord_2542177).sum := by decide
  have hdescent : baseEnd_2542177 < baseStart_2542177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542184 : List Nat := [2, 1, 4, 3, 2, 2, 1, 2, 2, 4]
def baseStart_2542184 : Nat := 118140960795 + 2542184 * 2 ^ 59
def prefixEnd_2542184 : Nat := 4983230072969 + 3 ^ 40 * 2542184 * 2
def baseEnd_2542184 : Nat := 435120768056528975702905

theorem tailTrace_2542184 : CollatzResearch.WordTrace tailWord_2542184 prefixEnd_2542184 435120768056528975702905 := by
  unfold tailWord_2542184
  simp only [CollatzResearch.WordTrace]
  refine ⟨46360533911054506653116803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61814045214739342204155737 46360533911054506653116803)
  ·
    refine ⟨69540800866581759979675205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46360533911054506653116803 69540800866581759979675205)
    ·
      refine ⟨13038900162484079996189101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69540800866581759979675205 13038900162484079996189101)
      ·
        refine ⟨4889587560931529998570913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13038900162484079996189101 4889587560931529998570913)
        ·
          refine ⟨3667190670698647498928185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4889587560931529998570913 3667190670698647498928185)
          ·
            refine ⟨2750393003023985624196139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3667190670698647498928185 2750393003023985624196139)
            ·
              refine ⟨4125589504535978436294209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2750393003023985624196139 4125589504535978436294209)
              ·
                refine ⟨3094192128401983827220657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4125589504535978436294209 3094192128401983827220657)
                ·
                  refine ⟨2320644096301487870415493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3094192128401983827220657 2320644096301487870415493)
                  ·
                    refine ⟨435120768056528975702905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2320644096301487870415493 435120768056528975702905)
                    ·
                      rfl

theorem cell23_2542184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_2542184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542184 prefixEnd_2542184 := by exact prefixLift 2542184
  have htrace : WordTrace (prefixWord ++ tailWord_2542184) baseStart_2542184 baseEnd_2542184 := by
    simpa [prefixWord, tailWord_2542184, baseEnd_2542184] using wordTrace_append hprefix tailTrace_2542184
  have hstable : (prefixWord ++ tailWord_2542184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542184).length < 2 ^ (prefixWord ++ tailWord_2542184).sum := by decide
  have hdescent : baseEnd_2542184 < baseStart_2542184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
