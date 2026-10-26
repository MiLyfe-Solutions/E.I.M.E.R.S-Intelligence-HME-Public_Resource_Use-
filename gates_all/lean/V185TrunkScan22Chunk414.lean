import V185TrunkScan22Chunk413

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3691832 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 5, 3]
def baseStart_3691832 : Nat := 118140960795 + 3691832 * 2 ^ 59
def prefixEnd_3691832 : Nat := 4983230072969 + 3 ^ 40 * 3691832 * 2
def baseEnd_3691832 : Nat := 1263789541099803282681053

theorem tailTrace_3691832 : CollatzResearch.WordTrace tailWord_3691832 prefixEnd_3691832 1263789541099803282681053 := by
  unfold tailWord_3691832
  simp only [CollatzResearch.WordTrace]
  refine ⟨67326087580565326776434875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89768116774087102368579833 67326087580565326776434875)
  ·
    refine ⟨100989131370847990164652313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67326087580565326776434875 100989131370847990164652313)
    ·
      refine ⟨75741848528135992623489235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100989131370847990164652313 75741848528135992623489235)
      ·
        refine ⟨113612772792203988935233853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75741848528135992623489235 113612772792203988935233853)
        ·
          refine ⟨42604789797076495850712695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113612772792203988935233853 42604789797076495850712695)
          ·
            refine ⟨63907184695614743776069043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42604789797076495850712695 63907184695614743776069043)
            ·
              refine ⟨95860777043422115664103565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63907184695614743776069043 95860777043422115664103565)
              ·
                refine ⟨35947791391283293374038837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95860777043422115664103565 35947791391283293374038837)
                ·
                  refine ⟨3370105442932808753816141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35947791391283293374038837 3370105442932808753816141)
                  ·
                    refine ⟨1263789541099803282681053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3370105442932808753816141 1263789541099803282681053)
                    ·
                      rfl

theorem cell22_3691832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_3691832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691832 prefixEnd_3691832 := by exact prefixLift 3691832
  have htrace : WordTrace (prefixWord ++ tailWord_3691832) baseStart_3691832 baseEnd_3691832 := by
    simpa [prefixWord, tailWord_3691832, baseEnd_3691832] using wordTrace_append hprefix tailTrace_3691832
  have hstable : (prefixWord ++ tailWord_3691832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691832).length < 2 ^ (prefixWord ++ tailWord_3691832).sum := by decide
  have hdescent : baseEnd_3691832 < baseStart_3691832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691845 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 9]
def baseStart_3691845 : Nat := 118140960795 + 3691845 * 2 ^ 59
def prefixEnd_3691845 : Nat := 4983230072969 + 3 ^ 40 * 3691845 * 2
def baseEnd_3691845 : Nat := 421264663755158527368671

theorem tailTrace_3691845 : CollatzResearch.WordTrace tailWord_3691845 prefixEnd_3691845 421264663755158527368671 := by
  unfold tailWord_3691845
  simp only [CollatzResearch.WordTrace]
  refine ⟨134652649310083556773092989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89768432873389037848728659 134652649310083556773092989)
  ·
    refine ⟨50494743491281333789909871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134652649310083556773092989 50494743491281333789909871)
    ·
      refine ⟨75742115236922000684864807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50494743491281333789909871 75742115236922000684864807)
      ·
        refine ⟨113613172855383001027297211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75742115236922000684864807 113613172855383001027297211)
        ·
          refine ⟨170419759283074501540945817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113613172855383001027297211 170419759283074501540945817)
          ·
            refine ⟨127814819462305876155709363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170419759283074501540945817 127814819462305876155709363)
            ·
              refine ⟨191722229193458814233564045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127814819462305876155709363 191722229193458814233564045)
              ·
                refine ⟨71895835947547055337586517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191722229193458814233564045 71895835947547055337586517)
                ·
                  refine ⟨421264663755158527368671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71895835947547055337586517 421264663755158527368671)
                  ·
                    rfl

theorem cell22_3691845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_3691845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691845 prefixEnd_3691845 := by exact prefixLift 3691845
  have htrace : WordTrace (prefixWord ++ tailWord_3691845) baseStart_3691845 baseEnd_3691845 := by
    simpa [prefixWord, tailWord_3691845, baseEnd_3691845] using wordTrace_append hprefix tailTrace_3691845
  have hstable : (prefixWord ++ tailWord_3691845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691845).length < 2 ^ (prefixWord ++ tailWord_3691845).sum := by decide
  have hdescent : baseEnd_3691845 < baseStart_3691845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691877 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_3691877 : Nat := 118140960795 + 3691877 * 2 ^ 59
def prefixEnd_3691877 : Nat := 4983230072969 + 3 ^ 40 * 3691877 * 2
def baseEnd_3691877 : Nat := 1263804945519438165305915

theorem tailTrace_3691877 : CollatzResearch.WordTrace tailWord_3691877 prefixEnd_3691877 1263804945519438165305915 := by
  unfold tailWord_3691877
  simp only [CollatzResearch.WordTrace]
  refine ⟨134653816445967626238257885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89769210963978417492171923 134653816445967626238257885)
  ·
    refine ⟨50495181167237859839346707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134653816445967626238257885 50495181167237859839346707)
    ·
      refine ⟨75742771750856789759020061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50495181167237859839346707 75742771750856789759020061)
      ·
        refine ⟨28403539406571296159632523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75742771750856789759020061 28403539406571296159632523)
        ·
          refine ⟨42605309109856944239448785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28403539406571296159632523 42605309109856944239448785)
          ·
            refine ⟨31953981832392708179586589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42605309109856944239448785 31953981832392708179586589)
            ·
              refine ⟨11982743187147265567344971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31953981832392708179586589 11982743187147265567344971)
              ·
                refine ⟨17974114780720898351017457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11982743187147265567344971 17974114780720898351017457)
                ·
                  refine ⟨13480586085540673763263093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17974114780720898351017457 13480586085540673763263093)
                  ·
                    refine ⟨1263804945519438165305915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13480586085540673763263093 1263804945519438165305915)
                    ·
                      rfl

theorem cell22_3691877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_3691877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691877 prefixEnd_3691877 := by exact prefixLift 3691877
  have htrace : WordTrace (prefixWord ++ tailWord_3691877) baseStart_3691877 baseEnd_3691877 := by
    simpa [prefixWord, tailWord_3691877, baseEnd_3691877] using wordTrace_append hprefix tailTrace_3691877
  have hstable : (prefixWord ++ tailWord_3691877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691877).length < 2 ^ (prefixWord ++ tailWord_3691877).sum := by decide
  have hdescent : baseEnd_3691877 < baseStart_3691877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691924 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 6]
def baseStart_3691924 : Nat := 118140960795 + 3691924 * 2 ^ 59
def prefixEnd_3691924 : Nat := 4983230072969 + 3 ^ 40 * 3691924 * 2
def baseEnd_3691924 : Nat := 421273678193315236460257

theorem tailTrace_3691924 : CollatzResearch.WordTrace tailWord_3691924 prefixEnd_3691924 421273678193315236460257 := by
  unfold tailWord_3691924
  simp only [CollatzResearch.WordTrace]
  refine ⟨67327765338398676632609413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89770353784531568843479217 67327765338398676632609413)
  ·
    refine ⟨12623956000949751868614265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67327765338398676632609413 12623956000949751868614265)
    ·
      refine ⟨9467967000712313901460699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12623956000949751868614265 9467967000712313901460699)
      ·
        refine ⟨14201950501068470852191049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9467967000712313901460699 14201950501068470852191049)
        ·
          refine ⟨10651462875801353139143287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14201950501068470852191049 10651462875801353139143287)
          ·
            refine ⟨15977194313702029708714931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10651462875801353139143287 15977194313702029708714931)
            ·
              refine ⟨23965791470553044563072397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15977194313702029708714931 23965791470553044563072397)
              ·
                refine ⟨8987171801457391711152149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23965791470553044563072397 8987171801457391711152149)
                ·
                  refine ⟨421273678193315236460257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8987171801457391711152149 421273678193315236460257)
                  ·
                    rfl

theorem cell22_3691924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_3691924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691924 prefixEnd_3691924 := by exact prefixLift 3691924
  have htrace : WordTrace (prefixWord ++ tailWord_3691924) baseStart_3691924 baseEnd_3691924 := by
    simpa [prefixWord, tailWord_3691924, baseEnd_3691924] using wordTrace_append hprefix tailTrace_3691924
  have hstable : (prefixWord ++ tailWord_3691924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691924).length < 2 ^ (prefixWord ++ tailWord_3691924).sum := by decide
  have hdescent : baseEnd_3691924 < baseStart_3691924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691990 : List Nat := [5, 2, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_3691990 : Nat := 118140960795 + 3691990 * 2 ^ 59
def prefixEnd_3691990 : Nat := 4983230072969 + 3 ^ 40 * 3691990 * 2
def baseEnd_3691990 : Nat := 1263843627728743537230569

theorem tailTrace_3691990 : CollatzResearch.WordTrace tailWord_3691990 prefixEnd_3691990 1263843627728743537230569 := by
  unfold tailWord_3691990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8416121118409890408570089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89771958596372164358080949 8416121118409890408570089)
  ·
    refine ⟨6312090838807417806427567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8416121118409890408570089 6312090838807417806427567)
    ·
      refine ⟨9468136258211126709641351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6312090838807417806427567 9468136258211126709641351)
      ·
        refine ⟨14202204387316690064462027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9468136258211126709641351 14202204387316690064462027)
        ·
          refine ⟨21303306580975035096693041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14202204387316690064462027 21303306580975035096693041)
          ·
            refine ⟨15977479935731276322519781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21303306580975035096693041 15977479935731276322519781)
            ·
              refine ⟨2995777487949614310472459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15977479935731276322519781 2995777487949614310472459)
              ·
                refine ⟨4493666231924421465708689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995777487949614310472459 4493666231924421465708689)
                ·
                  refine ⟨3370249673943316099281517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4493666231924421465708689 3370249673943316099281517)
                  ·
                    refine ⟨1263843627728743537230569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3370249673943316099281517 1263843627728743537230569)
                    ·
                      rfl

theorem cell22_3691990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_3691990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691990 prefixEnd_3691990 := by exact prefixLift 3691990
  have htrace : WordTrace (prefixWord ++ tailWord_3691990) baseStart_3691990 baseEnd_3691990 := by
    simpa [prefixWord, tailWord_3691990, baseEnd_3691990] using wordTrace_append hprefix tailTrace_3691990
  have hstable : (prefixWord ++ tailWord_3691990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691990).length < 2 ^ (prefixWord ++ tailWord_3691990).sum := by decide
  have hdescent : baseEnd_3691990 < baseStart_3691990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692012 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_3692012 : Nat := 118140960795 + 3692012 * 2 ^ 59
def prefixEnd_3692012 : Nat := 4983230072969 + 3 ^ 40 * 3692012 * 2
def baseEnd_3692012 : Nat := 1263851158778342813180501

theorem tailTrace_3692012 : CollatzResearch.WordTrace tailWord_3692012 prefixEnd_3692012 1263851158778342813180501 := by
  unfold tailWord_3692012
  simp only [CollatzResearch.WordTrace]
  refine ⟨67329370150239272147211145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89772493533652362862948193 67329370150239272147211145)
  ·
    refine ⟨50497027612679454110408359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67329370150239272147211145 50497027612679454110408359)
    ·
      refine ⟨75745541419019181165612539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50497027612679454110408359 75745541419019181165612539)
      ·
        refine ⟨113618312128528771748418809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75745541419019181165612539 113618312128528771748418809)
        ·
          refine ⟨85213734096396578811314107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113618312128528771748418809 85213734096396578811314107)
          ·
            refine ⟨127820601144594868216971161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85213734096396578811314107 127820601144594868216971161)
            ·
              refine ⟨95865450858446151162728371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127820601144594868216971161 95865450858446151162728371)
              ·
                refine ⟨143798176287669226744092557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95865450858446151162728371 143798176287669226744092557)
                ·
                  refine ⟨53924316107875960029034709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143798176287669226744092557 53924316107875960029034709)
                  ·
                    refine ⟨1263851158778342813180501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53924316107875960029034709 1263851158778342813180501)
                    ·
                      rfl

theorem cell22_3692012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_3692012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692012 prefixEnd_3692012 := by exact prefixLift 3692012
  have htrace : WordTrace (prefixWord ++ tailWord_3692012) baseStart_3692012 baseEnd_3692012 := by
    simpa [prefixWord, tailWord_3692012, baseEnd_3692012] using wordTrace_append hprefix tailTrace_3692012
  have hstable : (prefixWord ++ tailWord_3692012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692012).length < 2 ^ (prefixWord ++ tailWord_3692012).sum := by decide
  have hdescent : baseEnd_3692012 < baseStart_3692012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692046 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_3692046 : Nat := 118140960795 + 3692046 * 2 ^ 59
def prefixEnd_3692046 : Nat := 4983230072969 + 3 ^ 40 * 3692046 * 2
def baseEnd_3692046 : Nat := 1263862797673178057830397

theorem tailTrace_3692046 : CollatzResearch.WordTrace tailWord_3692046 prefixEnd_3692046 1263862797673178057830397 := by
  unfold tailWord_3692046
  simp only [CollatzResearch.WordTrace]
  refine ⟨16832497547794421012644999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89773320254903578734106661 16832497547794421012644999)
  ·
    refine ⟨25248746321691631518967499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16832497547794421012644999 25248746321691631518967499)
    ·
      refine ⟨37873119482537447278451249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25248746321691631518967499 37873119482537447278451249)
      ·
        refine ⟨28404839611903085458838437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37873119482537447278451249 28404839611903085458838437)
        ·
          refine ⟨5325907427231828523532207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28404839611903085458838437 5325907427231828523532207)
          ·
            refine ⟨7988861140847742785298311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5325907427231828523532207 7988861140847742785298311)
            ·
              refine ⟨11983291711271614177947467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7988861140847742785298311 11983291711271614177947467)
              ·
                refine ⟨17974937566907421266921201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11983291711271614177947467 17974937566907421266921201)
                ·
                  refine ⟨13481203175180565950190901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17974937566907421266921201 13481203175180565950190901)
                  ·
                    refine ⟨1263862797673178057830397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13481203175180565950190901 1263862797673178057830397)
                    ·
                      rfl

theorem cell22_3692046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_3692046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692046 prefixEnd_3692046 := by exact prefixLift 3692046
  have htrace : WordTrace (prefixWord ++ tailWord_3692046) baseStart_3692046 baseEnd_3692046 := by
    simpa [prefixWord, tailWord_3692046, baseEnd_3692046] using wordTrace_append hprefix tailTrace_3692046
  have hstable : (prefixWord ++ tailWord_3692046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692046).length < 2 ^ (prefixWord ++ tailWord_3692046).sum := by decide
  have hdescent : baseEnd_3692046 < baseStart_3692046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692061 : List Nat := [1, 4, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3692061 : Nat := 118140960795 + 3692061 * 2 ^ 59
def prefixEnd_3692061 : Nat := 4983230072969 + 3 ^ 40 * 3692061 * 2
def baseEnd_3692061 : Nat := 1263867932479723018705351

theorem tailTrace_3692061 : CollatzResearch.WordTrace tailWord_3692061 prefixEnd_3692061 1263867932479723018705351 := by
  unfold tailWord_3692061
  simp only [CollatzResearch.WordTrace]
  refine ⟨134660527477301025662956037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89773684984867350441970691 134660527477301025662956037)
  ·
    refine ⟨25248848901993942311804257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134660527477301025662956037 25248848901993942311804257)
    ·
      refine ⟨18936636676495456733853193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25248848901993942311804257 18936636676495456733853193)
      ·
        refine ⟨14202477507371592550389895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18936636676495456733853193 14202477507371592550389895)
        ·
          refine ⟨21303716261057388825584843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14202477507371592550389895 21303716261057388825584843)
          ·
            refine ⟨31955574391586083238377265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21303716261057388825584843 31955574391586083238377265)
            ·
              refine ⟨23966680793689562428782949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31955574391586083238377265 23966680793689562428782949)
              ·
                refine ⟨4493752648816792955396803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23966680793689562428782949 4493752648816792955396803)
                ·
                  refine ⟨6740628973225189433095205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493752648816792955396803 6740628973225189433095205)
                  ·
                    refine ⟨1263867932479723018705351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6740628973225189433095205 1263867932479723018705351)
                    ·
                      rfl

theorem cell22_3692061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3692061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692061 prefixEnd_3692061 := by exact prefixLift 3692061
  have htrace : WordTrace (prefixWord ++ tailWord_3692061) baseStart_3692061 baseEnd_3692061 := by
    simpa [prefixWord, tailWord_3692061, baseEnd_3692061] using wordTrace_append hprefix tailTrace_3692061
  have hstable : (prefixWord ++ tailWord_3692061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692061).length < 2 ^ (prefixWord ++ tailWord_3692061).sum := by decide
  have hdescent : baseEnd_3692061 < baseStart_3692061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692078 : List Nat := [4, 1, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3692078 : Nat := 118140960795 + 3692078 * 2 ^ 59
def prefixEnd_3692078 : Nat := 4983230072969 + 3 ^ 40 * 3692078 * 2
def baseEnd_3692078 : Nat := 1263873751927140641030299

theorem tailTrace_3692078 : CollatzResearch.WordTrace tailWord_3692078 prefixEnd_3692078 1263873751927140641030299 := by
  unfold tailWord_3692078
  simp only [CollatzResearch.WordTrace]
  refine ⟨16832643439779929695790611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89774098345492958377549925 16832643439779929695790611)
  ·
    refine ⟨25248965159669894543685917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16832643439779929695790611 25248965159669894543685917)
    ·
      refine ⟨9468361934876210453882219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25248965159669894543685917 9468361934876210453882219)
      ·
        refine ⟨14202542902314315680823329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9468361934876210453882219 14202542902314315680823329)
        ·
          refine ⟨10651907176735736760617497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14202542902314315680823329 10651907176735736760617497)
          ·
            refine ⟨7988930382551802570463123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10651907176735736760617497 7988930382551802570463123)
            ·
              refine ⟨11983395573827703855694685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7988930382551802570463123 11983395573827703855694685)
              ·
                refine ⟨4493773340185388945885507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11983395573827703855694685 4493773340185388945885507)
                ·
                  refine ⟨6740660010278083418828261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493773340185388945885507 6740660010278083418828261)
                  ·
                    refine ⟨1263873751927140641030299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6740660010278083418828261 1263873751927140641030299)
                    ·
                      rfl

theorem cell22_3692078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3692078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692078 prefixEnd_3692078 := by exact prefixLift 3692078
  have htrace : WordTrace (prefixWord ++ tailWord_3692078) baseStart_3692078 baseEnd_3692078 := by
    simpa [prefixWord, tailWord_3692078, baseEnd_3692078] using wordTrace_append hprefix tailTrace_3692078
  have hstable : (prefixWord ++ tailWord_3692078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692078).length < 2 ^ (prefixWord ++ tailWord_3692078).sum := by decide
  have hdescent : baseEnd_3692078 < baseStart_3692078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692239 : List Nat := [1, 1, 2, 1, 1, 3, 1, 12]
def baseStart_3692239 : Nat := 118140960795 + 3692239 * 2 ^ 59
def prefixEnd_3692239 : Nat := 4983230072969 + 3 ^ 40 * 3692239 * 2
def baseEnd_3692239 : Nat := 140436540613043320861645

theorem tailTrace_3692239 : CollatzResearch.WordTrace tailWord_3692239 prefixEnd_3692239 140436540613043320861645 := by
  unfold tailWord_3692239
  simp only [CollatzResearch.WordTrace]
  refine ⟨134667019670656162062935771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89778013113770774708623847 134667019670656162062935771)
  ·
    refine ⟨202000529505984243094403657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134667019670656162062935771 202000529505984243094403657)
    ·
      refine ⟨151500397129488182320802743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202000529505984243094403657 151500397129488182320802743)
      ·
        refine ⟨227250595694232273481204115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151500397129488182320802743 227250595694232273481204115)
        ·
          refine ⟨340875893541348410221806173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227250595694232273481204115 340875893541348410221806173)
          ·
            refine ⟨127828460078005653833177315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340875893541348410221806173 127828460078005653833177315)
            ·
              refine ⟨191742690117008480749765973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127828460078005653833177315 191742690117008480749765973)
              ·
                refine ⟨140436540613043320861645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 191742690117008480749765973 140436540613043320861645)
                ·
                  rfl

theorem cell22_3692239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 12].length) (baseStart_3692239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692239 prefixEnd_3692239 := by exact prefixLift 3692239
  have htrace : WordTrace (prefixWord ++ tailWord_3692239) baseStart_3692239 baseEnd_3692239 := by
    simpa [prefixWord, tailWord_3692239, baseEnd_3692239] using wordTrace_append hprefix tailTrace_3692239
  have hstable : (prefixWord ++ tailWord_3692239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692239).length < 2 ^ (prefixWord ++ tailWord_3692239).sum := by decide
  have hdescent : baseEnd_3692239 < baseStart_3692239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692241 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 1, 6]
def baseStart_3692241 : Nat := 118140960795 + 3692241 * 2 ^ 59
def prefixEnd_3692241 : Nat := 4983230072969 + 3 ^ 40 * 3692241 * 2
def baseEnd_3692241 : Nat := 1263929550158262549204799

theorem tailTrace_3692241 : CollatzResearch.WordTrace tailWord_3692241 prefixEnd_3692241 1263929550158262549204799 := by
  unfold tailWord_3692241
  simp only [CollatzResearch.WordTrace]
  refine ⟨134667092616648916404508577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89778061744432610936339051 134667092616648916404508577)
  ·
    refine ⟨101000319462486687303381433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134667092616648916404508577 101000319462486687303381433)
    ·
      refine ⟨75750239596865015477536075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101000319462486687303381433 75750239596865015477536075)
      ·
        refine ⟨113625359395297523216304113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75750239596865015477536075 113625359395297523216304113)
        ·
          refine ⟨85219019546473142412228085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113625359395297523216304113 85219019546473142412228085)
          ·
            refine ⟨7989283082481857101146383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85219019546473142412228085 7989283082481857101146383)
            ·
              refine ⟨11983924623722785651719575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7989283082481857101146383 11983924623722785651719575)
              ·
                refine ⟨17975886935584178477579363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11983924623722785651719575 17975886935584178477579363)
                ·
                  refine ⟨26963830403376267716369045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17975886935584178477579363 26963830403376267716369045)
                  ·
                    refine ⟨1263929550158262549204799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26963830403376267716369045 1263929550158262549204799)
                    ·
                      rfl

theorem cell22_3692241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_3692241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692241 prefixEnd_3692241 := by exact prefixLift 3692241
  have htrace : WordTrace (prefixWord ++ tailWord_3692241) baseStart_3692241 baseEnd_3692241 := by
    simpa [prefixWord, tailWord_3692241, baseEnd_3692241] using wordTrace_append hprefix tailTrace_3692241
  have hstable : (prefixWord ++ tailWord_3692241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692241).length < 2 ^ (prefixWord ++ tailWord_3692241).sum := by decide
  have hdescent : baseEnd_3692241 < baseStart_3692241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692376 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 5, 6]
def baseStart_3692376 : Nat := 118140960795 + 3692376 * 2 ^ 59
def prefixEnd_3692376 : Nat := 4983230072969 + 3 ^ 40 * 3692376 * 2
def baseEnd_3692376 : Nat := 1263975763417167197079385

theorem tailTrace_3692376 : CollatzResearch.WordTrace tailWord_3692376 prefixEnd_3692376 1263975763417167197079385 := by
  unfold tailWord_3692376
  simp only [CollatzResearch.WordTrace]
  refine ⟨67336008235579917230336491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89781344314106556307115321 67336008235579917230336491)
  ·
    refine ⟨101004012353369875845504737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67336008235579917230336491 101004012353369875845504737)
    ·
      refine ⟨75753009265027406884128553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101004012353369875845504737 75753009265027406884128553)
      ·
        refine ⟨56814756948770555163096415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75753009265027406884128553 56814756948770555163096415)
        ·
          refine ⟨85222135423155832744644623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56814756948770555163096415 85222135423155832744644623)
          ·
            refine ⟨127833203134733749116966935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85222135423155832744644623 127833203134733749116966935)
            ·
              refine ⟨191749804702100623675450403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127833203134733749116966935 191749804702100623675450403)
              ·
                refine ⟨287624707053150935513175605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191749804702100623675450403 287624707053150935513175605)
                ·
                  refine ⟨26964816286232900204360213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 287624707053150935513175605 26964816286232900204360213)
                  ·
                    refine ⟨1263975763417167197079385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26964816286232900204360213 1263975763417167197079385)
                    ·
                      rfl

theorem cell22_3692376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_3692376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692376 prefixEnd_3692376 := by exact prefixLift 3692376
  have htrace : WordTrace (prefixWord ++ tailWord_3692376) baseStart_3692376 baseEnd_3692376 := by
    simpa [prefixWord, tailWord_3692376, baseEnd_3692376] using wordTrace_append hprefix tailTrace_3692376
  have hstable : (prefixWord ++ tailWord_3692376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692376).length < 2 ^ (prefixWord ++ tailWord_3692376).sum := by decide
  have hdescent : baseEnd_3692376 < baseStart_3692376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692414 : List Nat := [4, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_3692414 : Nat := 118140960795 + 3692414 * 2 ^ 59
def prefixEnd_3692414 : Nat := 4983230072969 + 3 ^ 40 * 3692414 * 2
def baseEnd_3692414 : Nat := 421329590531249254876423

theorem tailTrace_3692414 : CollatzResearch.WordTrace tailWord_3692414 prefixEnd_3692414 421329590531249254876423 := by
  unfold tailWord_3692414
  simp only [CollatzResearch.WordTrace]
  refine ⟨16834175305627770868819537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89782268296681444633704197 16834175305627770868819537)
  ·
    refine ⟨12625631479220828151614653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16834175305627770868819537 12625631479220828151614653)
    ·
      refine ⟨4734611804707810556855495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12625631479220828151614653 4734611804707810556855495)
      ·
        refine ⟨7101917707061715835283243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4734611804707810556855495 7101917707061715835283243)
        ·
          refine ⟨10652876560592573752924865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7101917707061715835283243 10652876560592573752924865)
          ·
            refine ⟨7989657420444430314693649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10652876560592573752924865 7989657420444430314693649)
            ·
              refine ⟨5992243065333322736020237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7989657420444430314693649 5992243065333322736020237)
              ·
                refine ⟨2247091149499996026007589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5992243065333322736020237 2247091149499996026007589)
                ·
                  refine ⟨421329590531249254876423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247091149499996026007589 421329590531249254876423)
                  ·
                    rfl

theorem cell22_3692414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_3692414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692414 prefixEnd_3692414 := by exact prefixLift 3692414
  have htrace : WordTrace (prefixWord ++ tailWord_3692414) baseStart_3692414 baseEnd_3692414 := by
    simpa [prefixWord, tailWord_3692414, baseEnd_3692414] using wordTrace_append hprefix tailTrace_3692414
  have hstable : (prefixWord ++ tailWord_3692414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692414).length < 2 ^ (prefixWord ++ tailWord_3692414).sum := by decide
  have hdescent : baseEnd_3692414 < baseStart_3692414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692446 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_3692446 : Nat := 118140960795 + 3692446 * 2 ^ 59
def prefixEnd_3692446 : Nat := 4983230072969 + 3 ^ 40 * 3692446 * 2
def baseEnd_3692446 : Nat := 1263999725847710347829171

theorem tailTrace_3692446 : CollatzResearch.WordTrace tailWord_3692446 prefixEnd_3692446 1263999725847710347829171 := by
  unfold tailWord_3692446
  simp only [CollatzResearch.WordTrace]
  refine ⟨16834321197613279551965149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89783046387270824277147461 16834321197613279551965149)
  ·
    refine ⟨6312870449104979831986931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16834321197613279551965149 6312870449104979831986931)
    ·
      refine ⟨9469305673657469747980397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6312870449104979831986931 9469305673657469747980397)
      ·
        refine ⟨3550989627621551155492649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9469305673657469747980397 3550989627621551155492649)
        ·
          refine ⟨2663242220716163366619487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3550989627621551155492649 2663242220716163366619487)
          ·
            refine ⟨3994863331074245049929231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663242220716163366619487 3994863331074245049929231)
            ·
              refine ⟨5992294996611367574893847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994863331074245049929231 5992294996611367574893847)
              ·
                refine ⟨8988442494917051362340771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5992294996611367574893847 8988442494917051362340771)
                ·
                  refine ⟨13482663742375577043511157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8988442494917051362340771 13482663742375577043511157)
                  ·
                    refine ⟨1263999725847710347829171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13482663742375577043511157 1263999725847710347829171)
                    ·
                      rfl

theorem cell22_3692446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_3692446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692446 prefixEnd_3692446 := by exact prefixLift 3692446
  have htrace : WordTrace (prefixWord ++ tailWord_3692446) baseStart_3692446 baseEnd_3692446 := by
    simpa [prefixWord, tailWord_3692446, baseEnd_3692446] using wordTrace_append hprefix tailTrace_3692446
  have hstable : (prefixWord ++ tailWord_3692446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692446).length < 2 ^ (prefixWord ++ tailWord_3692446).sum := by decide
  have hdescent : baseEnd_3692446 < baseStart_3692446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692453 : List Nat := [1, 3, 1, 2, 1, 1, 1, 7, 5]
def baseStart_3692453 : Nat := 118140960795 + 3692453 * 2 ^ 59
def prefixEnd_3692453 : Nat := 4983230072969 + 3 ^ 40 * 3692453 * 2
def baseEnd_3692453 : Nat := 421334040696921554301383

theorem tailTrace_3692453 : CollatzResearch.WordTrace tailWord_3692453 prefixEnd_3692453 421334040696921554301383 := by
  unfold tailWord_3692453
  simp only [CollatzResearch.WordTrace]
  refine ⟨134674824891880876611226013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89783216594587251074150675 134674824891880876611226013)
  ·
    refine ⟨50503059334455328729209755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134674824891880876611226013 50503059334455328729209755)
    ·
      refine ⟨75754589001682993093814633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50503059334455328729209755 75754589001682993093814633)
      ·
        refine ⟨56815941751262244820360975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75754589001682993093814633 56815941751262244820360975)
        ·
          refine ⟨85223912626893367230541463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56815941751262244820360975 85223912626893367230541463)
          ·
            refine ⟨127835868940340050845812195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85223912626893367230541463 127835868940340050845812195)
            ·
              refine ⟨191753803410510076268718293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127835868940340050845812195 191753803410510076268718293)
              ·
                refine ⟨4494229767433829912548085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 191753803410510076268718293 4494229767433829912548085)
                ·
                  refine ⟨421334040696921554301383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4494229767433829912548085 421334040696921554301383)
                  ·
                    rfl

theorem cell22_3692453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_3692453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692453 prefixEnd_3692453 := by exact prefixLift 3692453
  have htrace : WordTrace (prefixWord ++ tailWord_3692453) baseStart_3692453 baseEnd_3692453 := by
    simpa [prefixWord, tailWord_3692453, baseEnd_3692453] using wordTrace_append hprefix tailTrace_3692453
  have hstable : (prefixWord ++ tailWord_3692453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692453).length < 2 ^ (prefixWord ++ tailWord_3692453).sum := by decide
  have hdescent : baseEnd_3692453 < baseStart_3692453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692500 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_3692500 : Nat := 118140960795 + 3692500 * 2 ^ 59
def prefixEnd_3692500 : Nat := 4983230072969 + 3 ^ 40 * 3692500 * 2
def baseEnd_3692500 : Nat := 1264018211151272206979005

theorem tailTrace_3692500 : CollatzResearch.WordTrace tailWord_3692500 prefixEnd_3692500 1264018211151272206979005 := by
  unfold tailWord_3692500
  simp only [CollatzResearch.WordTrace]
  refine ⟨67338269561355301819093477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89784359415140402425457969 67338269561355301819093477)
  ·
    refine ⟨12625925542754119091080027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67338269561355301819093477 12625925542754119091080027)
    ·
      refine ⟨18938888314131178636620041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12625925542754119091080027 18938888314131178636620041)
      ·
        refine ⟨14204166235598383977465031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18938888314131178636620041 14204166235598383977465031)
        ·
          refine ⟨21306249353397575966197547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14204166235598383977465031 21306249353397575966197547)
          ·
            refine ⟨31959374030096363949296321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21306249353397575966197547 31959374030096363949296321)
            ·
              refine ⟨23969530522572272961972241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31959374030096363949296321 23969530522572272961972241)
              ·
                refine ⟨17977147891929204721479181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23969530522572272961972241 17977147891929204721479181)
                ·
                  refine ⟨6741430459473451770554693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17977147891929204721479181 6741430459473451770554693)
                  ·
                    refine ⟨1264018211151272206979005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6741430459473451770554693 1264018211151272206979005)
                    ·
                      rfl

theorem cell22_3692500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_3692500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692500 prefixEnd_3692500 := by exact prefixLift 3692500
  have htrace : WordTrace (prefixWord ++ tailWord_3692500) baseStart_3692500 baseEnd_3692500 := by
    simpa [prefixWord, tailWord_3692500, baseEnd_3692500] using wordTrace_append hprefix tailTrace_3692500
  have hstable : (prefixWord ++ tailWord_3692500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692500).length < 2 ^ (prefixWord ++ tailWord_3692500).sum := by decide
  have hdescent : baseEnd_3692500 < baseStart_3692500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692528 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 1, 6]
def baseStart_3692528 : Nat := 118140960795 + 3692528 * 2 ^ 59
def prefixEnd_3692528 : Nat := 4983230072969 + 3 ^ 40 * 3692528 * 2
def baseEnd_3692528 : Nat := 1264027796123489467278919

theorem tailTrace_3692528 : CollatzResearch.WordTrace tailWord_3692528 prefixEnd_3692528 1264027796123489467278919 := by
  unfold tailWord_3692528
  simp only [CollatzResearch.WordTrace]
  refine ⟨67338780183304582210103119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89785040244406109613470825 67338780183304582210103119)
  ·
    refine ⟨101008170274956873315154679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67338780183304582210103119 101008170274956873315154679)
    ·
      refine ⟨151512255412435309972732019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101008170274956873315154679 151512255412435309972732019)
      ·
        refine ⟨227268383118652964959098029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151512255412435309972732019 227268383118652964959098029)
        ·
          refine ⟨85225643669494861859661761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227268383118652964959098029 85225643669494861859661761)
          ·
            refine ⟨63919232752121146394746321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85225643669494861859661761 63919232752121146394746321)
            ·
              refine ⟨47939424564090859796059741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63919232752121146394746321 47939424564090859796059741)
              ·
                refine ⟨17977284211534072423522403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47939424564090859796059741 17977284211534072423522403)
                ·
                  refine ⟨26965926317301108635283605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17977284211534072423522403 26965926317301108635283605)
                  ·
                    refine ⟨1264027796123489467278919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26965926317301108635283605 1264027796123489467278919)
                    ·
                      rfl

theorem cell22_3692528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_3692528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692528 prefixEnd_3692528 := by exact prefixLift 3692528
  have htrace : WordTrace (prefixWord ++ tailWord_3692528) baseStart_3692528 baseEnd_3692528 := by
    simpa [prefixWord, tailWord_3692528, baseEnd_3692528] using wordTrace_append hprefix tailTrace_3692528
  have hstable : (prefixWord ++ tailWord_3692528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692528).length < 2 ^ (prefixWord ++ tailWord_3692528).sum := by decide
  have hdescent : baseEnd_3692528 < baseStart_3692528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692545 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 2, 4]
def baseStart_3692545 : Nat := 118140960795 + 3692545 * 2 ^ 59
def prefixEnd_3692545 : Nat := 4983230072969 + 3 ^ 40 * 3692545 * 2
def baseEnd_3692545 : Nat := 1264033615570907089603867

theorem tailTrace_3692545 : CollatzResearch.WordTrace tailWord_3692545 prefixEnd_3692545 1264033615570907089603867 := by
  unfold tailWord_3692545
  simp only [CollatzResearch.WordTrace]
  refine ⟨134678180407547576323575089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89785453605031717549050059 134678180407547576323575089)
  ·
    refine ⟨101008635305660682242681317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134678180407547576323575089 101008635305660682242681317)
    ·
      refine ⟨18939119119811377920502747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101008635305660682242681317 18939119119811377920502747)
      ·
        refine ⟨28408678679717066880754121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18939119119811377920502747 28408678679717066880754121)
        ·
          refine ⟨21306509009787800160565591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28408678679717066880754121 21306509009787800160565591)
          ·
            refine ⟨31959763514681700240848387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21306509009787800160565591 31959763514681700240848387)
            ·
              refine ⟨47939645272022550361272581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31959763514681700240848387 47939645272022550361272581)
              ·
                refine ⟨8988683488504228192738609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47939645272022550361272581 8988683488504228192738609)
                ·
                  refine ⟨6741512616378171144553957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8988683488504228192738609 6741512616378171144553957)
                  ·
                    refine ⟨1264033615570907089603867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6741512616378171144553957 1264033615570907089603867)
                    ·
                      rfl

theorem cell22_3692545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_3692545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692545 prefixEnd_3692545 := by exact prefixLift 3692545
  have htrace : WordTrace (prefixWord ++ tailWord_3692545) baseStart_3692545 baseEnd_3692545 := by
    simpa [prefixWord, tailWord_3692545, baseEnd_3692545] using wordTrace_append hprefix tailTrace_3692545
  have hstable : (prefixWord ++ tailWord_3692545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692545).length < 2 ^ (prefixWord ++ tailWord_3692545).sum := by decide
  have hdescent : baseEnd_3692545 < baseStart_3692545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692549 : List Nat := [1, 3, 1, 1, 2, 6, 2, 2, 4]
def baseStart_3692549 : Nat := 118140960795 + 3692549 * 2 ^ 59
def prefixEnd_3692549 : Nat := 4983230072969 + 3 ^ 40 * 3692549 * 2
def baseEnd_3692549 : Nat := 421344994950884137501285

theorem tailTrace_3692549 : CollatzResearch.WordTrace tailWord_3692549 prefixEnd_3692549 421344994950884137501285 := by
  unfold tailWord_3692549
  simp only [CollatzResearch.WordTrace]
  refine ⟨134678326299533085006720701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89785550866355390004480467 134678326299533085006720701)
  ·
    refine ⟨50504372362324906877520263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134678326299533085006720701 50504372362324906877520263)
    ·
      refine ⟨75756558543487360316280395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50504372362324906877520263 75756558543487360316280395)
      ·
        refine ⟨113634837815231040474420593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75756558543487360316280395 113634837815231040474420593)
        ·
          refine ⟨85226128361423280355815445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113634837815231040474420593 85226128361423280355815445)
          ·
            refine ⟨3994974766941716266678849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85226128361423280355815445 3994974766941716266678849)
            ·
              refine ⟨2996231075206287200009137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3994974766941716266678849 2996231075206287200009137)
              ·
                refine ⟨2247173306404715400006853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2996231075206287200009137 2247173306404715400006853)
                ·
                  refine ⟨421344994950884137501285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247173306404715400006853 421344994950884137501285)
                  ·
                    rfl

theorem cell22_3692549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_3692549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692549 prefixEnd_3692549 := by exact prefixLift 3692549
  have htrace : WordTrace (prefixWord ++ tailWord_3692549) baseStart_3692549 baseEnd_3692549 := by
    simpa [prefixWord, tailWord_3692549, baseEnd_3692549] using wordTrace_append hprefix tailTrace_3692549
  have hstable : (prefixWord ++ tailWord_3692549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692549).length < 2 ^ (prefixWord ++ tailWord_3692549).sum := by decide
  have hdescent : baseEnd_3692549 < baseStart_3692549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692577 : List Nat := [1, 2, 3, 2, 4, 1, 3, 6]
def baseStart_3692577 : Nat := 118140960795 + 3692577 * 2 ^ 59
def prefixEnd_3692577 : Nat := 4983230072969 + 3 ^ 40 * 3692577 * 2
def baseEnd_3692577 : Nat := 140449396647207741422641

theorem tailTrace_3692577 : CollatzResearch.WordTrace tailWord_3692577 prefixEnd_3692577 140449396647207741422641 := by
  unfold tailWord_3692577
  simp only [CollatzResearch.WordTrace]
  refine ⟨134679347543431645788739985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89786231695621097192493323 134679347543431645788739985)
  ·
    refine ⟨101009510657573734341554989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134679347543431645788739985 101009510657573734341554989)
    ·
      refine ⟨37878566496590150378083121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101009510657573734341554989 37878566496590150378083121)
      ·
        refine ⟨28408924872442612783562341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37878566496590150378083121 28408924872442612783562341)
        ·
          refine ⟨5326673413582989896917939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28408924872442612783562341 5326673413582989896917939)
          ·
            refine ⟨7990010120374484845376909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326673413582989896917939 7990010120374484845376909)
            ·
              refine ⟨2996253795140431817016341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7990010120374484845376909 2996253795140431817016341)
              ·
                refine ⟨140449396647207741422641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2996253795140431817016341 140449396647207741422641)
                ·
                  rfl

theorem cell22_3692577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 6].length) (baseStart_3692577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692577 prefixEnd_3692577 := by exact prefixLift 3692577
  have htrace : WordTrace (prefixWord ++ tailWord_3692577) baseStart_3692577 baseEnd_3692577 := by
    simpa [prefixWord, tailWord_3692577, baseEnd_3692577] using wordTrace_append hprefix tailTrace_3692577
  have hstable : (prefixWord ++ tailWord_3692577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692577).length < 2 ^ (prefixWord ++ tailWord_3692577).sum := by decide
  have hdescent : baseEnd_3692577 < baseStart_3692577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692603 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 3, 7]
def baseStart_3692603 : Nat := 118140960795 + 3692603 * 2 ^ 59
def prefixEnd_3692603 : Nat := 4983230072969 + 3 ^ 40 * 3692603 * 2
def baseEnd_3692603 : Nat := 1264053470156214271653689

theorem tailTrace_3692603 : CollatzResearch.WordTrace tailWord_3692603 prefixEnd_3692603 1264053470156214271653689 := by
  unfold tailWord_3692603
  simp only [CollatzResearch.WordTrace]
  refine ⟨134680295841337452229186463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89786863894224968152790975 134680295841337452229186463)
  ·
    refine ⟨202020443762006178343779695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134680295841337452229186463 202020443762006178343779695)
    ·
      refine ⟨303030665643009267515669543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202020443762006178343779695 303030665643009267515669543)
      ·
        refine ⟨454545998464513901273504315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303030665643009267515669543 454545998464513901273504315)
        ·
          refine ⟨681818997696770851910256473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454545998464513901273504315 681818997696770851910256473)
          ·
            refine ⟨511364248272578138932692355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681818997696770851910256473 511364248272578138932692355)
            ·
              refine ⟨767046372408867208399038533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511364248272578138932692355 767046372408867208399038533)
              ·
                refine ⟨143821194826662601574819725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 767046372408867208399038533 143821194826662601574819725)
                ·
                  refine ⟨53932948059998475590557397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143821194826662601574819725 53932948059998475590557397)
                  ·
                    refine ⟨1264053470156214271653689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53932948059998475590557397 1264053470156214271653689)
                    ·
                      rfl

theorem cell22_3692603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_3692603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692603 prefixEnd_3692603 := by exact prefixLift 3692603
  have htrace : WordTrace (prefixWord ++ tailWord_3692603) baseStart_3692603 baseEnd_3692603 := by
    simpa [prefixWord, tailWord_3692603, baseEnd_3692603] using wordTrace_append hprefix tailTrace_3692603
  have hstable : (prefixWord ++ tailWord_3692603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692603).length < 2 ^ (prefixWord ++ tailWord_3692603).sum := by decide
  have hdescent : baseEnd_3692603 < baseStart_3692603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692605 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 7]
def baseStart_3692605 : Nat := 118140960795 + 3692605 * 2 ^ 59
def prefixEnd_3692605 : Nat := 4983230072969 + 3 ^ 40 * 3692605 * 2
def baseEnd_3692605 : Nat := 421351384932362311034561

theorem tailTrace_3692605 : CollatzResearch.WordTrace tailWord_3692605 prefixEnd_3692605 421351384932362311034561 := by
  unfold tailWord_3692605
  simp only [CollatzResearch.WordTrace]
  refine ⟨134680368787330206570759269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89786912524886804380506179 134680368787330206570759269)
  ·
    refine ⟨25252569147624413732017363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134680368787330206570759269 25252569147624413732017363)
    ·
      refine ⟨37878853721436620598026045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25252569147624413732017363 37878853721436620598026045)
      ·
        refine ⟨14204570145538732724259767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37878853721436620598026045 14204570145538732724259767)
        ·
          refine ⟨21306855218308099086389651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14204570145538732724259767 21306855218308099086389651)
          ·
            refine ⟨31960282827462148629584477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21306855218308099086389651 31960282827462148629584477)
            ·
              refine ⟨11985106060298305736094179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31960282827462148629584477 11985106060298305736094179)
              ·
                refine ⟨17977659090447458604141269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11985106060298305736094179 17977659090447458604141269)
                ·
                  refine ⟨421351384932362311034561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17977659090447458604141269 421351384932362311034561)
                  ·
                    rfl

theorem cell22_3692605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_3692605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692605 prefixEnd_3692605 := by exact prefixLift 3692605
  have htrace : WordTrace (prefixWord ++ tailWord_3692605) baseStart_3692605 baseEnd_3692605 := by
    simpa [prefixWord, tailWord_3692605, baseEnd_3692605] using wordTrace_append hprefix tailTrace_3692605
  have hstable : (prefixWord ++ tailWord_3692605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692605).length < 2 ^ (prefixWord ++ tailWord_3692605).sum := by decide
  have hdescent : baseEnd_3692605 < baseStart_3692605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692609 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 3, 3]
def baseStart_3692609 : Nat := 118140960795 + 3692609 * 2 ^ 59
def prefixEnd_3692609 : Nat := 4983230072969 + 3 ^ 40 * 3692609 * 2
def baseEnd_3692609 : Nat := 1264055524078832256003671

theorem tailTrace_3692609 : CollatzResearch.WordTrace tailWord_3692609 prefixEnd_3692609 1264055524078832256003671 := by
  unfold tailWord_3692609
  simp only [CollatzResearch.WordTrace]
  refine ⟨134680514679315715253904881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89787009786210476835936587 134680514679315715253904881)
  ·
    refine ⟨101010386009486786440428661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134680514679315715253904881 101010386009486786440428661)
    ·
      refine ⟨9469723688389386228790187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101010386009486786440428661 9469723688389386228790187)
      ·
        refine ⟨14204585532584079343185281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9469723688389386228790187 14204585532584079343185281)
        ·
          refine ⟨10653439149438059507388961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14204585532584079343185281 10653439149438059507388961)
          ·
            refine ⟨7990079362078544630541721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10653439149438059507388961 7990079362078544630541721)
            ·
              refine ⟨5992559521558908472906291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7990079362078544630541721 5992559521558908472906291)
              ·
                refine ⟨8988839282338362709359437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5992559521558908472906291 8988839282338362709359437)
                ·
                  refine ⟨3370814730876886016009789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8988839282338362709359437 3370814730876886016009789)
                  ·
                    refine ⟨1264055524078832256003671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3370814730876886016009789 1264055524078832256003671)
                    ·
                      rfl

theorem cell22_3692609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_3692609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692609 prefixEnd_3692609 := by exact prefixLift 3692609
  have htrace : WordTrace (prefixWord ++ tailWord_3692609) baseStart_3692609 baseEnd_3692609 := by
    simpa [prefixWord, tailWord_3692609, baseEnd_3692609] using wordTrace_append hprefix tailTrace_3692609
  have hstable : (prefixWord ++ tailWord_3692609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692609).length < 2 ^ (prefixWord ++ tailWord_3692609).sum := by decide
  have hdescent : baseEnd_3692609 < baseStart_3692609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692620 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_3692620 : Nat := 118140960795 + 3692620 * 2 ^ 59
def prefixEnd_3692620 : Nat := 4983230072969 + 3 ^ 40 * 3692620 * 2
def baseEnd_3692620 : Nat := 1264059289603631893978637

theorem tailTrace_3692620 : CollatzResearch.WordTrace tailWord_3692620 prefixEnd_3692620 1264059289603631893978637 := by
  unfold tailWord_3692620
  simp only [CollatzResearch.WordTrace]
  refine ⟨67340457941137932066277657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89787277254850576088370209 67340457941137932066277657)
  ·
    refine ⟨50505343455853449049708243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67340457941137932066277657 50505343455853449049708243)
    ·
      refine ⟨75758015183780173574562365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50505343455853449049708243 75758015183780173574562365)
      ·
        refine ⟨28409255693917565090460887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75758015183780173574562365 28409255693917565090460887)
        ·
          refine ⟨42613883540876347635691331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28409255693917565090460887 42613883540876347635691331)
          ·
            refine ⟨63920825311314521453536997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42613883540876347635691331 63920825311314521453536997)
            ·
              refine ⟨11985154745871472772538187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63920825311314521453536997 11985154745871472772538187)
              ·
                refine ⟨17977732118807209158807281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11985154745871472772538187 17977732118807209158807281)
                ·
                  refine ⟨13483299089105406869105461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17977732118807209158807281 13483299089105406869105461)
                  ·
                    refine ⟨1264059289603631893978637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13483299089105406869105461 1264059289603631893978637)
                    ·
                      rfl

theorem cell22_3692620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_3692620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692620 prefixEnd_3692620 := by exact prefixLift 3692620
  have htrace : WordTrace (prefixWord ++ tailWord_3692620) baseStart_3692620 baseEnd_3692620 := by
    simpa [prefixWord, tailWord_3692620, baseEnd_3692620] using wordTrace_append hprefix tailTrace_3692620
  have hstable : (prefixWord ++ tailWord_3692620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692620).length < 2 ^ (prefixWord ++ tailWord_3692620).sum := by decide
  have hdescent : baseEnd_3692620 < baseStart_3692620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692652 : List Nat := [2, 2, 1, 1, 3, 3, 2, 3, 1, 4]
def baseStart_3692652 : Nat := 118140960795 + 3692652 * 2 ^ 59
def prefixEnd_3692652 : Nat := 4983230072969 + 3 ^ 40 * 3692652 * 2
def baseEnd_3692652 : Nat := 1264070243857594477178539

theorem tailTrace_3692652 : CollatzResearch.WordTrace tailWord_3692652 prefixEnd_3692652 1264070243857594477178539 := by
  unfold tailWord_3692652
  simp only [CollatzResearch.WordTrace]
  refine ⟨67341041509079966798860105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89788055345439955731813473 67341041509079966798860105)
  ·
    refine ⟨50505781131809975099145079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67341041509079966798860105 50505781131809975099145079)
    ·
      refine ⟨75758671697714962648717619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50505781131809975099145079 75758671697714962648717619)
      ·
        refine ⟨113638007546572443973076429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75758671697714962648717619 113638007546572443973076429)
        ·
          refine ⟨42614252829964666489903661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113638007546572443973076429 42614252829964666489903661)
          ·
            refine ⟨15980344811236749933713873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42614252829964666489903661 15980344811236749933713873)
            ·
              refine ⟨11985258608427562450285405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15980344811236749933713873 11985258608427562450285405)
              ·
                refine ⟨4494471978160335918857027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11985258608427562450285405 4494471978160335918857027)
                ·
                  refine ⟨6741707967240503878285541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4494471978160335918857027 6741707967240503878285541)
                  ·
                    refine ⟨1264070243857594477178539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6741707967240503878285541 1264070243857594477178539)
                    ·
                      rfl

theorem cell22_3692652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_3692652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692652 prefixEnd_3692652 := by exact prefixLift 3692652
  have htrace : WordTrace (prefixWord ++ tailWord_3692652) baseStart_3692652 baseEnd_3692652 := by
    simpa [prefixWord, tailWord_3692652, baseEnd_3692652] using wordTrace_append hprefix tailTrace_3692652
  have hstable : (prefixWord ++ tailWord_3692652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692652).length < 2 ^ (prefixWord ++ tailWord_3692652).sum := by decide
  have hdescent : baseEnd_3692652 < baseStart_3692652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692686 : List Nat := [4, 1, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_3692686 : Nat := 118140960795 + 3692686 * 2 ^ 59
def prefixEnd_3692686 : Nat := 4983230072969 + 3 ^ 40 * 3692686 * 2
def baseEnd_3692686 : Nat := 1264081882752429721828435

theorem tailTrace_3692686 : CollatzResearch.WordTrace tailWord_3692686 prefixEnd_3692686 1264081882752429721828435 := by
  unfold tailWord_3692686
  simp only [CollatzResearch.WordTrace]
  refine ⟨16835415387504594675557239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89788882066691171602971941 16835415387504594675557239)
  ·
    refine ⟨25253123081256892013335859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16835415387504594675557239 25253123081256892013335859)
    ·
      refine ⟨37879684621885338020003789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25253123081256892013335859 37879684621885338020003789)
      ·
        refine ⟨14204881733207001757501421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37879684621885338020003789 14204881733207001757501421)
        ·
          refine ⟨5326830649952625659063033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14204881733207001757501421 5326830649952625659063033)
          ·
            refine ⟨3995122987464469244297275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5326830649952625659063033 3995122987464469244297275)
            ·
              refine ⟨5992684481196703866445913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3995122987464469244297275 5992684481196703866445913)
              ·
                refine ⟨4494513360897527899834435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5992684481196703866445913 4494513360897527899834435)
                ·
                  refine ⟨6741770041346291849751653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4494513360897527899834435 6741770041346291849751653)
                  ·
                    refine ⟨1264081882752429721828435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6741770041346291849751653 1264081882752429721828435)
                    ·
                      rfl

theorem cell22_3692686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_3692686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692686 prefixEnd_3692686 := by exact prefixLift 3692686
  have htrace : WordTrace (prefixWord ++ tailWord_3692686) baseStart_3692686 baseEnd_3692686 := by
    simpa [prefixWord, tailWord_3692686, baseEnd_3692686] using wordTrace_append hprefix tailTrace_3692686
  have hstable : (prefixWord ++ tailWord_3692686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692686).length < 2 ^ (prefixWord ++ tailWord_3692686).sum := by decide
  have hdescent : baseEnd_3692686 < baseStart_3692686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692718 : List Nat := [4, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_3692718 : Nat := 118140960795 + 3692718 * 2 ^ 59
def prefixEnd_3692718 : Nat := 4983230072969 + 3 ^ 40 * 3692718 * 2
def baseEnd_3692718 : Nat := 421364279002130768342779

theorem tailTrace_3692718 : CollatzResearch.WordTrace tailWord_3692718 prefixEnd_3692718 421364279002130768342779 := by
  unfold tailWord_3692718
  simp only [CollatzResearch.WordTrace]
  refine ⟨16835561279490103358702851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89789660157280551246415205 16835561279490103358702851)
  ·
    refine ⟨25253341919235155038054277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16835561279490103358702851 25253341919235155038054277)
    ·
      refine ⟨4735001609856591569635177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25253341919235155038054277 4735001609856591569635177)
      ·
        refine ⟨3551251207392443677226383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4735001609856591569635177 3551251207392443677226383)
        ·
          refine ⟨5326876811088665515839575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3551251207392443677226383 5326876811088665515839575)
          ·
            refine ⟨7990315216632998273759363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5326876811088665515839575 7990315216632998273759363)
            ·
              refine ⟨11985472824949497410639045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7990315216632998273759363 11985472824949497410639045)
              ·
                refine ⟨2247276154678030764494821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11985472824949497410639045 2247276154678030764494821)
                ·
                  refine ⟨421364279002130768342779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247276154678030764494821 421364279002130768342779)
                  ·
                    rfl

theorem cell22_3692718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_3692718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692718 prefixEnd_3692718 := by exact prefixLift 3692718
  have htrace : WordTrace (prefixWord ++ tailWord_3692718) baseStart_3692718 baseEnd_3692718 := by
    simpa [prefixWord, tailWord_3692718, baseEnd_3692718] using wordTrace_append hprefix tailTrace_3692718
  have hstable : (prefixWord ++ tailWord_3692718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692718).length < 2 ^ (prefixWord ++ tailWord_3692718).sum := by decide
  have hdescent : baseEnd_3692718 < baseStart_3692718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692748 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 2, 4]
def baseStart_3692748 : Nat := 118140960795 + 3692748 * 2 ^ 59
def prefixEnd_3692748 : Nat := 4983230072969 + 3 ^ 40 * 3692748 * 2
def baseEnd_3692748 : Nat := 1264103106619482226778245

theorem tailTrace_3692748 : CollatzResearch.WordTrace tailWord_3692748 prefixEnd_3692748 1264103106619482226778245 := by
  unfold tailWord_3692748
  simp only [CollatzResearch.WordTrace]
  refine ⟨67342792212906070996607449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89790389617208094662143265 67342792212906070996607449)
  ·
    refine ⟨50507094159679553247455587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67342792212906070996607449 50507094159679553247455587)
    ·
      refine ⟨75760641239519329871183381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50507094159679553247455587 75760641239519329871183381)
      ·
        refine ⟨3551280058102468587711721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75760641239519329871183381 3551280058102468587711721)
        ·
          refine ⟨2663460043576851440783791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3551280058102468587711721 2663460043576851440783791)
          ·
            refine ⟨3995190065365277161175687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663460043576851440783791 3995190065365277161175687)
            ·
              refine ⟨5992785098047915741763531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3995190065365277161175687 5992785098047915741763531)
              ·
                refine ⟨8989177647071873612645297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5992785098047915741763531 8989177647071873612645297)
                ·
                  refine ⟨6741883235303905209483973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8989177647071873612645297 6741883235303905209483973)
                  ·
                    refine ⟨1264103106619482226778245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6741883235303905209483973 1264103106619482226778245)
                    ·
                      rfl

theorem cell22_3692748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_3692748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692748 prefixEnd_3692748 := by exact prefixLift 3692748
  have htrace : WordTrace (prefixWord ++ tailWord_3692748) baseStart_3692748 baseEnd_3692748 := by
    simpa [prefixWord, tailWord_3692748, baseEnd_3692748] using wordTrace_append hprefix tailTrace_3692748
  have hstable : (prefixWord ++ tailWord_3692748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692748).length < 2 ^ (prefixWord ++ tailWord_3692748).sum := by decide
  have hdescent : baseEnd_3692748 < baseStart_3692748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692755 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 6, 5]
def baseStart_3692755 : Nat := 118140960795 + 3692755 * 2 ^ 59
def prefixEnd_3692755 : Nat := 4983230072969 + 3 ^ 40 * 3692755 * 2
def baseEnd_3692755 : Nat := 1264105502862536541853223

theorem tailTrace_3692755 : CollatzResearch.WordTrace tailWord_3692755 prefixEnd_3692755 1264105502862536541853223 := by
  unfold tailWord_3692755
  simp only [CollatzResearch.WordTrace]
  refine ⟨134685839736786782188719719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89790559824524521459146479 134685839736786782188719719)
  ·
    refine ⟨202028759605180173283079579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134685839736786782188719719 202028759605180173283079579)
    ·
      refine ⟨303043139407770259924619369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202028759605180173283079579 303043139407770259924619369)
      ·
        refine ⟨227282354555827694943464527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303043139407770259924619369 227282354555827694943464527)
        ·
          refine ⟨340923531833741542415196791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227282354555827694943464527 340923531833741542415196791)
          ·
            refine ⟨511385297750612313622795187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340923531833741542415196791 511385297750612313622795187)
            ·
              refine ⟨767077946625918470434192781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511385297750612313622795187 767077946625918470434192781)
              ·
                refine ⟨287654229984719426412822293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 767077946625918470434192781 287654229984719426412822293)
                ·
                  refine ⟨13483792030533723113101045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 287654229984719426412822293 13483792030533723113101045)
                  ·
                    refine ⟨1264105502862536541853223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13483792030533723113101045 1264105502862536541853223)
                    ·
                      rfl

theorem cell22_3692755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 5].length) (baseStart_3692755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692755 prefixEnd_3692755 := by exact prefixLift 3692755
  have htrace : WordTrace (prefixWord ++ tailWord_3692755) baseStart_3692755 baseEnd_3692755 := by
    simpa [prefixWord, tailWord_3692755, baseEnd_3692755] using wordTrace_append hprefix tailTrace_3692755
  have hstable : (prefixWord ++ tailWord_3692755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692755).length < 2 ^ (prefixWord ++ tailWord_3692755).sum := by decide
  have hdescent : baseEnd_3692755 < baseStart_3692755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692907 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 2, 5]
def baseStart_3692907 : Nat := 118140960795 + 3692907 * 2 ^ 59
def prefixEnd_3692907 : Nat := 4983230072969 + 3 ^ 40 * 3692907 * 2
def baseEnd_3692907 : Nat := 1264157535568858812052757

theorem tailTrace_3692907 : CollatzResearch.WordTrace tailWord_3692907 prefixEnd_3692907 1264157535568858812052757 := by
  unfold tailWord_3692907
  simp only [CollatzResearch.WordTrace]
  refine ⟨134691383632236112148252975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89794255754824074765501983 134691383632236112148252975)
  ·
    refine ⟨202037075448354168222379463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134691383632236112148252975 202037075448354168222379463)
    ·
      refine ⟨303055613172531252333569195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202037075448354168222379463 303055613172531252333569195)
      ·
        refine ⟨454583419758796878500353793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303055613172531252333569195 454583419758796878500353793)
        ·
          refine ⟨340937564819097658875265345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454583419758796878500353793 340937564819097658875265345)
          ·
            refine ⟨255703173614323244156449009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340937564819097658875265345 255703173614323244156449009)
            ·
              refine ⟨191777380210742433117336757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255703173614323244156449009 191777380210742433117336757)
              ·
                refine ⟨17979129394757103104750321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191777380210742433117336757 17979129394757103104750321)
                ·
                  refine ⟨13484347046067827328562741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17979129394757103104750321 13484347046067827328562741)
                  ·
                    refine ⟨1264157535568858812052757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13484347046067827328562741 1264157535568858812052757)
                    ·
                      rfl

theorem cell22_3692907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 5].length) (baseStart_3692907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692907 prefixEnd_3692907 := by exact prefixLift 3692907
  have htrace : WordTrace (prefixWord ++ tailWord_3692907) baseStart_3692907 baseEnd_3692907 := by
    simpa [prefixWord, tailWord_3692907, baseEnd_3692907] using wordTrace_append hprefix tailTrace_3692907
  have hstable : (prefixWord ++ tailWord_3692907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692907).length < 2 ^ (prefixWord ++ tailWord_3692907).sum := by decide
  have hdescent : baseEnd_3692907 < baseStart_3692907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692909 : List Nat := [1, 5, 1, 1, 1, 2, 1, 5, 5]
def baseStart_3692909 : Nat := 118140960795 + 3692909 * 2 ^ 59
def prefixEnd_3692909 : Nat := 4983230072969 + 3 ^ 40 * 3692909 * 2
def baseEnd_3692909 : Nat := 421386073403243824500917

theorem tailTrace_3692909 : CollatzResearch.WordTrace tailWord_3692909 prefixEnd_3692909 421386073403243824500917 := by
  unfold tailWord_3692909
  simp only [CollatzResearch.WordTrace]
  refine ⟨134691456578228866489825781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89794304385485910993217187 134691456578228866489825781)
  ·
    refine ⟨12627324054208956233421167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134691456578228866489825781 12627324054208956233421167)
    ·
      refine ⟨18940986081313434350131751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12627324054208956233421167 18940986081313434350131751)
      ·
        refine ⟨28411479121970151525197627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18940986081313434350131751 28411479121970151525197627)
        ·
          refine ⟨42617218682955227287796441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28411479121970151525197627 42617218682955227287796441)
          ·
            refine ⟨31962914012216420465847331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42617218682955227287796441 31962914012216420465847331)
            ·
              refine ⟨47944371018324630698770997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31962914012216420465847331 47944371018324630698770997)
              ·
                refine ⟨4494784782967934128009781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47944371018324630698770997 4494784782967934128009781)
                ·
                  refine ⟨421386073403243824500917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4494784782967934128009781 421386073403243824500917)
                  ·
                    rfl

theorem cell22_3692909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_3692909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692909 prefixEnd_3692909 := by exact prefixLift 3692909
  have htrace : WordTrace (prefixWord ++ tailWord_3692909) baseStart_3692909 baseEnd_3692909 := by
    simpa [prefixWord, tailWord_3692909, baseEnd_3692909] using wordTrace_append hprefix tailTrace_3692909
  have hstable : (prefixWord ++ tailWord_3692909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692909).length < 2 ^ (prefixWord ++ tailWord_3692909).sum := by decide
  have hdescent : baseEnd_3692909 < baseStart_3692909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692954 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 6]
def baseStart_3692954 : Nat := 118140960795 + 3692954 * 2 ^ 59
def prefixEnd_3692954 : Nat := 4983230072969 + 3 ^ 40 * 3692954 * 2
def baseEnd_3692954 : Nat := 421391208209788785375871

theorem tailTrace_3692954 : CollatzResearch.WordTrace tailWord_3692954 prefixEnd_3692954 421391208209788785375871 := by
  unfold tailWord_3692954
  simp only [CollatzResearch.WordTrace]
  refine ⟨33673274465766459793803479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89795398575377226116809277 33673274465766459793803479)
  ·
    refine ⟨50509911698649689690705219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33673274465766459793803479 50509911698649689690705219)
    ·
      refine ⟨75764867547974534536057829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50509911698649689690705219 75764867547974534536057829)
      ·
        refine ⟨14205912665245225225510843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75764867547974534536057829 14205912665245225225510843)
        ·
          refine ⟨21308868997867837838266265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14205912665245225225510843 21308868997867837838266265)
          ·
            refine ⟨15981651748400878378699699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21308868997867837838266265 15981651748400878378699699)
            ·
              refine ⟨23972477622601317568049549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15981651748400878378699699 23972477622601317568049549)
              ·
                refine ⟨8989679108475494088018581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23972477622601317568049549 8989679108475494088018581)
                ·
                  refine ⟨421391208209788785375871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8989679108475494088018581 421391208209788785375871)
                  ·
                    rfl

theorem cell22_3692954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_3692954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692954 prefixEnd_3692954 := by exact prefixLift 3692954
  have htrace : WordTrace (prefixWord ++ tailWord_3692954) baseStart_3692954 baseEnd_3692954 := by
    simpa [prefixWord, tailWord_3692954, baseEnd_3692954] using wordTrace_append hprefix tailTrace_3692954
  have hstable : (prefixWord ++ tailWord_3692954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692954).length < 2 ^ (prefixWord ++ tailWord_3692954).sum := by decide
  have hdescent : baseEnd_3692954 < baseStart_3692954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692984 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 2, 4]
def baseStart_3692984 : Nat := 118140960795 + 3692984 * 2 ^ 59
def prefixEnd_3692984 : Nat := 4983230072969 + 3 ^ 40 * 3692984 * 2
def baseEnd_3692984 : Nat := 1264183894242456277877521

theorem tailTrace_3692984 : CollatzResearch.WordTrace tailWord_3692984 prefixEnd_3692984 1264183894242456277877521 := by
  unfold tailWord_3692984
  simp only [CollatzResearch.WordTrace]
  refine ⟨67347096026478577149403003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89796128035304769532537337 67347096026478577149403003)
  ·
    refine ⟨101020644039717865724104505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67347096026478577149403003 101020644039717865724104505)
    ·
      refine ⟨75765483029788399293078379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101020644039717865724104505 75765483029788399293078379)
      ·
        refine ⟨113648224544682598939617569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75765483029788399293078379 113648224544682598939617569)
        ·
          refine ⟨85236168408511949204713177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113648224544682598939617569 85236168408511949204713177)
          ·
            refine ⟨63927126306383961903534883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85236168408511949204713177 63927126306383961903534883)
            ·
              refine ⟨95890689459575942855302325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63927126306383961903534883 95890689459575942855302325)
              ·
                refine ⟨8989752136835244642684593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95890689459575942855302325 8989752136835244642684593)
                ·
                  refine ⟨6742314102626433482013445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8989752136835244642684593 6742314102626433482013445)
                  ·
                    refine ⟨1264183894242456277877521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6742314102626433482013445 1264183894242456277877521)
                    ·
                      rfl

theorem cell22_3692984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_3692984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692984 prefixEnd_3692984 := by exact prefixLift 3692984
  have htrace : WordTrace (prefixWord ++ tailWord_3692984) baseStart_3692984 baseEnd_3692984 := by
    simpa [prefixWord, tailWord_3692984, baseEnd_3692984] using wordTrace_append hprefix tailTrace_3692984
  have hstable : (prefixWord ++ tailWord_3692984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692984).length < 2 ^ (prefixWord ++ tailWord_3692984).sum := by decide
  have hdescent : baseEnd_3692984 < baseStart_3692984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692988 : List Nat := [2, 2, 2, 4, 1, 1, 3, 3, 4]
def baseStart_3692988 : Nat := 118140960795 + 3692988 * 2 ^ 59
def prefixEnd_3692988 : Nat := 4983230072969 + 3 ^ 40 * 3692988 * 2
def baseEnd_3692988 : Nat := 421395087841400533592503

theorem tailTrace_3692988 : CollatzResearch.WordTrace tailWord_3692988 prefixEnd_3692988 421395087841400533592503 := by
  unfold tailWord_3692988
  simp only [CollatzResearch.WordTrace]
  refine ⟨67347168972471331490975809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89796225296628441987967745 67347168972471331490975809)
  ·
    refine ⟨50510376729353498618231857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67347168972471331490975809 50510376729353498618231857)
    ·
      refine ⟨37882782547015123963673893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50510376729353498618231857 37882782547015123963673893)
      ·
        refine ⟨7103021727565335743188855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37882782547015123963673893 7103021727565335743188855)
        ·
          refine ⟨10654532591348003614783283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7103021727565335743188855 10654532591348003614783283)
          ·
            refine ⟨15981798887022005422174925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10654532591348003614783283 15981798887022005422174925)
            ·
              refine ⟨5993174582633252033315597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15981798887022005422174925 5993174582633252033315597)
              ·
                refine ⟨2247440468487469512493349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5993174582633252033315597 2247440468487469512493349)
                ·
                  refine ⟨421395087841400533592503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247440468487469512493349 421395087841400533592503)
                  ·
                    rfl

theorem cell22_3692988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_3692988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692988 prefixEnd_3692988 := by exact prefixLift 3692988
  have htrace : WordTrace (prefixWord ++ tailWord_3692988) baseStart_3692988 baseEnd_3692988 := by
    simpa [prefixWord, tailWord_3692988, baseEnd_3692988] using wordTrace_append hprefix tailTrace_3692988
  have hstable : (prefixWord ++ tailWord_3692988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692988).length < 2 ^ (prefixWord ++ tailWord_3692988).sum := by decide
  have hdescent : baseEnd_3692988 < baseStart_3692988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3692999 : List Nat := [1, 1, 4, 1, 1, 6, 8]
def baseStart_3692999 : Nat := 118140960795 + 3692999 * 2 ^ 59
def prefixEnd_3692999 : Nat := 4983230072969 + 3 ^ 40 * 3692999 * 2
def baseEnd_3692999 : Nat := 46821815890703749583425

theorem tailTrace_3692999 : CollatzResearch.WordTrace tailWord_3692999 prefixEnd_3692999 46821815890703749583425 := by
  unfold tailWord_3692999
  simp only [CollatzResearch.WordTrace]
  refine ⟨134694739147902811860602051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89796492765268541240401367 134694739147902811860602051)
  ·
    refine ⟨202042108721854217790903077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134694739147902811860602051 202042108721854217790903077)
    ·
      refine ⟨37882895385347665835794327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202042108721854217790903077 37882895385347665835794327)
      ·
        refine ⟨56824343078021498753691491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37882895385347665835794327 56824343078021498753691491)
        ·
          refine ⟨85236514617032248130537237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56824343078021498753691491 85236514617032248130537237)
          ·
            refine ⟨3995461622673386631118933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85236514617032248130537237 3995461622673386631118933)
            ·
              refine ⟨46821815890703749583425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3995461622673386631118933 46821815890703749583425)
              ·
                rfl

theorem cell22_3692999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 8].length) (baseStart_3692999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3692999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3692999 prefixEnd_3692999 := by exact prefixLift 3692999
  have htrace : WordTrace (prefixWord ++ tailWord_3692999) baseStart_3692999 baseEnd_3692999 := by
    simpa [prefixWord, tailWord_3692999, baseEnd_3692999] using wordTrace_append hprefix tailTrace_3692999
  have hstable : (prefixWord ++ tailWord_3692999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3692999).length < 2 ^ (prefixWord ++ tailWord_3692999).sum := by decide
  have hdescent : baseEnd_3692999 < baseStart_3692999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3692999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693031 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 5, 3]
def baseStart_3693031 : Nat := 118140960795 + 3693031 * 2 ^ 59
def prefixEnd_3693031 : Nat := 4983230072969 + 3 ^ 40 * 3693031 * 2
def baseEnd_3693031 : Nat := 1264199983302963821952377

theorem tailTrace_3693031 : CollatzResearch.WordTrace tailWord_3693031 prefixEnd_3693031 1264199983302963821952377 := by
  unfold tailWord_3693031
  simp only [CollatzResearch.WordTrace]
  refine ⟨134695906283786881325766947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89797270855857920883844631 134695906283786881325766947)
  ·
    refine ⟨202043859425680321988650421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134695906283786881325766947 202043859425680321988650421)
    ·
      refine ⟨18941611821157530186435977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202043859425680321988650421 18941611821157530186435977)
      ·
        refine ⟨14206208865868147639826983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18941611821157530186435977 14206208865868147639826983)
        ·
          refine ⟨21309313298802221459740475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14206208865868147639826983 21309313298802221459740475)
          ·
            refine ⟨31963969948203332189610713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21309313298802221459740475 31963969948203332189610713)
            ·
              refine ⟨23972977461152499142208035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31963969948203332189610713 23972977461152499142208035)
              ·
                refine ⟨35959466191728748713312053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23972977461152499142208035 35959466191728748713312053)
                ·
                  refine ⟨3371199955474570191873005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35959466191728748713312053 3371199955474570191873005)
                  ·
                    refine ⟨1264199983302963821952377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3371199955474570191873005 1264199983302963821952377)
                    ·
                      rfl

theorem cell22_3693031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_3693031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693031 prefixEnd_3693031 := by exact prefixLift 3693031
  have htrace : WordTrace (prefixWord ++ tailWord_3693031) baseStart_3693031 baseEnd_3693031 := by
    simpa [prefixWord, tailWord_3693031, baseEnd_3693031] using wordTrace_append hprefix tailTrace_3693031
  have hstable : (prefixWord ++ tailWord_3693031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693031).length < 2 ^ (prefixWord ++ tailWord_3693031).sum := by decide
  have hdescent : baseEnd_3693031 < baseStart_3693031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693048 : List Nat := [2, 1, 2, 1, 1, 4, 2, 5, 1, 3]
def baseStart_3693048 : Nat := 118140960795 + 3693048 * 2 ^ 59
def prefixEnd_3693048 : Nat := 4983230072969 + 3 ^ 40 * 3693048 * 2
def baseEnd_3693048 : Nat := 1264205802750381444277325

theorem tailTrace_3693048 : CollatzResearch.WordTrace tailWord_3693048 prefixEnd_3693048 1264205802750381444277325 := by
  unfold tailWord_3693048
  simp only [CollatzResearch.WordTrace]
  refine ⟨67348263162362646614567899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89797684216483528819423865 67348263162362646614567899)
  ·
    refine ⟨101022394743543969921851849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67348263162362646614567899 101022394743543969921851849)
    ·
      refine ⟨75766796057657977441388887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101022394743543969921851849 75766796057657977441388887)
      ·
        refine ⟨113650194086486966162083331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75766796057657977441388887 113650194086486966162083331)
        ·
          refine ⟨170475291129730449243124997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113650194086486966162083331 170475291129730449243124997)
          ·
            refine ⟨31964117086824459233085937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170475291129730449243124997 31964117086824459233085937)
            ·
              refine ⟨23973087815118344424814453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31964117086824459233085937 23973087815118344424814453)
              ·
                refine ⟨2247476982667344789826355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23973087815118344424814453 2247476982667344789826355)
                ·
                  refine ⟨3371215474001017184739533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247476982667344789826355 3371215474001017184739533)
                  ·
                    refine ⟨1264205802750381444277325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3371215474001017184739533 1264205802750381444277325)
                    ·
                      rfl

theorem cell22_3693048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_3693048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693048 prefixEnd_3693048 := by exact prefixLift 3693048
  have htrace : WordTrace (prefixWord ++ tailWord_3693048) baseStart_3693048 baseEnd_3693048 := by
    simpa [prefixWord, tailWord_3693048, baseEnd_3693048] using wordTrace_append hprefix tailTrace_3693048
  have hstable : (prefixWord ++ tailWord_3693048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693048).length < 2 ^ (prefixWord ++ tailWord_3693048).sum := by decide
  have hdescent : baseEnd_3693048 < baseStart_3693048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693059 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 2, 5]
def baseStart_3693059 : Nat := 118140960795 + 3693059 * 2 ^ 59
def prefixEnd_3693059 : Nat := 4983230072969 + 3 ^ 40 * 3693059 * 2
def baseEnd_3693059 : Nat := 1264209568275181082252291

theorem tailTrace_3693059 : CollatzResearch.WordTrace tailWord_3693059 prefixEnd_3693059 1264209568275181082252291 := by
  unfold tailWord_3693059
  simp only [CollatzResearch.WordTrace]
  refine ⟨134696927527685442107786231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89797951685123628071857487 134696927527685442107786231)
  ·
    refine ⟨202045391291528163161679347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134696927527685442107786231 202045391291528163161679347)
    ·
      refine ⟨303068086937292244742519021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202045391291528163161679347 303068086937292244742519021)
      ·
        refine ⟨113650532601484591778444633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303068086937292244742519021 113650532601484591778444633)
        ·
          refine ⟨85237899451113443833833475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113650532601484591778444633 85237899451113443833833475)
          ·
            refine ⟨127856849176670165750750213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85237899451113443833833475 127856849176670165750750213)
            ·
              refine ⟨23973159220625656078265665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127856849176670165750750213 23973159220625656078265665)
              ·
                refine ⟨17979869415469242058699249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23973159220625656078265665 17979869415469242058699249)
                ·
                  refine ⟨13484902061601931544024437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17979869415469242058699249 13484902061601931544024437)
                  ·
                    refine ⟨1264209568275181082252291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13484902061601931544024437 1264209568275181082252291)
                    ·
                      rfl

theorem cell22_3693059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 5].length) (baseStart_3693059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693059 prefixEnd_3693059 := by exact prefixLift 3693059
  have htrace : WordTrace (prefixWord ++ tailWord_3693059) baseStart_3693059 baseEnd_3693059 := by
    simpa [prefixWord, tailWord_3693059, baseEnd_3693059] using wordTrace_append hprefix tailTrace_3693059
  have hstable : (prefixWord ++ tailWord_3693059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693059).length < 2 ^ (prefixWord ++ tailWord_3693059).sum := by decide
  have hdescent : baseEnd_3693059 < baseStart_3693059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693091 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 3, 4]
def baseStart_3693091 : Nat := 118140960795 + 3693091 * 2 ^ 59
def prefixEnd_3693091 : Nat := 4983230072969 + 3 ^ 40 * 3693091 * 2
def baseEnd_3693091 : Nat := 1264220522529143665452193

theorem tailTrace_3693091 : CollatzResearch.WordTrace tailWord_3693091 prefixEnd_3693091 1264220522529143665452193 := by
  unfold tailWord_3693091
  simp only [CollatzResearch.WordTrace]
  refine ⟨134698094663569511572951127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89798729775713007715300751 134698094663569511572951127)
  ·
    refine ⟨202047141995354267359426691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134698094663569511572951127 202047141995354267359426691)
    ·
      refine ⟨303070712993031401039140037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202047141995354267359426691 303070712993031401039140037)
      ·
        refine ⟨56825758686193387694838757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303070712993031401039140037 56825758686193387694838757)
        ·
          refine ⟨10654829753661260192782267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56825758686193387694838757 10654829753661260192782267)
          ·
            refine ⟨15982244630491890289173401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10654829753661260192782267 15982244630491890289173401)
            ·
              refine ⟨11986683472868917716880051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15982244630491890289173401 11986683472868917716880051)
              ·
                refine ⟨17980025209303376575320077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11986683472868917716880051 17980025209303376575320077)
                ·
                  refine ⟨6742509453488766215745029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17980025209303376575320077 6742509453488766215745029)
                  ·
                    refine ⟨1264220522529143665452193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6742509453488766215745029 1264220522529143665452193)
                    ·
                      rfl

theorem cell22_3693091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 4].length) (baseStart_3693091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693091 prefixEnd_3693091 := by exact prefixLift 3693091
  have htrace : WordTrace (prefixWord ++ tailWord_3693091) baseStart_3693091 baseEnd_3693091 := by
    simpa [prefixWord, tailWord_3693091, baseEnd_3693091] using wordTrace_append hprefix tailTrace_3693091
  have hstable : (prefixWord ++ tailWord_3693091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693091).length < 2 ^ (prefixWord ++ tailWord_3693091).sum := by decide
  have hdescent : baseEnd_3693091 < baseStart_3693091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693157 : List Nat := [1, 3, 1, 3, 5, 1, 1, 3, 4]
def baseStart_3693157 : Nat := 118140960795 + 3693157 * 2 ^ 59
def prefixEnd_3693157 : Nat := 4983230072969 + 3 ^ 40 * 3693157 * 2
def baseEnd_3693157 : Nat := 421414371892647164433997

theorem tailTrace_3693157 : CollatzResearch.WordTrace tailWord_3693157 prefixEnd_3693157 421414371892647164433997 := by
  unfold tailWord_3693157
  simp only [CollatzResearch.WordTrace]
  refine ⟨134700501881330404844853725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89800334587553603229902483 134700501881330404844853725)
  ·
    refine ⟨50512688205498901816820147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134700501881330404844853725 50512688205498901816820147)
    ·
      refine ⟨75769032308248352725230221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50512688205498901816820147 75769032308248352725230221)
      ·
        refine ⟨28413387115593132271961333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75769032308248352725230221 28413387115593132271961333)
        ·
          refine ⟨2663755042086856150496375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28413387115593132271961333 2663755042086856150496375)
          ·
            refine ⟨3995632563130284225744563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663755042086856150496375 3995632563130284225744563)
            ·
              refine ⟨5993448844695426338616845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3995632563130284225744563 5993448844695426338616845)
              ·
                refine ⟨2247543316760784876981317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5993448844695426338616845 2247543316760784876981317)
                ·
                  refine ⟨421414371892647164433997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247543316760784876981317 421414371892647164433997)
                  ·
                    rfl

theorem cell22_3693157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_3693157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693157 prefixEnd_3693157 := by exact prefixLift 3693157
  have htrace : WordTrace (prefixWord ++ tailWord_3693157) baseStart_3693157 baseEnd_3693157 := by
    simpa [prefixWord, tailWord_3693157, baseEnd_3693157] using wordTrace_append hprefix tailTrace_3693157
  have hstable : (prefixWord ++ tailWord_3693157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693157).length < 2 ^ (prefixWord ++ tailWord_3693157).sum := by decide
  have hdescent : baseEnd_3693157 < baseStart_3693157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693168 : List Nat := [2, 1, 1, 1, 8, 1, 8]
def baseStart_3693168 : Nat := 118140960795 + 3693168 * 2 ^ 59
def prefixEnd_3693168 : Nat := 4983230072969 + 3 ^ 40 * 3693168 * 2
def baseEnd_3693168 : Nat := 46823958563064486343591

theorem tailTrace_3693168 : CollatzResearch.WordTrace tailWord_3693168 prefixEnd_3693168 46823958563064486343591 := by
  unfold tailWord_3693168
  simp only [CollatzResearch.WordTrace]
  refine ⟨67350451542145276861752079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89800602056193702482336105 67350451542145276861752079)
  ·
    refine ⟨101025677313217915292628119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67350451542145276861752079 101025677313217915292628119)
    ·
      refine ⟨151538515969826872938942179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101025677313217915292628119 151538515969826872938942179)
      ·
        refine ⟨227307773954740309408413269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151538515969826872938942179 227307773954740309408413269)
        ·
          refine ⟨2663762976032113000879843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 227307773954740309408413269 2663762976032113000879843)
          ·
            refine ⟨3995644464048169501319765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663762976032113000879843 3995644464048169501319765)
            ·
              refine ⟨46823958563064486343591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3995644464048169501319765 46823958563064486343591)
              ·
                rfl

theorem cell22_3693168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 8].length) (baseStart_3693168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693168 prefixEnd_3693168 := by exact prefixLift 3693168
  have htrace : WordTrace (prefixWord ++ tailWord_3693168) baseStart_3693168 baseEnd_3693168 := by
    simpa [prefixWord, tailWord_3693168, baseEnd_3693168] using wordTrace_append hprefix tailTrace_3693168
  have hstable : (prefixWord ++ tailWord_3693168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693168).length < 2 ^ (prefixWord ++ tailWord_3693168).sum := by decide
  have hdescent : baseEnd_3693168 < baseStart_3693168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693230 : List Nat := [4, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_3693230 : Nat := 118140960795 + 3693230 * 2 ^ 59
def prefixEnd_3693230 : Nat := 4983230072969 + 3 ^ 40 * 3693230 * 2
def baseEnd_3693230 : Nat := 421422701689931212075589

theorem tailTrace_3693230 : CollatzResearch.WordTrace tailWord_3693230 prefixEnd_3693230 421422701689931212075589 := by
  unfold tailWord_3693230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16837895551258242289032643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89802109606710625541507429 16837895551258242289032643)
  ·
    refine ⟨25256843326887363433548965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16837895551258242289032643 25256843326887363433548965)
    ·
      refine ⟨4735658123791380643790431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25256843326887363433548965 4735658123791380643790431)
      ·
        refine ⟨7103487185687070965685647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4735658123791380643790431 7103487185687070965685647)
        ·
          refine ⟨10655230778530606448528471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7103487185687070965685647 10655230778530606448528471)
          ·
            refine ⟨15982846167795909672792707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10655230778530606448528471 15982846167795909672792707)
            ·
              refine ⟨23974269251693864509189061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15982846167795909672792707 23974269251693864509189061)
              ·
                refine ⟨4495175484692599595472949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23974269251693864509189061 4495175484692599595472949)
                ·
                  refine ⟨421422701689931212075589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4495175484692599595472949 421422701689931212075589)
                  ·
                    rfl

theorem cell22_3693230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_3693230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693230 prefixEnd_3693230 := by exact prefixLift 3693230
  have htrace : WordTrace (prefixWord ++ tailWord_3693230) baseStart_3693230 baseEnd_3693230 := by
    simpa [prefixWord, tailWord_3693230, baseEnd_3693230] using wordTrace_append hprefix tailTrace_3693230
  have hstable : (prefixWord ++ tailWord_3693230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693230).length < 2 ^ (prefixWord ++ tailWord_3693230).sum := by decide
  have hdescent : baseEnd_3693230 < baseStart_3693230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693241 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 6]
def baseStart_3693241 : Nat := 118140960795 + 3693241 * 2 ^ 59
def prefixEnd_3693241 : Nat := 4983230072969 + 3 ^ 40 * 3693241 * 2
def baseEnd_3693241 : Nat := 421423956864864424733911

theorem tailTrace_3693241 : CollatzResearch.WordTrace tailWord_3693241 prefixEnd_3693241 421423956864864424733911 := by
  unfold tailWord_3693241
  simp only [CollatzResearch.WordTrace]
  refine ⟨134703565613026087190911577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89802377075350724793941051 134703565613026087190911577)
  ·
    refine ⟨101027674209769565393183683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134703565613026087190911577 101027674209769565393183683)
    ·
      refine ⟨151541511314654348089775525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101027674209769565393183683 151541511314654348089775525)
      ·
        refine ⟨28414033371497690266832911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151541511314654348089775525 28414033371497690266832911)
        ·
          refine ⟨42621050057246535400249367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28414033371497690266832911 42621050057246535400249367)
          ·
            refine ⟨63931575085869803100374051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42621050057246535400249367 63931575085869803100374051)
            ·
              refine ⟨95897362628804704650561077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63931575085869803100374051 95897362628804704650561077)
              ·
                refine ⟨8990377746450441060990101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95897362628804704650561077 8990377746450441060990101)
                ·
                  refine ⟨421423956864864424733911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8990377746450441060990101 421423956864864424733911)
                  ·
                    rfl

theorem cell22_3693241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 6].length) (baseStart_3693241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693241 prefixEnd_3693241 := by exact prefixLift 3693241
  have htrace : WordTrace (prefixWord ++ tailWord_3693241) baseStart_3693241 baseEnd_3693241 := by
    simpa [prefixWord, tailWord_3693241, baseEnd_3693241] using wordTrace_append hprefix tailTrace_3693241
  have hstable : (prefixWord ++ tailWord_3693241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693241).length < 2 ^ (prefixWord ++ tailWord_3693241).sum := by decide
  have hdescent : baseEnd_3693241 < baseStart_3693241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693258 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 6]
def baseStart_3693258 : Nat := 118140960795 + 3693258 * 2 ^ 59
def prefixEnd_3693258 : Nat := 4983230072969 + 3 ^ 40 * 3693258 * 2
def baseEnd_3693258 : Nat := 421425896680670298842227

theorem tailTrace_3693258 : CollatzResearch.WordTrace tailWord_3693258 prefixEnd_3693258 421425896680670298842227 := by
  unfold tailWord_3693258
  simp only [CollatzResearch.WordTrace]
  refine ⟨33676046413491124773570107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89802790435976332729520285 33676046413491124773570107)
  ·
    refine ⟨50514069620236687160355161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33676046413491124773570107 50514069620236687160355161)
    ·
      refine ⟨37885552215177515370266371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50514069620236687160355161 37885552215177515370266371)
      ·
        refine ⟨56828328322766273055399557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37885552215177515370266371 56828328322766273055399557)
        ·
          refine ⟨10655311560518676197887417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56828328322766273055399557 10655311560518676197887417)
          ·
            refine ⟨7991483670389007148415563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10655311560518676197887417 7991483670389007148415563)
            ·
              refine ⟨11987225505583510722623345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7991483670389007148415563 11987225505583510722623345)
              ·
                refine ⟨8990419129187633041967509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11987225505583510722623345 8990419129187633041967509)
                ·
                  refine ⟨421425896680670298842227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8990419129187633041967509 421425896680670298842227)
                  ·
                    rfl

theorem cell22_3693258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_3693258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693258 prefixEnd_3693258 := by exact prefixLift 3693258
  have htrace : WordTrace (prefixWord ++ tailWord_3693258) baseStart_3693258 baseEnd_3693258 := by
    simpa [prefixWord, tailWord_3693258, baseEnd_3693258] using wordTrace_append hprefix tailTrace_3693258
  have hstable : (prefixWord ++ tailWord_3693258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693258).length < 2 ^ (prefixWord ++ tailWord_3693258).sum := by decide
  have hdescent : baseEnd_3693258 < baseStart_3693258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693273 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 4, 3]
def baseStart_3693273 : Nat := 118140960795 + 3693273 * 2 ^ 59
def prefixEnd_3693273 : Nat := 4983230072969 + 3 ^ 40 * 3693273 * 2
def baseEnd_3693273 : Nat := 1264282824848555857401635

theorem tailTrace_3693273 : CollatzResearch.WordTrace tailWord_3693273 prefixEnd_3693273 1264282824848555857401635 := by
  unfold tailWord_3693273
  simp only [CollatzResearch.WordTrace]
  refine ⟨134704732748910156656076473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89803155165940104437384315 134704732748910156656076473)
  ·
    refine ⟨101028549561682617492057355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134704732748910156656076473 101028549561682617492057355)
    ·
      refine ⟨151542824342523926238086033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101028549561682617492057355 151542824342523926238086033)
      ·
        refine ⟨113657118256892944678564525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151542824342523926238086033 113657118256892944678564525)
        ·
          refine ⟨42621419346334854254461697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113657118256892944678564525 42621419346334854254461697)
          ·
            refine ⟨31966064509751140690846273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42621419346334854254461697 31966064509751140690846273)
            ·
              refine ⟨23974548382313355518134705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31966064509751140690846273 23974548382313355518134705)
              ·
                refine ⟨17980911286735016638601029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23974548382313355518134705 17980911286735016638601029)
                ·
                  refine ⟨3371420866262815619737693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17980911286735016638601029 3371420866262815619737693)
                  ·
                    refine ⟨1264282824848555857401635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3371420866262815619737693 1264282824848555857401635)
                    ·
                      rfl

theorem cell22_3693273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 3].length) (baseStart_3693273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693273 prefixEnd_3693273 := by exact prefixLift 3693273
  have htrace : WordTrace (prefixWord ++ tailWord_3693273) baseStart_3693273 baseEnd_3693273 := by
    simpa [prefixWord, tailWord_3693273, baseEnd_3693273] using wordTrace_append hprefix tailTrace_3693273
  have hstable : (prefixWord ++ tailWord_3693273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693273).length < 2 ^ (prefixWord ++ tailWord_3693273).sum := by decide
  have hdescent : baseEnd_3693273 < baseStart_3693273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693320 : List Nat := [2, 1, 3, 2, 2, 4, 2, 6]
def baseStart_3693320 : Nat := 118140960795 + 3693320 * 2 ^ 59
def prefixEnd_3693320 : Nat := 4983230072969 + 3 ^ 40 * 3693320 * 2
def baseEnd_3693320 : Nat := 140477657101007044608499

theorem tailTrace_3693320 : CollatzResearch.WordTrace tailWord_3693320 prefixEnd_3693320 140477657101007044608499 := by
  unfold tailWord_3693320
  simp only [CollatzResearch.WordTrace]
  refine ⟨67353223489869941841518707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89804297986493255788691609 67353223489869941841518707)
  ·
    refine ⟨101029835234804912762278061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67353223489869941841518707 101029835234804912762278061)
    ·
      refine ⟨37886188213051842285854273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101029835234804912762278061 37886188213051842285854273)
      ·
        refine ⟨28414641159788881714390705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37886188213051842285854273 28414641159788881714390705)
        ·
          refine ⟨21310980869841661285793029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28414641159788881714390705 21310980869841661285793029)
          ·
            refine ⟨3995808913095311491086193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21310980869841661285793029 3995808913095311491086193)
            ·
              refine ⟨2996856684821483618314645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3995808913095311491086193 2996856684821483618314645)
              ·
                refine ⟨140477657101007044608499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2996856684821483618314645 140477657101007044608499)
                ·
                  rfl

theorem cell22_3693320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 6].length) (baseStart_3693320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693320 prefixEnd_3693320 := by exact prefixLift 3693320
  have htrace : WordTrace (prefixWord ++ tailWord_3693320) baseStart_3693320 baseEnd_3693320 := by
    simpa [prefixWord, tailWord_3693320, baseEnd_3693320] using wordTrace_append hprefix tailTrace_3693320
  have hstable : (prefixWord ++ tailWord_3693320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693320).length < 2 ^ (prefixWord ++ tailWord_3693320).sum := by decide
  have hdescent : baseEnd_3693320 < baseStart_3693320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693331 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 9]
def baseStart_3693331 : Nat := 118140960795 + 3693331 * 2 ^ 59
def prefixEnd_3693331 : Nat := 4983230072969 + 3 ^ 40 * 3693331 * 2
def baseEnd_3693331 : Nat := 421434226477954346483819

theorem tailTrace_3693331 : CollatzResearch.WordTrace tailWord_3693331 prefixEnd_3693331 421434226477954346483819 := by
  unfold tailWord_3693331
  simp only [CollatzResearch.WordTrace]
  refine ⟨134706848182700032561687847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89804565455133355041125231 134706848182700032561687847)
  ·
    refine ⟨202060272274050048842531771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134706848182700032561687847 202060272274050048842531771)
    ·
      refine ⟨303090408411075073263797657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202060272274050048842531771 303090408411075073263797657)
      ·
        refine ⟨227317806308306304947848243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303090408411075073263797657 227317806308306304947848243)
        ·
          refine ⟨340976709462459457421772365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227317806308306304947848243 340976709462459457421772365)
          ·
            refine ⟨127866266048422296533164637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340976709462459457421772365 127866266048422296533164637)
            ·
              refine ⟨47949849768158361199936739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127866266048422296533164637 47949849768158361199936739)
              ·
                refine ⟨71924774652237541799905109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47949849768158361199936739 71924774652237541799905109)
                ·
                  refine ⟨421434226477954346483819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71924774652237541799905109 421434226477954346483819)
                  ·
                    rfl

theorem cell22_3693331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 9].length) (baseStart_3693331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693331 prefixEnd_3693331 := by exact prefixLift 3693331
  have htrace : WordTrace (prefixWord ++ tailWord_3693331) baseStart_3693331 baseEnd_3693331 := by
    simpa [prefixWord, tailWord_3693331, baseEnd_3693331] using wordTrace_append hprefix tailTrace_3693331
  have hstable : (prefixWord ++ tailWord_3693331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693331).length < 2 ^ (prefixWord ++ tailWord_3693331).sum := by decide
  have hdescent : baseEnd_3693331 < baseStart_3693331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693365 : List Nat := [1, 3, 3, 1, 3, 2, 1, 3, 5]
def baseStart_3693365 : Nat := 118140960795 + 3693365 * 2 ^ 59
def prefixEnd_3693365 : Nat := 4983230072969 + 3 ^ 40 * 3693365 * 2
def baseEnd_3693365 : Nat := 421438106109566094700451

theorem tailTrace_3693365 : CollatzResearch.WordTrace tailWord_3693365 prefixEnd_3693365 421438106109566094700451 := by
  unfold tailWord_3693365
  simp only [CollatzResearch.WordTrace]
  refine ⟨134708088264576856368425549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89805392176384570912283699 134708088264576856368425549)
  ·
    refine ⟨50515533099216321138159581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134708088264576856368425549 50515533099216321138159581)
    ·
      refine ⟨18943324912206120426809843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50515533099216321138159581 18943324912206120426809843)
      ·
        refine ⟨28414987368309180640214765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18943324912206120426809843 28414987368309180640214765)
        ·
          refine ⟨10655620263115942740080537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28414987368309180640214765 10655620263115942740080537)
          ·
            refine ⟨7991715197336957055060403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10655620263115942740080537 7991715197336957055060403)
            ·
              refine ⟨11987572796005435582590605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7991715197336957055060403 11987572796005435582590605)
              ·
                refine ⟨4495339798502038343471477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11987572796005435582590605 4495339798502038343471477)
                ·
                  refine ⟨421438106109566094700451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4495339798502038343471477 421438106109566094700451)
                  ·
                    rfl

theorem cell22_3693365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_3693365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693365 prefixEnd_3693365 := by exact prefixLift 3693365
  have htrace : WordTrace (prefixWord ++ tailWord_3693365) baseStart_3693365 baseEnd_3693365 := by
    simpa [prefixWord, tailWord_3693365, baseEnd_3693365] using wordTrace_append hprefix tailTrace_3693365
  have hstable : (prefixWord ++ tailWord_3693365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693365).length < 2 ^ (prefixWord ++ tailWord_3693365).sum := by decide
  have hdescent : baseEnd_3693365 < baseStart_3693365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693408 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 3, 5]
def baseStart_3693408 : Nat := 118140960795 + 3693408 * 2 ^ 59
def prefixEnd_3693408 : Nat := 4983230072969 + 3 ^ 40 * 3693408 * 2
def baseEnd_3693408 : Nat := 1264329038107460505276221

theorem tailTrace_3693408 : CollatzResearch.WordTrace tailWord_3693408 prefixEnd_3693408 1264329038107460505276221 := by
  unfold tailWord_3693408
  simp only [CollatzResearch.WordTrace]
  refine ⟨67354828301710537356120439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89806437735614049808160585 67354828301710537356120439)
  ·
    refine ⟨101032242452565806034180659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67354828301710537356120439 101032242452565806034180659)
    ·
      refine ⟨151548363678848709051270989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101032242452565806034180659 151548363678848709051270989)
      ·
        refine ⟨56830636379568265894226621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151548363678848709051270989 56830636379568265894226621)
        ·
          refine ⟨21311488642338099710334983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56830636379568265894226621 21311488642338099710334983)
          ·
            refine ⟨31967232963507149565502475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21311488642338099710334983 31967232963507149565502475)
            ·
              refine ⟨47950849445260724348253713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31967232963507149565502475 47950849445260724348253713)
              ·
                refine ⟨35963137083945543261190285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47950849445260724348253713 35963137083945543261190285)
                ·
                  refine ⟨13486176406479578722946357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35963137083945543261190285 13486176406479578722946357)
                  ·
                    refine ⟨1264329038107460505276221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13486176406479578722946357 1264329038107460505276221)
                    ·
                      rfl

theorem cell22_3693408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_3693408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693408 prefixEnd_3693408 := by exact prefixLift 3693408
  have htrace : WordTrace (prefixWord ++ tailWord_3693408) baseStart_3693408 baseEnd_3693408 := by
    simpa [prefixWord, tailWord_3693408, baseEnd_3693408] using wordTrace_append hprefix tailTrace_3693408
  have hstable : (prefixWord ++ tailWord_3693408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693408).length < 2 ^ (prefixWord ++ tailWord_3693408).sum := by decide
  have hdescent : baseEnd_3693408 < baseStart_3693408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693423 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 4, 4]
def baseStart_3693423 : Nat := 118140960795 + 3693423 * 2 ^ 59
def prefixEnd_3693423 : Nat := 4983230072969 + 3 ^ 40 * 3693423 * 2
def baseEnd_3693423 : Nat := 1264334172914005466151175

theorem tailTrace_3693423 : CollatzResearch.WordTrace tailWord_3693423 prefixEnd_3693423 1264334172914005466151175 := by
  unfold tailWord_3693423
  simp only [CollatzResearch.WordTrace]
  refine ⟨134710203698366732274036923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89806802465577821516024615 134710203698366732274036923)
  ·
    refine ⟨202065305547550098411055385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134710203698366732274036923 202065305547550098411055385)
    ·
      refine ⟨151548979160662573808291539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202065305547550098411055385 151548979160662573808291539)
      ·
        refine ⟨227323468740993860712437309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151548979160662573808291539 227323468740993860712437309)
        ·
          refine ⟨85246300777872697767163991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227323468740993860712437309 85246300777872697767163991)
          ·
            refine ⟨127869451166809046650745987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85246300777872697767163991 127869451166809046650745987)
            ·
              refine ⟨191804176750213569976118981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127869451166809046650745987 191804176750213569976118981)
              ·
                refine ⟨35963283140665044370522309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191804176750213569976118981 35963283140665044370522309)
                ·
                  refine ⟨6743115588874695819472933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35963283140665044370522309 6743115588874695819472933)
                  ·
                    refine ⟨1264334172914005466151175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6743115588874695819472933 1264334172914005466151175)
                    ·
                      rfl

theorem cell22_3693423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_3693423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693423 prefixEnd_3693423 := by exact prefixLift 3693423
  have htrace : WordTrace (prefixWord ++ tailWord_3693423) baseStart_3693423 baseEnd_3693423 := by
    simpa [prefixWord, tailWord_3693423, baseEnd_3693423] using wordTrace_append hprefix tailTrace_3693423
  have hstable : (prefixWord ++ tailWord_3693423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693423).length < 2 ^ (prefixWord ++ tailWord_3693423).sum := by decide
  have hdescent : baseEnd_3693423 < baseStart_3693423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693425 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 1, 5]
def baseStart_3693425 : Nat := 118140960795 + 3693425 * 2 ^ 59
def prefixEnd_3693425 : Nat := 4983230072969 + 3 ^ 40 * 3693425 * 2
def baseEnd_3693425 : Nat := 1264334857554878127601169

theorem tailTrace_3693425 : CollatzResearch.WordTrace tailWord_3693425 prefixEnd_3693425 1264334857554878127601169 := by
  unfold tailWord_3693425
  simp only [CollatzResearch.WordTrace]
  refine ⟨134710276644359486615609729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89806851096239657743739819 134710276644359486615609729)
  ·
    refine ⟨101032707483269614961707297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134710276644359486615609729 101032707483269614961707297)
    ·
      refine ⟨75774530612452211221280473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101032707483269614961707297 75774530612452211221280473)
      ·
        refine ⟨56830897959339158415960355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75774530612452211221280473 56830897959339158415960355)
        ·
          refine ⟨85246346939008737623940533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56830897959339158415960355 85246346939008737623940533)
          ·
            refine ⟨7991845025532069152244425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85246346939008737623940533 7991845025532069152244425)
            ·
              refine ⟨5993883769149051864183319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7991845025532069152244425 5993883769149051864183319)
              ·
                refine ⟨8990825653723577796274979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5993883769149051864183319 8990825653723577796274979)
                ·
                  refine ⟨13486238480585366694412469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8990825653723577796274979 13486238480585366694412469)
                  ·
                    refine ⟨1264334857554878127601169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13486238480585366694412469 1264334857554878127601169)
                    ·
                      rfl

theorem cell22_3693425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_3693425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693425 prefixEnd_3693425 := by exact prefixLift 3693425
  have htrace : WordTrace (prefixWord ++ tailWord_3693425) baseStart_3693425 baseEnd_3693425 := by
    simpa [prefixWord, tailWord_3693425, baseEnd_3693425] using wordTrace_append hprefix tailTrace_3693425
  have hstable : (prefixWord ++ tailWord_3693425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693425).length < 2 ^ (prefixWord ++ tailWord_3693425).sum := by decide
  have hdescent : baseEnd_3693425 < baseStart_3693425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693489 : List Nat := [1, 2, 2, 4, 4, 1, 2, 6]
def baseStart_3693489 : Nat := 118140960795 + 3693489 * 2 ^ 59
def prefixEnd_3693489 : Nat := 4983230072969 + 3 ^ 40 * 3693489 * 2
def baseEnd_3693489 : Nat := 140484085118089254888997

theorem tailTrace_3693489 : CollatzResearch.WordTrace tailWord_3693489 prefixEnd_3693489 140484085118089254888997 := by
  unfold tailWord_3693489
  simp only [CollatzResearch.WordTrace]
  refine ⟨134712610916127625545939521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89808407277418417030626347 134712610916127625545939521)
  ·
    refine ⟨101034458187095719159454641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134712610916127625545939521 101034458187095719159454641)
    ·
      refine ⟨75775843640321789369590981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101034458187095719159454641 75775843640321789369590981)
      ·
        refine ⟨14207970682560335506798309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75775843640321789369590981 14207970682560335506798309)
        ·
          refine ⟨2663994502980062907524683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14207970682560335506798309 2663994502980062907524683)
          ·
            refine ⟨3995991754470094361287025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663994502980062907524683 3995991754470094361287025)
            ·
              refine ⟨2996993815852570770965269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3995991754470094361287025 2996993815852570770965269)
              ·
                refine ⟨140484085118089254888997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2996993815852570770965269 140484085118089254888997)
                ·
                  rfl

theorem cell22_3693489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 6].length) (baseStart_3693489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693489 prefixEnd_3693489 := by exact prefixLift 3693489
  have htrace : WordTrace (prefixWord ++ tailWord_3693489) baseStart_3693489 baseEnd_3693489 := by
    simpa [prefixWord, tailWord_3693489, baseEnd_3693489] using wordTrace_append hprefix tailTrace_3693489
  have hstable : (prefixWord ++ tailWord_3693489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693489).length < 2 ^ (prefixWord ++ tailWord_3693489).sum := by decide
  have hdescent : baseEnd_3693489 < baseStart_3693489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693504 : List Nat := [2, 1, 1, 2, 3, 3, 3, 3, 1, 3]
def baseStart_3693504 : Nat := 118140960795 + 3693504 * 2 ^ 59
def prefixEnd_3693504 : Nat := 4983230072969 + 3 ^ 40 * 3693504 * 2
def baseEnd_3693504 : Nat := 1264361900869348254875927

theorem tailTrace_3693504 : CollatzResearch.WordTrace tailWord_3693504 prefixEnd_3693504 1264361900869348254875927 := by
  unfold tailWord_3693504
  simp only [CollatzResearch.WordTrace]
  refine ⟨67356579005536641553867783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89808772007382188738490377 67356579005536641553867783)
  ·
    refine ⟨101034868508304962330801675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67356579005536641553867783 101034868508304962330801675)
    ·
      refine ⟨151552302762457443496202513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101034868508304962330801675 151552302762457443496202513)
      ·
        refine ⟨113664227071843082622151885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151552302762457443496202513 113664227071843082622151885)
        ·
          refine ⟨42624085151941155983306957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113664227071843082622151885 42624085151941155983306957)
          ·
            refine ⟨15984031931977933493740109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42624085151941155983306957 15984031931977933493740109)
            ·
              refine ⟨5994011974491725060152541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15984031931977933493740109 5994011974491725060152541)
              ·
                refine ⟨2247754490434396897557203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5994011974491725060152541 2247754490434396897557203)
                ·
                  refine ⟨3371631735651595346335805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247754490434396897557203 3371631735651595346335805)
                  ·
                    refine ⟨1264361900869348254875927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3371631735651595346335805 1264361900869348254875927)
                    ·
                      rfl

theorem cell22_3693504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 1, 3].length) (baseStart_3693504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693504 prefixEnd_3693504 := by exact prefixLift 3693504
  have htrace : WordTrace (prefixWord ++ tailWord_3693504) baseStart_3693504 baseEnd_3693504 := by
    simpa [prefixWord, tailWord_3693504, baseEnd_3693504] using wordTrace_append hprefix tailTrace_3693504
  have hstable : (prefixWord ++ tailWord_3693504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693504).length < 2 ^ (prefixWord ++ tailWord_3693504).sum := by decide
  have hdescent : baseEnd_3693504 < baseStart_3693504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693564 : List Nat := [2, 2, 2, 1, 2, 4, 3, 1, 1, 4]
def baseStart_3693564 : Nat := 118140960795 + 3693564 * 2 ^ 59
def prefixEnd_3693564 : Nat := 4983230072969 + 3 ^ 40 * 3693564 * 2
def baseEnd_3693564 : Nat := 1264382440095528098375743

theorem tailTrace_3693564 : CollatzResearch.WordTrace tailWord_3693564 prefixEnd_3693564 1264382440095528098375743 := by
  unfold tailWord_3693564
  simp only [CollatzResearch.WordTrace]
  refine ⟨67357673195427956677459873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89810230927237275569946497 67357673195427956677459873)
  ·
    refine ⟨50518254896570967508094905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67357673195427956677459873 50518254896570967508094905)
    ·
      refine ⟨37888691172428225631071179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50518254896570967508094905 37888691172428225631071179)
      ·
        refine ⟨56833036758642338446606769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37888691172428225631071179 56833036758642338446606769)
        ·
          refine ⟨42624777568981753834955077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56833036758642338446606769 42624777568981753834955077)
          ·
            refine ⟨7992145794184078844054077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42624777568981753834955077 7992145794184078844054077)
            ·
              refine ⟨2997054672819029566520279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7992145794184078844054077 2997054672819029566520279)
              ·
                refine ⟨4495582009228544349780419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2997054672819029566520279 4495582009228544349780419)
                ·
                  refine ⟨6743373013842816524670629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4495582009228544349780419 6743373013842816524670629)
                  ·
                    refine ⟨1264382440095528098375743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6743373013842816524670629 1264382440095528098375743)
                    ·
                      rfl

theorem cell22_3693564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_3693564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693564 prefixEnd_3693564 := by exact prefixLift 3693564
  have htrace : WordTrace (prefixWord ++ tailWord_3693564) baseStart_3693564 baseEnd_3693564 := by
    simpa [prefixWord, tailWord_3693564, baseEnd_3693564] using wordTrace_append hprefix tailTrace_3693564
  have hstable : (prefixWord ++ tailWord_3693564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693564).length < 2 ^ (prefixWord ++ tailWord_3693564).sum := by decide
  have hdescent : baseEnd_3693564 < baseStart_3693564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693579 : List Nat := [1, 1, 1, 1, 6, 2, 4, 2, 4]
def baseStart_3693579 : Nat := 118140960795 + 3693579 * 2 ^ 59
def prefixEnd_3693579 : Nat := 4983230072969 + 3 ^ 40 * 3693579 * 2
def baseEnd_3693579 : Nat := 421462524967357686416899

theorem tailTrace_3693579 : CollatzResearch.WordTrace tailWord_3693579 prefixEnd_3693579 421462524967357686416899 := by
  unfold tailWord_3693579
  simp only [CollatzResearch.WordTrace]
  refine ⟨134715893485801570916715791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89810595657201047277810527 134715893485801570916715791)
  ·
    refine ⟨202073840228702356375073687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134715893485801570916715791 202073840228702356375073687)
    ·
      refine ⟨303110760343053534562610531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202073840228702356375073687 303110760343053534562610531)
      ·
        refine ⟨454666140514580301843915797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303110760343053534562610531 454666140514580301843915797)
        ·
          refine ⟨21312475336620951648933553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 454666140514580301843915797 21312475336620951648933553)
          ·
            refine ⟨15984356502465713736700165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21312475336620951648933553 15984356502465713736700165)
            ·
              refine ⟨2997066844212321325631281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15984356502465713736700165 2997066844212321325631281)
              ·
                refine ⟨2247800133159240994223461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2997066844212321325631281 2247800133159240994223461)
                ·
                  refine ⟨421462524967357686416899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2247800133159240994223461 421462524967357686416899)
                  ·
                    rfl

theorem cell22_3693579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 4].length) (baseStart_3693579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693579 prefixEnd_3693579 := by exact prefixLift 3693579
  have htrace : WordTrace (prefixWord ++ tailWord_3693579) baseStart_3693579 baseEnd_3693579 := by
    simpa [prefixWord, tailWord_3693579, baseEnd_3693579] using wordTrace_append hprefix tailTrace_3693579
  have hstable : (prefixWord ++ tailWord_3693579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693579).length < 2 ^ (prefixWord ++ tailWord_3693579).sum := by decide
  have hdescent : baseEnd_3693579 < baseStart_3693579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693635 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 7]
def baseStart_3693635 : Nat := 118140960795 + 3693635 * 2 ^ 59
def prefixEnd_3693635 : Nat := 4983230072969 + 3 ^ 40 * 3693635 * 2
def baseEnd_3693635 : Nat := 421468914948835859950175

theorem tailTrace_3693635 : CollatzResearch.WordTrace tailWord_3693635 prefixEnd_3693635 421468914948835859950175 := by
  unfold tailWord_3693635
  simp only [CollatzResearch.WordTrace]
  refine ⟨134717935973598692480754359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89811957315732461653836239 134717935973598692480754359)
  ·
    refine ⟨202076903960398038721131539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134717935973598692480754359 202076903960398038721131539)
    ·
      refine ⟨303115355940597058081697309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202076903960398038721131539 303115355940597058081697309)
      ·
        refine ⟨113668258477723896780636491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303115355940597058081697309 113668258477723896780636491)
        ·
          refine ⟨170502387716585845170954737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113668258477723896780636491 170502387716585845170954737)
          ·
            refine ⟨127876790787439383878216053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170502387716585845170954737 127876790787439383878216053)
            ·
              refine ⟨11988449136322442238582755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127876790787439383878216053 11988449136322442238582755)
              ·
                refine ⟨17982673704483663357874133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11988449136322442238582755 17982673704483663357874133)
                ·
                  refine ⟨421468914948835859950175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17982673704483663357874133 421468914948835859950175)
                  ·
                    rfl

theorem cell22_3693635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 7].length) (baseStart_3693635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693635 prefixEnd_3693635 := by exact prefixLift 3693635
  have htrace : WordTrace (prefixWord ++ tailWord_3693635) baseStart_3693635 baseEnd_3693635 := by
    simpa [prefixWord, tailWord_3693635, baseEnd_3693635] using wordTrace_append hprefix tailTrace_3693635
  have hstable : (prefixWord ++ tailWord_3693635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693635).length < 2 ^ (prefixWord ++ tailWord_3693635).sum := by decide
  have hdescent : baseEnd_3693635 < baseStart_3693635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693639 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 3, 3]
def baseStart_3693639 : Nat := 118140960795 + 3693639 * 2 ^ 59
def prefixEnd_3693639 : Nat := 4983230072969 + 3 ^ 40 * 3693639 * 2
def baseEnd_3693639 : Nat := 1264408114128252902750513

theorem tailTrace_3693639 : CollatzResearch.WordTrace tailWord_3693639 prefixEnd_3693639 1264408114128252902750513 := by
  unfold tailWord_3693639
  simp only [CollatzResearch.WordTrace]
  refine ⟨134718081865584201163899971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89812054577056134109266647 134718081865584201163899971)
  ·
    refine ⟨202077122798376301745849957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134718081865584201163899971 202077122798376301745849957)
    ·
      refine ⟨37889460524695556577346867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202077122798376301745849957 37889460524695556577346867)
      ·
        refine ⟨56834190787043334866020301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37889460524695556577346867 56834190787043334866020301)
        ·
          refine ⟨21312821545141250574757613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56834190787043334866020301 21312821545141250574757613)
          ·
            refine ⟨7992308079427968965534105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21312821545141250574757613 7992308079427968965534105)
            ·
              refine ⟨5994231059570976724150579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7992308079427968965534105 5994231059570976724150579)
              ·
                refine ⟨8991346589356465086225869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5994231059570976724150579 8991346589356465086225869)
                ·
                  refine ⟨3371754971008674407334701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8991346589356465086225869 3371754971008674407334701)
                  ·
                    refine ⟨1264408114128252902750513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3371754971008674407334701 1264408114128252902750513)
                    ·
                      rfl

theorem cell22_3693639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_3693639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693639 prefixEnd_3693639 := by exact prefixLift 3693639
  have htrace : WordTrace (prefixWord ++ tailWord_3693639) baseStart_3693639 baseEnd_3693639 := by
    simpa [prefixWord, tailWord_3693639, baseEnd_3693639] using wordTrace_append hprefix tailTrace_3693639
  have hstable : (prefixWord ++ tailWord_3693639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693639).length < 2 ^ (prefixWord ++ tailWord_3693639).sum := by decide
  have hdescent : baseEnd_3693639 < baseStart_3693639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693652 : List Nat := [2, 4, 1, 1, 1, 1, 2, 5, 5]
def baseStart_3693652 : Nat := 118140960795 + 3693652 * 2 ^ 59
def prefixEnd_3693652 : Nat := 4983230072969 + 3 ^ 40 * 3693652 * 2
def baseEnd_3693652 : Nat := 421470854764641734058491

theorem tailTrace_3693652 : CollatzResearch.WordTrace tailWord_3693652 prefixEnd_3693652 421470854764641734058491 := by
  unfold tailWord_3693652
  simp only [CollatzResearch.WordTrace]
  refine ⟨67359278007268552192061605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89812370676358069589415473 67359278007268552192061605)
  ·
    refine ⟨12629864626362853536011551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67359278007268552192061605 12629864626362853536011551)
    ·
      refine ⟨18944796939544280304017327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12629864626362853536011551 18944796939544280304017327)
      ·
        refine ⟨28417195409316420456025991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18944796939544280304017327 28417195409316420456025991)
        ·
          refine ⟨42625793113974630684038987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28417195409316420456025991 42625793113974630684038987)
          ·
            refine ⟨63938689670961946026058481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42625793113974630684038987 63938689670961946026058481)
            ·
              refine ⟨47954017253221459519543861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63938689670961946026058481 47954017253221459519543861)
              ·
                refine ⟨4495689117489511829957237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47954017253221459519543861 4495689117489511829957237)
                ·
                  refine ⟨421470854764641734058491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4495689117489511829957237 421470854764641734058491)
                  ·
                    rfl

theorem cell22_3693652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_3693652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693652 prefixEnd_3693652 := by exact prefixLift 3693652
  have htrace : WordTrace (prefixWord ++ tailWord_3693652) baseStart_3693652 baseEnd_3693652 := by
    simpa [prefixWord, tailWord_3693652, baseEnd_3693652] using wordTrace_append hprefix tailTrace_3693652
  have hstable : (prefixWord ++ tailWord_3693652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693652).length < 2 ^ (prefixWord ++ tailWord_3693652).sum := by decide
  have hdescent : baseEnd_3693652 < baseStart_3693652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693712 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 6, 3]
def baseStart_3693712 : Nat := 118140960795 + 3693712 * 2 ^ 59
def prefixEnd_3693712 : Nat := 4983230072969 + 3 ^ 40 * 3693712 * 2
def baseEnd_3693712 : Nat := 1264433103520105045675289

theorem tailTrace_3693712 : CollatzResearch.WordTrace tailWord_3693712 prefixEnd_3693712 1264433103520105045675289 := by
  unfold tailWord_3693712
  simp only [CollatzResearch.WordTrace]
  refine ⟨67360372197159867315653695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89813829596213156420871593 67360372197159867315653695)
  ·
    refine ⟨101040558295739800973480543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67360372197159867315653695 101040558295739800973480543)
    ·
      refine ⟨151560837443609701460220815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101040558295739800973480543 151560837443609701460220815)
      ·
        refine ⟨227341256165414552190331223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151560837443609701460220815 227341256165414552190331223)
        ·
          refine ⟨341011884248121828285496835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227341256165414552190331223 341011884248121828285496835)
          ·
            refine ⟨511517826372182742428245253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341011884248121828285496835 511517826372182742428245253)
            ·
              refine ⟨95909592444784264205295985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 511517826372182742428245253 95909592444784264205295985)
              ·
                refine ⟨71932194333588198153971989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95909592444784264205295985 71932194333588198153971989)
                ·
                  refine ⟨3371821609386946788467437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71932194333588198153971989 3371821609386946788467437)
                  ·
                    refine ⟨1264433103520105045675289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3371821609386946788467437 1264433103520105045675289)
                    ·
                      rfl

theorem cell22_3693712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 6, 3].length) (baseStart_3693712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693712 prefixEnd_3693712 := by exact prefixLift 3693712
  have htrace : WordTrace (prefixWord ++ tailWord_3693712) baseStart_3693712 baseEnd_3693712 := by
    simpa [prefixWord, tailWord_3693712, baseEnd_3693712] using wordTrace_append hprefix tailTrace_3693712
  have hstable : (prefixWord ++ tailWord_3693712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693712).length < 2 ^ (prefixWord ++ tailWord_3693712).sum := by decide
  have hdescent : baseEnd_3693712 < baseStart_3693712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693742 : List Nat := [4, 1, 4, 13]
def baseStart_3693742 : Nat := 118140960795 + 3693742 * 2 ^ 59
def prefixEnd_3693742 : Nat := 4983230072969 + 3 ^ 40 * 3693742 * 2
def baseEnd_3693742 : Nat := 1734490223776673480693

theorem tailTrace_3693742 : CollatzResearch.WordTrace tailWord_3693742 prefixEnd_3693742 1734490223776673480693 := by
  unfold tailWord_3693742
  simp only [CollatzResearch.WordTrace]
  refine ⟨16840229823026381219362435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89814559056140699836599653 16840229823026381219362435)
  ·
    refine ⟨25260344734539571829043653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16840229823026381219362435 25260344734539571829043653)
    ·
      refine ⟨4736314637726169717945685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25260344734539571829043653 4736314637726169717945685)
      ·
        refine ⟨1734490223776673480693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4736314637726169717945685 1734490223776673480693)
        ·
          rfl

theorem cell22_3693742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 13].length) (baseStart_3693742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693742 prefixEnd_3693742 := by exact prefixLift 3693742
  have htrace : WordTrace (prefixWord ++ tailWord_3693742) baseStart_3693742 baseEnd_3693742 := by
    simpa [prefixWord, tailWord_3693742, baseEnd_3693742] using wordTrace_append hprefix tailTrace_3693742
  have hstable : (prefixWord ++ tailWord_3693742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693742).length < 2 ^ (prefixWord ++ tailWord_3693742).sum := by decide
  have hdescent : baseEnd_3693742 < baseStart_3693742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693746 : List Nat := [3, 2, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_3693746 : Nat := 118140960795 + 3693746 * 2 ^ 59
def prefixEnd_3693746 : Nat := 4983230072969 + 3 ^ 40 * 3693746 * 2
def baseEnd_3693746 : Nat := 1264444742414940290325185

theorem tailTrace_3693746 : CollatzResearch.WordTrace tailWord_3693746 prefixEnd_3693746 1264444742414940290325185 := by
  unfold tailWord_3693746
  simp only [CollatzResearch.WordTrace]
  refine ⟨33680496119049139609511273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89814656317464372292030061 33680496119049139609511273)
  ·
    refine ⟨25260372089286854707133455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33680496119049139609511273 25260372089286854707133455)
    ·
      refine ⟨37890558133930282060700183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25260372089286854707133455 37890558133930282060700183)
      ·
        refine ⟨56835837200895423091050275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37890558133930282060700183 56835837200895423091050275)
        ·
          refine ⟨85253755801343134636575413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56835837200895423091050275 85253755801343134636575413)
          ·
            refine ⟨7992539606375918872178945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85253755801343134636575413 7992539606375918872178945)
            ·
              refine ⟨5994404704781939154134209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7992539606375918872178945 5994404704781939154134209)
              ·
                refine ⟨4495803528586454365600657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5994404704781939154134209 4495803528586454365600657)
                ·
                  refine ⟨3371852646439840774200493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4495803528586454365600657 3371852646439840774200493)
                  ·
                    refine ⟨1264444742414940290325185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3371852646439840774200493 1264444742414940290325185)
                    ·
                      rfl

theorem cell22_3693746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_3693746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693746 prefixEnd_3693746 := by exact prefixLift 3693746
  have htrace : WordTrace (prefixWord ++ tailWord_3693746) baseStart_3693746 baseEnd_3693746 := by
    simpa [prefixWord, tailWord_3693746, baseEnd_3693746] using wordTrace_append hprefix tailTrace_3693746
  have hstable : (prefixWord ++ tailWord_3693746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693746).length < 2 ^ (prefixWord ++ tailWord_3693746).sum := by decide
  have hdescent : baseEnd_3693746 < baseStart_3693746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693791 : List Nat := [1, 1, 2, 3, 2, 1, 3, 5, 1, 3]
def baseStart_3693791 : Nat := 118140960795 + 3693791 * 2 ^ 59
def prefixEnd_3693791 : Nat := 4983230072969 + 3 ^ 40 * 3693791 * 2
def baseEnd_3693791 : Nat := 1264460146834575172950047

theorem tailTrace_3693791 : CollatzResearch.WordTrace tailWord_3693791 prefixEnd_3693791 1264460146834575172950047 := by
  unfold tailWord_3693791
  simp only [CollatzResearch.WordTrace]
  refine ⟨134723625761033531123433227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89815750507355687415622151 134723625761033531123433227)
  ·
    refine ⟨202085438641550296685149841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134723625761033531123433227 202085438641550296685149841)
    ·
      refine ⟨151564078981162722513862381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202085438641550296685149841 151564078981162722513862381)
      ·
        refine ⟨56836529617936020942698393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151564078981162722513862381 56836529617936020942698393)
        ·
          refine ⟨42627397213452015707023795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56836529617936020942698393 42627397213452015707023795)
          ·
            refine ⟨63941095820178023560535693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42627397213452015707023795 63941095820178023560535693)
            ·
              refine ⟨23977910932566758835200885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63941095820178023560535693 23977910932566758835200885)
              ·
                refine ⟨2247929149928133640800083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23977910932566758835200885 2247929149928133640800083)
                ·
                  refine ⟨3371893724892200461200125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2247929149928133640800083 3371893724892200461200125)
                  ·
                    refine ⟨1264460146834575172950047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3371893724892200461200125 1264460146834575172950047)
                    ·
                      rfl

theorem cell22_3693791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 1, 3].length) (baseStart_3693791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693791 prefixEnd_3693791 := by exact prefixLift 3693791
  have htrace : WordTrace (prefixWord ++ tailWord_3693791) baseStart_3693791 baseEnd_3693791 := by
    simpa [prefixWord, tailWord_3693791, baseEnd_3693791] using wordTrace_append hprefix tailTrace_3693791
  have hstable : (prefixWord ++ tailWord_3693791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693791).length < 2 ^ (prefixWord ++ tailWord_3693791).sum := by decide
  have hdescent : baseEnd_3693791 < baseStart_3693791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693804 : List Nat := [2, 2, 1, 1, 2, 4, 3, 2, 5]
def baseStart_3693804 : Nat := 118140960795 + 3693804 * 2 ^ 59
def prefixEnd_3693804 : Nat := 4983230072969 + 3 ^ 40 * 3693804 * 2
def baseEnd_3693804 : Nat := 421488199000082490791669

theorem tailTrace_3693804 : CollatzResearch.WordTrace tailWord_3693804 prefixEnd_3693804 421488199000082490791669 := by
  unfold tailWord_3693804
  simp only [CollatzResearch.WordTrace]
  refine ⟨67362049954993217171828233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89816066606657622895770977 67362049954993217171828233)
  ·
    refine ⟨50521537466244912878871175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67362049954993217171828233 50521537466244912878871175)
    ·
      refine ⟨75782306199367369318306763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50521537466244912878871175 75782306199367369318306763)
      ·
        refine ⟨113673459299051053977460145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75782306199367369318306763 113673459299051053977460145)
        ·
          refine ⟨85255094474288290483095109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113673459299051053977460145 85255094474288290483095109)
          ·
            refine ⟨15985330213929054465580333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85255094474288290483095109 15985330213929054465580333)
            ·
              refine ⟨5994498830223395424592625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15985330213929054465580333 5994498830223395424592625)
              ·
                refine ⟨4495874122667546568444469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5994498830223395424592625 4495874122667546568444469)
                ·
                  refine ⟨421488199000082490791669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4495874122667546568444469 421488199000082490791669)
                  ·
                    rfl

theorem cell22_3693804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_3693804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693804 prefixEnd_3693804 := by exact prefixLift 3693804
  have htrace : WordTrace (prefixWord ++ tailWord_3693804) baseStart_3693804 baseEnd_3693804 := by
    simpa [prefixWord, tailWord_3693804, baseEnd_3693804] using wordTrace_append hprefix tailTrace_3693804
  have hstable : (prefixWord ++ tailWord_3693804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693804).length < 2 ^ (prefixWord ++ tailWord_3693804).sum := by decide
  have hdescent : baseEnd_3693804 < baseStart_3693804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693866 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 6]
def baseStart_3693866 : Nat := 118140960795 + 3693866 * 2 ^ 59
def prefixEnd_3693866 : Nat := 4983230072969 + 3 ^ 40 * 3693866 * 2
def baseEnd_3693866 : Nat := 421495273622433325774939

theorem tailTrace_3693866 : CollatzResearch.WordTrace tailWord_3693866 prefixEnd_3693866 421495273622433325774939 := by
  unfold tailWord_3693866
  simp only [CollatzResearch.WordTrace]
  refine ⟨33681590308940454733103363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89817574157174545954942301 33681590308940454733103363)
  ·
    refine ⟨50522385463410682099655045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33681590308940454733103363 50522385463410682099655045)
    ·
      refine ⟨9472947274389502893685321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50522385463410682099655045 9472947274389502893685321)
      ·
        refine ⟨7104710455792127170263991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9472947274389502893685321 7104710455792127170263991)
        ·
          refine ⟨10657065683688190755395987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7104710455792127170263991 10657065683688190755395987)
          ·
            refine ⟨15985598525532286133093981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10657065683688190755395987 15985598525532286133093981)
            ·
              refine ⟨5994599447074607299910243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15985598525532286133093981 5994599447074607299910243)
              ·
                refine ⟨8991899170611910949865365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5994599447074607299910243 8991899170611910949865365)
                ·
                  refine ⟨421495273622433325774939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8991899170611910949865365 421495273622433325774939)
                  ·
                    rfl

theorem cell22_3693866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_3693866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693866 prefixEnd_3693866 := by exact prefixLift 3693866
  have htrace : WordTrace (prefixWord ++ tailWord_3693866) baseStart_3693866 baseEnd_3693866 := by
    simpa [prefixWord, tailWord_3693866, baseEnd_3693866] using wordTrace_append hprefix tailTrace_3693866
  have hstable : (prefixWord ++ tailWord_3693866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693866).length < 2 ^ (prefixWord ++ tailWord_3693866).sum := by decide
  have hdescent : baseEnd_3693866 < baseStart_3693866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693885 : List Nat := [1, 4, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_3693885 : Nat := 118140960795 + 3693885 * 2 ^ 59
def prefixEnd_3693885 : Nat := 4983230072969 + 3 ^ 40 * 3693885 * 2
def baseEnd_3693885 : Nat := 1264492324955590261099759

theorem tailTrace_3693885 : CollatzResearch.WordTrace tailWord_3693885 prefixEnd_3693885 1264492324955590261099759 := by
  unfold tailWord_3693885
  simp only [CollatzResearch.WordTrace]
  refine ⟨134727054222692985177355109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89818036148461990118236739 134727054222692985177355109)
  ·
    refine ⟨25261322666754934720754083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134727054222692985177355109 25261322666754934720754083)
    ·
      refine ⟨37891984000132402081131125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25261322666754934720754083 37891984000132402081131125)
      ·
        refine ⟨3552373500012412695106043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37891984000132402081131125 3552373500012412695106043)
        ·
          refine ⟨5328560250018619042659065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3552373500012412695106043 5328560250018619042659065)
          ·
            refine ⟨3996420187513964281994299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5328560250018619042659065 3996420187513964281994299)
            ·
              refine ⟨5994630281270946422991449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3996420187513964281994299 5994630281270946422991449)
              ·
                refine ⟨4495972710953209817243587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5994630281270946422991449 4495972710953209817243587)
                ·
                  refine ⟨6743959066429814725865381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4495972710953209817243587 6743959066429814725865381)
                  ·
                    refine ⟨1264492324955590261099759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6743959066429814725865381 1264492324955590261099759)
                    ·
                      rfl

theorem cell22_3693885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_3693885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693885 prefixEnd_3693885 := by exact prefixLift 3693885
  have htrace : WordTrace (prefixWord ++ tailWord_3693885) baseStart_3693885 baseEnd_3693885 := by
    simpa [prefixWord, tailWord_3693885, baseEnd_3693885] using wordTrace_append hprefix tailTrace_3693885
  have hstable : (prefixWord ++ tailWord_3693885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693885).length < 2 ^ (prefixWord ++ tailWord_3693885).sum := by decide
  have hdescent : baseEnd_3693885 < baseStart_3693885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693917 : List Nat := [1, 4, 5, 1, 1, 1, 1, 4, 4]
def baseStart_3693917 : Nat := 118140960795 + 3693917 * 2 ^ 59
def prefixEnd_3693917 : Nat := 4983230072969 + 3 ^ 40 * 3693917 * 2
def baseEnd_3693917 : Nat := 421501093069850948099887

theorem tailTrace_3693917 : CollatzResearch.WordTrace tailWord_3693917 prefixEnd_3693917 421501093069850948099887 := by
  unfold tailWord_3693917
  simp only [CollatzResearch.WordTrace]
  refine ⟨134728221358577054642520005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89818814239051369761680003 134728221358577054642520005)
  ·
    refine ⟨25261541504733197745472501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134728221358577054642520005 25261541504733197745472501)
    ·
      refine ⟨2368269516068737288638047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25261541504733197745472501 2368269516068737288638047)
      ·
        refine ⟨3552404274103105932957071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368269516068737288638047 3552404274103105932957071)
        ·
          refine ⟨5328606411154658899435607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3552404274103105932957071 5328606411154658899435607)
          ·
            refine ⟨7992909616731988349153411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5328606411154658899435607 7992909616731988349153411)
            ·
              refine ⟨11989364425097982523730117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7992909616731988349153411 11989364425097982523730117)
              ·
                refine ⟨2248005829705871723199397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11989364425097982523730117 2248005829705871723199397)
                ·
                  refine ⟨421501093069850948099887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2248005829705871723199397 421501093069850948099887)
                  ·
                    rfl

theorem cell22_3693917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_3693917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693917 prefixEnd_3693917 := by exact prefixLift 3693917
  have htrace : WordTrace (prefixWord ++ tailWord_3693917) baseStart_3693917 baseEnd_3693917 := by
    simpa [prefixWord, tailWord_3693917, baseEnd_3693917] using wordTrace_append hprefix tailTrace_3693917
  have hstable : (prefixWord ++ tailWord_3693917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693917).length < 2 ^ (prefixWord ++ tailWord_3693917).sum := by decide
  have hdescent : baseEnd_3693917 < baseStart_3693917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693924 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_3693924 : Nat := 118140960795 + 3693924 * 2 ^ 59
def prefixEnd_3693924 : Nat := 4983230072969 + 3 ^ 40 * 3693924 * 2
def baseEnd_3693924 : Nat := 1264505675452607159374639

theorem tailTrace_3693924 : CollatzResearch.WordTrace tailWord_3693924 prefixEnd_3693924 1264505675452607159374639 := by
  unfold tailWord_3693924
  simp only [CollatzResearch.WordTrace]
  refine ⟨67364238334775847419012413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89818984446367796558683217 67364238334775847419012413)
  ·
    refine ⟨25261589375540942782129655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67364238334775847419012413 25261589375540942782129655)
    ·
      refine ⟨37892384063311414173194483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25261589375540942782129655 37892384063311414173194483)
      ·
        refine ⟨56838576094967121259791725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37892384063311414173194483 56838576094967121259791725)
        ·
          refine ⟨21314466035612670472421897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56838576094967121259791725 21314466035612670472421897)
          ·
            refine ⟨15985849526709502854316423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21314466035612670472421897 15985849526709502854316423)
            ·
              refine ⟨23978774290064254281474635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15985849526709502854316423 23978774290064254281474635)
              ·
                refine ⟨35968161435096381422211953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23978774290064254281474635 35968161435096381422211953)
                ·
                  refine ⟨26976121076322286066658965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35968161435096381422211953 26976121076322286066658965)
                  ·
                    refine ⟨1264505675452607159374639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26976121076322286066658965 1264505675452607159374639)
                    ·
                      rfl

theorem cell22_3693924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_3693924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693924 prefixEnd_3693924 := by exact prefixLift 3693924
  have htrace : WordTrace (prefixWord ++ tailWord_3693924) baseStart_3693924 baseEnd_3693924 := by
    simpa [prefixWord, tailWord_3693924, baseEnd_3693924] using wordTrace_append hprefix tailTrace_3693924
  have hstable : (prefixWord ++ tailWord_3693924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693924).length < 2 ^ (prefixWord ++ tailWord_3693924).sum := by decide
  have hdescent : baseEnd_3693924 < baseStart_3693924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693928 : List Nat := [2, 1, 4, 2, 4, 1, 1, 7]
def baseStart_3693928 : Nat := 118140960795 + 3693928 * 2 ^ 59
def prefixEnd_3693928 : Nat := 4983230072969 + 3 ^ 40 * 3693928 * 2
def baseEnd_3693928 : Nat := 140500782748261386919403

theorem tailTrace_3693928 : CollatzResearch.WordTrace tailWord_3693928 prefixEnd_3693928 140500782748261386919403 := by
  unfold tailWord_3693928
  simp only [CollatzResearch.WordTrace]
  refine ⟨67364311280768601760585219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89819081707691469014113625 67364311280768601760585219)
  ·
    refine ⟨101046466921152902640877829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67364311280768601760585219 101046466921152902640877829)
    ·
      refine ⟨18946212547716169245164593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101046466921152902640877829 18946212547716169245164593)
      ·
        refine ⟨14209659410787126933873445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18946212547716169245164593 14209659410787126933873445)
        ·
          refine ⟨2664311139522586300101271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14209659410787126933873445 2664311139522586300101271)
          ·
            refine ⟨3996466709283879450151907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664311139522586300101271 3996466709283879450151907)
            ·
              refine ⟨5994700063925819175227861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3996466709283879450151907 5994700063925819175227861)
              ·
                refine ⟨140500782748261386919403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5994700063925819175227861 140500782748261386919403)
                ·
                  rfl

theorem cell22_3693928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 7].length) (baseStart_3693928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693928 prefixEnd_3693928 := by exact prefixLift 3693928
  have htrace : WordTrace (prefixWord ++ tailWord_3693928) baseStart_3693928 baseEnd_3693928 := by
    simpa [prefixWord, tailWord_3693928, baseEnd_3693928] using wordTrace_append hprefix tailTrace_3693928
  have hstable : (prefixWord ++ tailWord_3693928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693928).length < 2 ^ (prefixWord ++ tailWord_3693928).sum := by decide
  have hdescent : baseEnd_3693928 < baseStart_3693928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3693960 : List Nat := [2, 1, 3, 3, 1, 3, 2, 3, 1, 3]
def baseStart_3693960 : Nat := 118140960795 + 3693960 * 2 ^ 59
def prefixEnd_3693960 : Nat := 4983230072969 + 3 ^ 40 * 3693960 * 2
def baseEnd_3693960 : Nat := 1264517998988315065474529

theorem tailTrace_3693960 : CollatzResearch.WordTrace tailWord_3693960 prefixEnd_3693960 1264517998988315065474529 := by
  unfold tailWord_3693960
  simp only [CollatzResearch.WordTrace]
  refine ⟨67364894848710636493167667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89819859798280848657556889 67364894848710636493167667)
  ·
    refine ⟨101047342273065954739751501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67364894848710636493167667 101047342273065954739751501)
    ·
      refine ⟨37892753352399733027406813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101047342273065954739751501 37892753352399733027406813)
      ·
        refine ⟨14209782507149899885277555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37892753352399733027406813 14209782507149899885277555)
        ·
          refine ⟨21314673760724849827916333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14209782507149899885277555 21314673760724849827916333)
          ·
            refine ⟨7993002660271818685468625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21314673760724849827916333 7993002660271818685468625)
            ·
              refine ⟨5994751995203864014101469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7993002660271818685468625 5994751995203864014101469)
              ·
                refine ⟨2248031998201449005288051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5994751995203864014101469 2248031998201449005288051)
                ·
                  refine ⟨3372047997302173507932077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248031998201449005288051 3372047997302173507932077)
                  ·
                    refine ⟨1264517998988315065474529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3372047997302173507932077 1264517998988315065474529)
                    ·
                      rfl

theorem cell22_3693960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_3693960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3693960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3693960 prefixEnd_3693960 := by exact prefixLift 3693960
  have htrace : WordTrace (prefixWord ++ tailWord_3693960) baseStart_3693960 baseEnd_3693960 := by
    simpa [prefixWord, tailWord_3693960, baseEnd_3693960] using wordTrace_append hprefix tailTrace_3693960
  have hstable : (prefixWord ++ tailWord_3693960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3693960).length < 2 ^ (prefixWord ++ tailWord_3693960).sum := by decide
  have hdescent : baseEnd_3693960 < baseStart_3693960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3693960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694016 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 4, 3]
def baseStart_3694016 : Nat := 118140960795 + 3694016 * 2 ^ 59
def prefixEnd_3694016 : Nat := 4983230072969 + 3 ^ 40 * 3694016 * 2
def baseEnd_3694016 : Nat := 1264537168932749586074357

theorem tailTrace_3694016 : CollatzResearch.WordTrace tailWord_3694016 prefixEnd_3694016 1264537168932749586074357 := by
  unfold tailWord_3694016
  simp only [CollatzResearch.WordTrace]
  refine ⟨67365916092609197275186951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89821221456812263033582601 67365916092609197275186951)
  ·
    refine ⟨101048874138913795912780427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67365916092609197275186951 101048874138913795912780427)
    ·
      refine ⟨151573311208370693869170641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101048874138913795912780427 151573311208370693869170641)
      ·
        refine ⟨113679983406278020401877981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151573311208370693869170641 113679983406278020401877981)
        ·
          refine ⟨42629993777354257650704243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113679983406278020401877981 42629993777354257650704243)
          ·
            refine ⟨63944990666031386476056365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42629993777354257650704243 63944990666031386476056365)
            ·
              refine ⟨23979371499761769928521137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63944990666031386476056365 23979371499761769928521137)
              ·
                refine ⟨17984528624821327446390853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23979371499761769928521137 17984528624821327446390853)
                ·
                  refine ⟨3372099117153998896198285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17984528624821327446390853 3372099117153998896198285)
                  ·
                    refine ⟨1264537168932749586074357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3372099117153998896198285 1264537168932749586074357)
                    ·
                      rfl

theorem cell22_3694016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 4, 3].length) (baseStart_3694016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694016 prefixEnd_3694016 := by exact prefixLift 3694016
  have htrace : WordTrace (prefixWord ++ tailWord_3694016) baseStart_3694016 baseEnd_3694016 := by
    simpa [prefixWord, tailWord_3694016, baseEnd_3694016] using wordTrace_append hprefix tailTrace_3694016
  have hstable : (prefixWord ++ tailWord_3694016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694016).length < 2 ^ (prefixWord ++ tailWord_3694016).sum := by decide
  have hdescent : baseEnd_3694016 < baseStart_3694016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694059 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 4, 6]
def baseStart_3694059 : Nat := 118140960795 + 3694059 * 2 ^ 59
def prefixEnd_3694059 : Nat := 4983230072969 + 3 ^ 40 * 3694059 * 2
def baseEnd_3694059 : Nat := 1264551888711511807249225

theorem tailTrace_3694059 : CollatzResearch.WordTrace tailWord_3694059 prefixEnd_3694059 1264551888711511807249225 := by
  unfold tailWord_3694059
  simp only [CollatzResearch.WordTrace]
  refine ⟨134733400524062612894189231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89822267016041741929459487 134733400524062612894189231)
  ·
    refine ⟨202100100786093919341283847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134733400524062612894189231 202100100786093919341283847)
    ·
      refine ⟨303150151179140879011925771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202100100786093919341283847 303150151179140879011925771)
      ·
        refine ⟨454725226768711318517888657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303150151179140879011925771 454725226768711318517888657)
        ·
          refine ⟨341043920076533488888416493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454725226768711318517888657 341043920076533488888416493)
          ·
            refine ⟨127891470028700058333156185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341043920076533488888416493 127891470028700058333156185)
            ·
              refine ⟨95918602521525043749867139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127891470028700058333156185 95918602521525043749867139)
              ·
                refine ⟨143877903782287565624800709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95918602521525043749867139 143877903782287565624800709)
                ·
                  refine ⟨26977106959178918554650133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143877903782287565624800709 26977106959178918554650133)
                  ·
                    refine ⟨1264551888711511807249225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26977106959178918554650133 1264551888711511807249225)
                    ·
                      rfl

theorem cell22_3694059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 6].length) (baseStart_3694059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694059 prefixEnd_3694059 := by exact prefixLift 3694059
  have htrace : WordTrace (prefixWord ++ tailWord_3694059) baseStart_3694059 baseEnd_3694059 := by
    simpa [prefixWord, tailWord_3694059, baseEnd_3694059] using wordTrace_append hprefix tailTrace_3694059
  have hstable : (prefixWord ++ tailWord_3694059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694059).length < 2 ^ (prefixWord ++ tailWord_3694059).sum := by decide
  have hdescent : baseEnd_3694059 < baseStart_3694059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694138 : List Nat := [3, 1, 1, 1, 3, 2, 3, 3, 1, 4]
def baseStart_3694138 : Nat := 118140960795 + 3694138 * 2 ^ 59
def prefixEnd_3694138 : Nat := 4983230072969 + 3 ^ 40 * 3694138 * 2
def baseEnd_3694138 : Nat := 1264578932025981934523983

theorem tailTrace_3694138 : CollatzResearch.WordTrace tailWord_3694138 prefixEnd_3694138 1264578932025981934523983 := by
  unfold tailWord_3694138
  simp only [CollatzResearch.WordTrace]
  refine ⟨33684070472694102346578767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89824187927184272924210045 33684070472694102346578767)
  ·
    refine ⟨50526105709041153519868151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33684070472694102346578767 50526105709041153519868151)
    ·
      refine ⟨75789158563561730279802227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50526105709041153519868151 75789158563561730279802227)
      ·
        refine ⟨113683737845342595419703341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75789158563561730279802227 113683737845342595419703341)
        ·
          refine ⟨42631401692003473282388753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113683737845342595419703341 42631401692003473282388753)
          ·
            refine ⟨31973551269002604961791565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42631401692003473282388753 31973551269002604961791565)
            ·
              refine ⟨11990081725875976860671837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31973551269002604961791565 11990081725875976860671837)
              ·
                refine ⟨4496280647203491322751939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11990081725875976860671837 4496280647203491322751939)
                ·
                  refine ⟨6744420970805236984127909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496280647203491322751939 6744420970805236984127909)
                  ·
                    refine ⟨1264578932025981934523983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6744420970805236984127909 1264578932025981934523983)
                    ·
                      rfl

theorem cell22_3694138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_3694138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694138 prefixEnd_3694138 := by exact prefixLift 3694138
  have htrace : WordTrace (prefixWord ++ tailWord_3694138) baseStart_3694138 baseEnd_3694138 := by
    simpa [prefixWord, tailWord_3694138, baseEnd_3694138] using wordTrace_append hprefix tailTrace_3694138
  have hstable : (prefixWord ++ tailWord_3694138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694138).length < 2 ^ (prefixWord ++ tailWord_3694138).sum := by decide
  have hdescent : baseEnd_3694138 < baseStart_3694138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694198 : List Nat := [5, 1, 1, 2, 2, 1, 10]
def baseStart_3694198 : Nat := 118140960795 + 3694198 * 2 ^ 59
def prefixEnd_3694198 : Nat := 4983230072969 + 3 ^ 40 * 3694198 * 2
def baseEnd_3694198 : Nat := 46837017453783769556437

theorem tailTrace_3694198 : CollatzResearch.WordTrace tailWord_3694198 prefixEnd_3694198 46837017453783769556437 := by
  unfold tailWord_3694198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8421154391909939977093703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89825646847039359755666165 8421154391909939977093703)
  ·
    refine ⟨12631731587864909965640555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8421154391909939977093703 12631731587864909965640555)
    ·
      refine ⟨18947597381797364948460833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12631731587864909965640555 18947597381797364948460833)
      ·
        refine ⟨14210698036348023711345625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18947597381797364948460833 14210698036348023711345625)
        ·
          refine ⟨10658023527261017783509219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14210698036348023711345625 10658023527261017783509219)
          ·
            refine ⟨15987035290891526675263829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10658023527261017783509219 15987035290891526675263829)
            ·
              refine ⟨46837017453783769556437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15987035290891526675263829 46837017453783769556437)
              ·
                rfl

theorem cell22_3694198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 10].length) (baseStart_3694198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694198 prefixEnd_3694198 := by exact prefixLift 3694198
  have htrace : WordTrace (prefixWord ++ tailWord_3694198) baseStart_3694198 baseEnd_3694198 := by
    simpa [prefixWord, tailWord_3694198, baseEnd_3694198] using wordTrace_append hprefix tailTrace_3694198
  have hstable : (prefixWord ++ tailWord_3694198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694198).length < 2 ^ (prefixWord ++ tailWord_3694198).sum := by decide
  have hdescent : baseEnd_3694198 < baseStart_3694198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694211 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 2, 6]
def baseStart_3694211 : Nat := 118140960795 + 3694211 * 2 ^ 59
def prefixEnd_3694211 : Nat := 4983230072969 + 3 ^ 40 * 3694211 * 2
def baseEnd_3694211 : Nat := 1264603921417834077448759

theorem tailTrace_3694211 : CollatzResearch.WordTrace tailWord_3694211 prefixEnd_3694211 1264603921417834077448759 := by
  unfold tailWord_3694211
  simp only [CollatzResearch.WordTrace]
  refine ⟨134738944419511942853722487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89825962946341295235814991 134738944419511942853722487)
  ·
    refine ⟨202108416629267914280583731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134738944419511942853722487 202108416629267914280583731)
    ·
      refine ⟨303162624943901871420875597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202108416629267914280583731 303162624943901871420875597)
      ·
        refine ⟨113685984353963201782828349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303162624943901871420875597 113685984353963201782828349)
        ·
          refine ⟨42632244132736200668560631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113685984353963201782828349 42632244132736200668560631)
          ·
            refine ⟨63948366199104301002840947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42632244132736200668560631 63948366199104301002840947)
            ·
              refine ⟨95922549298656451504261421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63948366199104301002840947 95922549298656451504261421)
              ·
                refine ⟨35970955986996169314098033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95922549298656451504261421 35970955986996169314098033)
                ·
                  refine ⟨26978216990247126985573525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35970955986996169314098033 26978216990247126985573525)
                  ·
                    refine ⟨1264603921417834077448759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26978216990247126985573525 1264603921417834077448759)
                    ·
                      rfl

theorem cell22_3694211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 6].length) (baseStart_3694211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694211 prefixEnd_3694211 := by exact prefixLift 3694211
  have htrace : WordTrace (prefixWord ++ tailWord_3694211) baseStart_3694211 baseEnd_3694211 := by
    simpa [prefixWord, tailWord_3694211, baseEnd_3694211] using wordTrace_append hprefix tailTrace_3694211
  have hstable : (prefixWord ++ tailWord_3694211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694211).length < 2 ^ (prefixWord ++ tailWord_3694211).sum := by decide
  have hdescent : baseEnd_3694211 < baseStart_3694211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694290 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_3694290 : Nat := 118140960795 + 3694290 * 2 ^ 59
def prefixEnd_3694290 : Nat := 4983230072969 + 3 ^ 40 * 3694290 * 2
def baseEnd_3694290 : Nat := 1264630964732304204723517

theorem tailTrace_3694290 : CollatzResearch.WordTrace tailWord_3694290 prefixEnd_3694290 1264630964732304204723517 := by
  unfold tailWord_3694290
  simp only [CollatzResearch.WordTrace]
  refine ⟨33685456446556434836462081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89827883857483826230565549 33685456446556434836462081)
  ·
    refine ⟨25264092334917326127346561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33685456446556434836462081 25264092334917326127346561)
    ·
      refine ⟨18948069251187994595509921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25264092334917326127346561 18948069251187994595509921)
      ·
        refine ⟨14211051938390995946632441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18948069251187994595509921 14211051938390995946632441)
        ·
          refine ⟨10658288953793246959974331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14211051938390995946632441 10658288953793246959974331)
          ·
            refine ⟨15987433430689870439961497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10658288953793246959974331 15987433430689870439961497)
            ·
              refine ⟨11990575073017402829971123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15987433430689870439961497 11990575073017402829971123)
              ·
                refine ⟨17985862609526104244956685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11990575073017402829971123 17985862609526104244956685)
                ·
                  refine ⟨6744698478572289091858757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17985862609526104244956685 6744698478572289091858757)
                  ·
                    refine ⟨1264630964732304204723517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6744698478572289091858757 1264630964732304204723517)
                    ·
                      rfl

theorem cell22_3694290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_3694290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694290 prefixEnd_3694290 := by exact prefixLift 3694290
  have htrace : WordTrace (prefixWord ++ tailWord_3694290) baseStart_3694290 baseEnd_3694290 := by
    simpa [prefixWord, tailWord_3694290, baseEnd_3694290] using wordTrace_append hprefix tailTrace_3694290
  have hstable : (prefixWord ++ tailWord_3694290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694290).length < 2 ^ (prefixWord ++ tailWord_3694290).sum := by decide
  have hdescent : baseEnd_3694290 < baseStart_3694290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694303 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 1, 5]
def baseStart_3694303 : Nat := 118140960795 + 3694303 * 2 ^ 59
def prefixEnd_3694303 : Nat := 4983230072969 + 3 ^ 40 * 3694303 * 2
def baseEnd_3694303 : Nat := 1264635414897976504148477

theorem tailTrace_3694303 : CollatzResearch.WordTrace tailWord_3694303 prefixEnd_3694303 1264635414897976504148477 := by
  unfold tailWord_3694303
  simp only [CollatzResearch.WordTrace]
  refine ⟨134742299935178642566071563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89828199956785761710714375 134742299935178642566071563)
  ·
    refine ⟨202113449902767963849107345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134742299935178642566071563 202113449902767963849107345)
    ·
      refine ⟨151585087427075972886830509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202113449902767963849107345 151585087427075972886830509)
      ·
        refine ⟨56844407785153489832561441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151585087427075972886830509 56844407785153489832561441)
        ·
          refine ⟨42633305838865117374421081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56844407785153489832561441 42633305838865117374421081)
          ·
            refine ⟨31974979379148838030815811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42633305838865117374421081 31974979379148838030815811)
            ·
              refine ⟨47962469068723257046223717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31974979379148838030815811 47962469068723257046223717)
              ·
                refine ⟨8992962950385610696166947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47962469068723257046223717 8992962950385610696166947)
                ·
                  refine ⟨13489444425578416044250421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8992962950385610696166947 13489444425578416044250421)
                  ·
                    refine ⟨1264635414897976504148477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13489444425578416044250421 1264635414897976504148477)
                    ·
                      rfl

theorem cell22_3694303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_3694303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694303 prefixEnd_3694303 := by exact prefixLift 3694303
  have htrace : WordTrace (prefixWord ++ tailWord_3694303) baseStart_3694303 baseEnd_3694303 := by
    simpa [prefixWord, tailWord_3694303, baseEnd_3694303] using wordTrace_append hprefix tailTrace_3694303
  have hstable : (prefixWord ++ tailWord_3694303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694303).length < 2 ^ (prefixWord ++ tailWord_3694303).sum := by decide
  have hdescent : baseEnd_3694303 < baseStart_3694303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694307 : List Nat := [1, 1, 1, 7, 2, 1, 1, 3, 1, 4]
def baseStart_3694307 : Nat := 118140960795 + 3694307 * 2 ^ 59
def prefixEnd_3694307 : Nat := 4983230072969 + 3 ^ 40 * 3694307 * 2
def baseEnd_3694307 : Nat := 1264636784179721827048465

theorem tailTrace_3694307 : CollatzResearch.WordTrace tailWord_3694307 prefixEnd_3694307 1264636784179721827048465 := by
  unfold tailWord_3694307
  simp only [CollatzResearch.WordTrace]
  refine ⟨134742445827164151249217175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89828297218109434166144783 134742445827164151249217175)
  ·
    refine ⟨202113668740746226873825763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134742445827164151249217175 202113668740746226873825763)
    ·
      refine ⟨303170503111119340310738645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202113668740746226873825763 303170503111119340310738645)
      ·
        refine ⟨7105558666666859538532937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 303170503111119340310738645 7105558666666859538532937)
        ·
          refine ⟨5329169000000144653899703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7105558666666859538532937 5329169000000144653899703)
          ·
            refine ⟨7993753500000216980849555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5329169000000144653899703 7993753500000216980849555)
            ·
              refine ⟨11990630250000325471274333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7993753500000216980849555 11990630250000325471274333)
              ·
                refine ⟨4496486343750122051727875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11990630250000325471274333 4496486343750122051727875)
                ·
                  refine ⟨6744729515625183077591813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4496486343750122051727875 6744729515625183077591813)
                  ·
                    refine ⟨1264636784179721827048465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6744729515625183077591813 1264636784179721827048465)
                    ·
                      rfl

theorem cell22_3694307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 4].length) (baseStart_3694307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694307 prefixEnd_3694307 := by exact prefixLift 3694307
  have htrace : WordTrace (prefixWord ++ tailWord_3694307) baseStart_3694307 baseEnd_3694307 := by
    simpa [prefixWord, tailWord_3694307, baseEnd_3694307] using wordTrace_append hprefix tailTrace_3694307
  have hstable : (prefixWord ++ tailWord_3694307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694307).length < 2 ^ (prefixWord ++ tailWord_3694307).sum := by decide
  have hdescent : baseEnd_3694307 < baseStart_3694307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694320 : List Nat := [2, 1, 1, 1, 3, 1, 2, 6, 2, 3]
def baseStart_3694320 : Nat := 118140960795 + 3694320 * 2 ^ 59
def prefixEnd_3694320 : Nat := 4983230072969 + 3 ^ 40 * 3694320 * 2
def baseEnd_3694320 : Nat := 1264641234345394126473425

theorem tailTrace_3694320 : CollatzResearch.WordTrace tailWord_3694320 prefixEnd_3694320 1264641234345394126473425 := by
  unfold tailWord_3694320
  simp only [CollatzResearch.WordTrace]
  refine ⟨67371459988058527234720207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89828613317411369646293609 67371459988058527234720207)
  ·
    refine ⟨101057189982087790852080311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67371459988058527234720207 101057189982087790852080311)
    ·
      refine ⟨151585784973131686278120467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101057189982087790852080311 151585784973131686278120467)
      ·
        refine ⟨227378677459697529417180701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151585784973131686278120467 227378677459697529417180701)
        ·
          refine ⟨85267004047386573531442763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227378677459697529417180701 85267004047386573531442763)
          ·
            refine ⟨127900506071079860297164145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85267004047386573531442763 127900506071079860297164145)
            ·
              refine ⟨95925379553309895222873109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127900506071079860297164145 95925379553309895222873109)
              ·
                refine ⟨4496502166561401338572177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95925379553309895222873109 4496502166561401338572177)
                ·
                  refine ⟨3372376624921051003929133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4496502166561401338572177 3372376624921051003929133)
                  ·
                    refine ⟨1264641234345394126473425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3372376624921051003929133 1264641234345394126473425)
                    ·
                      rfl

theorem cell22_3694320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 2, 3].length) (baseStart_3694320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694320 prefixEnd_3694320 := by exact prefixLift 3694320
  have htrace : WordTrace (prefixWord ++ tailWord_3694320) baseStart_3694320 baseEnd_3694320 := by
    simpa [prefixWord, tailWord_3694320, baseEnd_3694320] using wordTrace_append hprefix tailTrace_3694320
  have hstable : (prefixWord ++ tailWord_3694320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694320).length < 2 ^ (prefixWord ++ tailWord_3694320).sum := by decide
  have hdescent : baseEnd_3694320 < baseStart_3694320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694350 : List Nat := [4, 1, 1, 2, 1, 1, 6, 6]
def baseStart_3694350 : Nat := 118140960795 + 3694350 * 2 ^ 59
def prefixEnd_3694350 : Nat := 4983230072969 + 3 ^ 40 * 3694350 * 2
def baseEnd_3694350 : Nat := 140516833773164894247037

theorem tailTrace_3694350 : CollatzResearch.WordTrace tailWord_3694350 prefixEnd_3694350 140516833773164894247037 := by
  unfold tailWord_3694350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16843001770751046199129063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89829342777338913062021669 16843001770751046199129063)
  ·
    refine ⟨25264502656126569298693595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16843001770751046199129063 25264502656126569298693595)
    ·
      refine ⟨37896753984189853948040393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25264502656126569298693595 37896753984189853948040393)
      ·
        refine ⟨28422565488142390461030295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37896753984189853948040393 28422565488142390461030295)
        ·
          refine ⟨42633848232213585691545443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28422565488142390461030295 42633848232213585691545443)
          ·
            refine ⟨63950772348320378537318165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42633848232213585691545443 63950772348320378537318165)
            ·
              refine ⟨2997692453827517743936789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63950772348320378537318165 2997692453827517743936789)
              ·
                refine ⟨140516833773164894247037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2997692453827517743936789 140516833773164894247037)
                ·
                  rfl

theorem cell22_3694350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_3694350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694350 prefixEnd_3694350 := by exact prefixLift 3694350
  have htrace : WordTrace (prefixWord ++ tailWord_3694350) baseStart_3694350 baseEnd_3694350 := by
    simpa [prefixWord, tailWord_3694350, baseEnd_3694350] using wordTrace_append hprefix tailTrace_3694350
  have hstable : (prefixWord ++ tailWord_3694350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694350).length < 2 ^ (prefixWord ++ tailWord_3694350).sum := by decide
  have hdescent : baseEnd_3694350 < baseStart_3694350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694440 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 6]
def baseStart_3694440 : Nat := 118140960795 + 3694440 * 2 ^ 59
def prefixEnd_3694440 : Nat := 4983230072969 + 3 ^ 40 * 3694440 * 2
def baseEnd_3694440 : Nat := 421560770932584604491019

theorem tailTrace_3694440 : CollatzResearch.WordTrace tailWord_3694440 prefixEnd_3694440 421560770932584604491019 := by
  unfold tailWord_3694440
  simp only [CollatzResearch.WordTrace]
  refine ⟨67373648367841157481904387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89831531157121543309205849 67373648367841157481904387)
  ·
    refine ⟨101060472551761736222856581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67373648367841157481904387 101060472551761736222856581)
    ·
      refine ⟨18948838603455325541785609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101060472551761736222856581 18948838603455325541785609)
      ·
        refine ⟨14211628952591494156339207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18948838603455325541785609 14211628952591494156339207)
        ·
          refine ⟨21317443428887241234508811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14211628952591494156339207 21317443428887241234508811)
          ·
            refine ⟨31976165143330861851763217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21317443428887241234508811 31976165143330861851763217)
            ·
              refine ⟨23982123857498146388822413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31976165143330861851763217 23982123857498146388822413)
              ·
                refine ⟨8993296446561804895808405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23982123857498146388822413 8993296446561804895808405)
                ·
                  refine ⟨421560770932584604491019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8993296446561804895808405 421560770932584604491019)
                  ·
                    rfl

theorem cell22_3694440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 6].length) (baseStart_3694440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694440 prefixEnd_3694440 := by exact prefixLift 3694440
  have htrace : WordTrace (prefixWord ++ tailWord_3694440) baseStart_3694440 baseEnd_3694440 := by
    simpa [prefixWord, tailWord_3694440, baseEnd_3694440] using wordTrace_append hprefix tailTrace_3694440
  have hstable : (prefixWord ++ tailWord_3694440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694440).length < 2 ^ (prefixWord ++ tailWord_3694440).sum := by decide
  have hdescent : baseEnd_3694440 < baseStart_3694440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694455 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 8, 3]
def baseStart_3694455 : Nat := 118140960795 + 3694455 * 2 ^ 59
def prefixEnd_3694455 : Nat := 4983230072969 + 3 ^ 40 * 3694455 * 2
def baseEnd_3694455 : Nat := 1264687447604298774348011

theorem tailTrace_3694455 : CollatzResearch.WordTrace tailWord_3694455 prefixEnd_3694455 1264687447604298774348011 := by
  unfold tailWord_3694455
  simp only [CollatzResearch.WordTrace]
  refine ⟨134747843830627972525604819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89831895887085315017069879 134747843830627972525604819)
  ·
    refine ⟨202121765745941958788407229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134747843830627972525604819 202121765745941958788407229)
    ·
      refine ⟨75795662154728234545652711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202121765745941958788407229 75795662154728234545652711)
      ·
        refine ⟨113693493232092351818479067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75795662154728234545652711 113693493232092351818479067)
        ·
          refine ⟨170540239848138527727718601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113693493232092351818479067 170540239848138527727718601)
          ·
            refine ⟨127905179886103895795788951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170540239848138527727718601 127905179886103895795788951)
            ·
              refine ⟨191857769829155843693683427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127905179886103895795788951 191857769829155843693683427)
              ·
                refine ⟨287786654743733765540525141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191857769829155843693683427 287786654743733765540525141)
                ·
                  refine ⟨3372499860278130064928029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 287786654743733765540525141 3372499860278130064928029)
                  ·
                    refine ⟨1264687447604298774348011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3372499860278130064928029 1264687447604298774348011)
                    ·
                      rfl

theorem cell22_3694455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_3694455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694455 prefixEnd_3694455 := by exact prefixLift 3694455
  have htrace : WordTrace (prefixWord ++ tailWord_3694455) baseStart_3694455 baseEnd_3694455 := by
    simpa [prefixWord, tailWord_3694455, baseEnd_3694455] using wordTrace_append hprefix tailTrace_3694455
  have hstable : (prefixWord ++ tailWord_3694455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694455).length < 2 ^ (prefixWord ++ tailWord_3694455).sum := by decide
  have hdescent : baseEnd_3694455 < baseStart_3694455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694545 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 2, 5]
def baseStart_3694545 : Nat := 118140960795 + 3694545 * 2 ^ 59
def prefixEnd_3694545 : Nat := 4983230072969 + 3 ^ 40 * 3694545 * 2
def baseEnd_3694545 : Nat := 1264718256443568539597735

theorem tailTrace_3694545 : CollatzResearch.WordTrace tailWord_3694545 prefixEnd_3694545 1264718256443568539597735 := by
  unfold tailWord_3694545
  simp only [CollatzResearch.WordTrace]
  refine ⟨134751126400301917896381089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89834084266867945264254059 134751126400301917896381089)
  ·
    refine ⟨101063344800226438422285817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134751126400301917896381089 101063344800226438422285817)
    ·
      refine ⟨75797508600169828816714363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101063344800226438422285817 75797508600169828816714363)
      ·
        refine ⟨113696262900254743225071545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75797508600169828816714363 113696262900254743225071545)
        ·
          refine ⟨85272197175191057418803659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113696262900254743225071545 85272197175191057418803659)
          ·
            refine ⟨127908295762786586128205489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85272197175191057418803659 127908295762786586128205489)
            ·
              refine ⟨95931221822089939596154117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127908295762786586128205489 95931221822089939596154117)
              ·
                refine ⟨17987104091641863674278897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95931221822089939596154117 17987104091641863674278897)
                ·
                  refine ⟨13490328068731397755709173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17987104091641863674278897 13490328068731397755709173)
                  ·
                    refine ⟨1264718256443568539597735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13490328068731397755709173 1264718256443568539597735)
                    ·
                      rfl

theorem cell22_3694545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_3694545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694545 prefixEnd_3694545 := by exact prefixLift 3694545
  have htrace : WordTrace (prefixWord ++ tailWord_3694545) baseStart_3694545 baseEnd_3694545 := by
    simpa [prefixWord, tailWord_3694545, baseEnd_3694545] using wordTrace_append hprefix tailTrace_3694545
  have hstable : (prefixWord ++ tailWord_3694545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694545).length < 2 ^ (prefixWord ++ tailWord_3694545).sum := by decide
  have hdescent : baseEnd_3694545 < baseStart_3694545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694551 : List Nat := [1, 1, 3, 2, 1, 1, 7, 2, 1, 3]
def baseStart_3694551 : Nat := 118140960795 + 3694551 * 2 ^ 59
def prefixEnd_3694551 : Nat := 4983230072969 + 3 ^ 40 * 3694551 * 2
def baseEnd_3694551 : Nat := 1264720310366186523947717

theorem tailTrace_3694551 : CollatzResearch.WordTrace tailWord_3694551 prefixEnd_3694551 1264720310366186523947717 := by
  unfold tailWord_3694551
  simp only [CollatzResearch.WordTrace]
  refine ⟨134751345238280180921099507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89834230158853453947399671 134751345238280180921099507)
  ·
    refine ⟨202127017857420271381649261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134751345238280180921099507 202127017857420271381649261)
    ·
      refine ⟨75797631696532601768118473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202127017857420271381649261 75797631696532601768118473)
      ·
        refine ⟨56848223772399451326088855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75797631696532601768118473 56848223772399451326088855)
        ·
          refine ⟨85272335658599176989133283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56848223772399451326088855 85272335658599176989133283)
          ·
            refine ⟨127908503487898765483699925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85272335658599176989133283 127908503487898765483699925)
            ·
              refine ⟨2997855550497627316024217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 127908503487898765483699925 2997855550497627316024217)
              ·
                refine ⟨2248391662873220487018163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2997855550497627316024217 2248391662873220487018163)
                ·
                  refine ⟨3372587494309830730527245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248391662873220487018163 3372587494309830730527245)
                  ·
                    refine ⟨1264720310366186523947717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3372587494309830730527245 1264720310366186523947717)
                    ·
                      rfl

theorem cell22_3694551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_3694551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694551 prefixEnd_3694551 := by exact prefixLift 3694551
  have htrace : WordTrace (prefixWord ++ tailWord_3694551) baseStart_3694551 baseEnd_3694551 := by
    simpa [prefixWord, tailWord_3694551, baseEnd_3694551] using wordTrace_append hprefix tailTrace_3694551
  have hstable : (prefixWord ++ tailWord_3694551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694551).length < 2 ^ (prefixWord ++ tailWord_3694551).sum := by decide
  have hdescent : baseEnd_3694551 < baseStart_3694551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694575 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 8]
def baseStart_3694575 : Nat := 118140960795 + 3694575 * 2 ^ 59
def prefixEnd_3694575 : Nat := 4983230072969 + 3 ^ 40 * 3694575 * 2
def baseEnd_3694575 : Nat := 421576175352219487115881

theorem tailTrace_3694575 : CollatzResearch.WordTrace tailWord_3694575 prefixEnd_3694575 421576175352219487115881 := by
  unfold tailWord_3694575
  simp only [CollatzResearch.WordTrace]
  refine ⟨134752220590193233019973179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89834813726795488679982119 134752220590193233019973179)
  ·
    refine ⟨202128330885289849529959769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134752220590193233019973179 202128330885289849529959769)
    ·
      refine ⟨151596248163967387147469827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202128330885289849529959769 151596248163967387147469827)
      ·
        refine ⟨227394372245951080721204741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151596248163967387147469827 227394372245951080721204741)
        ·
          refine ⟨42636444796115827635225889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227394372245951080721204741 42636444796115827635225889)
          ·
            refine ⟨31977333597086870726419417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42636444796115827635225889 31977333597086870726419417)
            ·
              refine ⟨23983000197815153044814563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31977333597086870726419417 23983000197815153044814563)
              ·
                refine ⟨35974500296722729567221845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23983000197815153044814563 35974500296722729567221845)
                ·
                  refine ⟨421576175352219487115881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35974500296722729567221845 421576175352219487115881)
                  ·
                    rfl

theorem cell22_3694575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 8].length) (baseStart_3694575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694575 prefixEnd_3694575 := by exact prefixLift 3694575
  have htrace : WordTrace (prefixWord ++ tailWord_3694575) baseStart_3694575 baseEnd_3694575 := by
    simpa [prefixWord, tailWord_3694575, baseEnd_3694575] using wordTrace_append hprefix tailTrace_3694575
  have hstable : (prefixWord ++ tailWord_3694575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694575).length < 2 ^ (prefixWord ++ tailWord_3694575).sum := by decide
  have hdescent : baseEnd_3694575 < baseStart_3694575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694635 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 1, 9]
def baseStart_3694635 : Nat := 118140960795 + 3694635 * 2 ^ 59
def prefixEnd_3694635 : Nat := 4983230072969 + 3 ^ 40 * 3694635 * 2
def baseEnd_3694635 : Nat := 1264749065282838304847459

theorem tailTrace_3694635 : CollatzResearch.WordTrace tailWord_3694635 prefixEnd_3694635 1264749065282838304847459 := by
  unfold tailWord_3694635
  simp only [CollatzResearch.WordTrace]
  refine ⟨134754408969975863267157359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89836272646650575511438239 134754408969975863267157359)
  ·
    refine ⟨202131613454963794900736039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134754408969975863267157359 202131613454963794900736039)
    ·
      refine ⟨303197420182445692351104059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202131613454963794900736039 303197420182445692351104059)
      ·
        refine ⟨454796130273668538526656089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303197420182445692351104059 454796130273668538526656089)
        ·
          refine ⟨341097097705251403894992067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454796130273668538526656089 341097097705251403894992067)
          ·
            refine ⟨511645646557877105842488101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341097097705251403894992067 511645646557877105842488101)
            ·
              refine ⟨95933558729601957345466519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 511645646557877105842488101 95933558729601957345466519)
              ·
                refine ⟨143900338094402936018199779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95933558729601957345466519 143900338094402936018199779)
                ·
                  refine ⟨215850507141604404027299669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143900338094402936018199779 215850507141604404027299669)
                  ·
                    refine ⟨1264749065282838304847459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 215850507141604404027299669 1264749065282838304847459)
                    ·
                      rfl

theorem cell22_3694635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_3694635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694635 prefixEnd_3694635 := by exact prefixLift 3694635
  have htrace : WordTrace (prefixWord ++ tailWord_3694635) baseStart_3694635 baseEnd_3694635 := by
    simpa [prefixWord, tailWord_3694635, baseEnd_3694635] using wordTrace_append hprefix tailTrace_3694635
  have hstable : (prefixWord ++ tailWord_3694635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694635).length < 2 ^ (prefixWord ++ tailWord_3694635).sum := by decide
  have hdescent : baseEnd_3694635 < baseStart_3694635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694654 : List Nat := [4, 2, 1, 3, 2, 1, 9]
def baseStart_3694654 : Nat := 118140960795 + 3694654 * 2 ^ 59
def prefixEnd_3694654 : Nat := 4983230072969 + 3 ^ 40 * 3694654 * 2
def baseEnd_3694654 : Nat := 46842798865597355134163

theorem tailTrace_3694654 : CollatzResearch.WordTrace tailWord_3694654 prefixEnd_3694654 46842798865597355134163 := by
  unfold tailWord_3694654
  simp only [CollatzResearch.WordTrace]
  refine ⟨16844387744613378689012377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89836734637938019674732677 16844387744613378689012377)
  ·
    refine ⟨12633290808460034016759283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16844387744613378689012377 12633290808460034016759283)
    ·
      refine ⟨18949936212690051025138925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12633290808460034016759283 18949936212690051025138925)
      ·
        refine ⟨7106226079758769134427097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18949936212690051025138925 7106226079758769134427097)
        ·
          refine ⟨5329669559819076850820323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7106226079758769134427097 5329669559819076850820323)
          ·
            refine ⟨7994504339728615276230485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5329669559819076850820323 7994504339728615276230485)
            ·
              refine ⟨46842798865597355134163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7994504339728615276230485 46842798865597355134163)
              ·
                rfl

theorem cell22_3694654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 9].length) (baseStart_3694654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694654 prefixEnd_3694654 := by exact prefixLift 3694654
  have htrace : WordTrace (prefixWord ++ tailWord_3694654) baseStart_3694654 baseEnd_3694654 := by
    simpa [prefixWord, tailWord_3694654, baseEnd_3694654] using wordTrace_append hprefix tailTrace_3694654
  have hstable : (prefixWord ++ tailWord_3694654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694654).length < 2 ^ (prefixWord ++ tailWord_3694654).sum := by decide
  have hdescent : baseEnd_3694654 < baseStart_3694654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694703 : List Nat := [1, 1, 2, 1, 3, 6, 1, 3, 1, 3]
def baseStart_3694703 : Nat := 118140960795 + 3694703 * 2 ^ 59
def prefixEnd_3694703 : Nat := 4983230072969 + 3 ^ 40 * 3694703 * 2
def baseEnd_3694703 : Nat := 1264772343072508794147251

theorem tailTrace_3694703 : CollatzResearch.WordTrace tailWord_3694703 prefixEnd_3694703 1264772343072508794147251 := by
  unfold tailWord_3694703
  simp only [CollatzResearch.WordTrace]
  refine ⟨134756889133729510880632763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89837926089153007253755175 134756889133729510880632763)
  ·
    refine ⟨202135333700594266320949145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134756889133729510880632763 202135333700594266320949145)
    ·
      refine ⟨151601500275445699740711859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202135333700594266320949145 151601500275445699740711859)
      ·
        refine ⟨227402250413168549611067789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151601500275445699740711859 227402250413168549611067789)
        ·
          refine ⟨85275843904938206104150421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227402250413168549611067789 85275843904938206104150421)
          ·
            refine ⟨3997305183043978411132051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85275843904938206104150421 3997305183043978411132051)
            ·
              refine ⟨5995957774565967616698077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997305183043978411132051 5995957774565967616698077)
              ·
                refine ⟨2248484165462237856261779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5995957774565967616698077 2248484165462237856261779)
                ·
                  refine ⟨3372726248193356784392669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248484165462237856261779 3372726248193356784392669)
                  ·
                    refine ⟨1264772343072508794147251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3372726248193356784392669 1264772343072508794147251)
                    ·
                      rfl

theorem cell22_3694703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 1, 3].length) (baseStart_3694703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694703 prefixEnd_3694703 := by exact prefixLift 3694703
  have htrace : WordTrace (prefixWord ++ tailWord_3694703) baseStart_3694703 baseEnd_3694703 := by
    simpa [prefixWord, tailWord_3694703, baseEnd_3694703] using wordTrace_append hprefix tailTrace_3694703
  have hstable : (prefixWord ++ tailWord_3694703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694703).length < 2 ^ (prefixWord ++ tailWord_3694703).sum := by decide
  have hdescent : baseEnd_3694703 < baseStart_3694703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694712 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 5, 4]
def baseStart_3694712 : Nat := 118140960795 + 3694712 * 2 ^ 59
def prefixEnd_3694712 : Nat := 4983230072969 + 3 ^ 40 * 3694712 * 2
def baseEnd_3694712 : Nat := 1264775423956435770672223

theorem tailTrace_3694712 : CollatzResearch.WordTrace tailWord_3694712 prefixEnd_3694712 1264775423956435770672223 := by
  unfold tailWord_3694712
  simp only [CollatzResearch.WordTrace]
  refine ⟨67378608695348452708855195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89838144927131270278473593 67378608695348452708855195)
  ·
    refine ⟨101067913043022679063282793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67378608695348452708855195 101067913043022679063282793)
    ·
      refine ⟨75800934782267009297462095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101067913043022679063282793 75800934782267009297462095)
      ·
        refine ⟨113701402173400513946193143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75800934782267009297462095 113701402173400513946193143)
        ·
          refine ⟨170552103260100770919289715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113701402173400513946193143 170552103260100770919289715)
          ·
            refine ⟨255828154890151156378934573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170552103260100770919289715 255828154890151156378934573)
            ·
              refine ⟨95935558083806683642100465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255828154890151156378934573 95935558083806683642100465)
              ·
                refine ⟨71951668562855012731575349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95935558083806683642100465 71951668562855012731575349)
                ·
                  refine ⟨6745468927767657443585189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71951668562855012731575349 6745468927767657443585189)
                  ·
                    refine ⟨1264775423956435770672223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6745468927767657443585189 1264775423956435770672223)
                    ·
                      rfl

theorem cell22_3694712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_3694712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694712 prefixEnd_3694712 := by exact prefixLift 3694712
  have htrace : WordTrace (prefixWord ++ tailWord_3694712) baseStart_3694712 baseEnd_3694712 := by
    simpa [prefixWord, tailWord_3694712, baseEnd_3694712] using wordTrace_append hprefix tailTrace_3694712
  have hstable : (prefixWord ++ tailWord_3694712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694712).length < 2 ^ (prefixWord ++ tailWord_3694712).sum := by decide
  have hdescent : baseEnd_3694712 < baseStart_3694712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694746 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 3, 4]
def baseStart_3694746 : Nat := 118140960795 + 3694746 * 2 ^ 59
def prefixEnd_3694746 : Nat := 4983230072969 + 3 ^ 40 * 3694746 * 2
def baseEnd_3694746 : Nat := 1264787062851271015322119

theorem tailTrace_3694746 : CollatzResearch.WordTrace tailWord_3694746 prefixEnd_3694746 1264787062851271015322119 := by
  unfold tailWord_3694746
  simp only [CollatzResearch.WordTrace]
  refine ⟨33689614368143432306112023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89838971648382486149632061 33689614368143432306112023)
  ·
    refine ⟨50534421552215148459168035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33689614368143432306112023 50534421552215148459168035)
    ·
      refine ⟨75801632328322722688752053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50534421552215148459168035 75801632328322722688752053)
      ·
        refine ⟨7106403030780255252070505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75801632328322722688752053 7106403030780255252070505)
        ·
          refine ⟨5329802273085191439052879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7106403030780255252070505 5329802273085191439052879)
          ·
            refine ⟨7994703409627787158579319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5329802273085191439052879 7994703409627787158579319)
            ·
              refine ⟨11992055114441680737868979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7994703409627787158579319 11992055114441680737868979)
              ·
                refine ⟨17988082671662521106803469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11992055114441680737868979 17988082671662521106803469)
                ·
                  refine ⟨6745531001873445415051301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17988082671662521106803469 6745531001873445415051301)
                  ·
                    refine ⟨1264787062851271015322119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6745531001873445415051301 1264787062851271015322119)
                    ·
                      rfl

theorem cell22_3694746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_3694746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694746 prefixEnd_3694746 := by exact prefixLift 3694746
  have htrace : WordTrace (prefixWord ++ tailWord_3694746) baseStart_3694746 baseEnd_3694746 := by
    simpa [prefixWord, tailWord_3694746, baseEnd_3694746] using wordTrace_append hprefix tailTrace_3694746
  have hstable : (prefixWord ++ tailWord_3694746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694746).length < 2 ^ (prefixWord ++ tailWord_3694746).sum := by decide
  have hdescent : baseEnd_3694746 < baseStart_3694746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694776 : List Nat := [2, 1, 2, 1, 2, 1, 6, 2, 2, 3]
def baseStart_3694776 : Nat := 118140960795 + 3694776 * 2 ^ 59
def prefixEnd_3694776 : Nat := 4983230072969 + 3 ^ 40 * 3694776 * 2
def baseEnd_3694776 : Nat := 1264797332464360937072027

theorem tailTrace_3694776 : CollatzResearch.WordTrace tailWord_3694776 prefixEnd_3694776 1264797332464360937072027 := by
  unfold tailWord_3694776
  simp only [CollatzResearch.WordTrace]
  refine ⟨67379775831232522174020091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89839701108310029565360121 67379775831232522174020091)
  ·
    refine ⟨101069663746848783261030137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67379775831232522174020091 101069663746848783261030137)
    ·
      refine ⟨75802247810136587445772603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101069663746848783261030137 75802247810136587445772603)
      ·
        refine ⟨113703371715204881168658905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75802247810136587445772603 113703371715204881168658905)
        ·
          refine ⟨85277528786403660876494179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113703371715204881168658905 85277528786403660876494179)
          ·
            refine ⟨127916293179605491314741269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85277528786403660876494179 127916293179605491314741269)
            ·
              refine ⟨5996076242794007405378497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127916293179605491314741269 5996076242794007405378497)
              ·
                refine ⟨4497057182095505554033873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5996076242794007405378497 4497057182095505554033873)
                ·
                  refine ⟨3372792886571629165525405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4497057182095505554033873 3372792886571629165525405)
                  ·
                    refine ⟨1264797332464360937072027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3372792886571629165525405 1264797332464360937072027)
                    ·
                      rfl

theorem cell22_3694776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_3694776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694776 prefixEnd_3694776 := by exact prefixLift 3694776
  have htrace : WordTrace (prefixWord ++ tailWord_3694776) baseStart_3694776 baseEnd_3694776 := by
    simpa [prefixWord, tailWord_3694776, baseEnd_3694776] using wordTrace_append hprefix tailTrace_3694776
  have hstable : (prefixWord ++ tailWord_3694776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694776).length < 2 ^ (prefixWord ++ tailWord_3694776).sum := by decide
  have hdescent : baseEnd_3694776 < baseStart_3694776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694849 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 2, 5]
def baseStart_3694849 : Nat := 118140960795 + 3694849 * 2 ^ 59
def prefixEnd_3694849 : Nat := 4983230072969 + 3 ^ 40 * 3694849 * 2
def baseEnd_3694849 : Nat := 1264822321856213079996803

theorem tailTrace_3694849 : CollatzResearch.WordTrace tailWord_3694849 prefixEnd_3694849 1264822321856213079996803 := by
  unfold tailWord_3694849
  simp only [CollatzResearch.WordTrace]
  refine ⟨134762214191200577815447601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89841476127467051876965067 134762214191200577815447601)
  ·
    refine ⟨101071660643400433361585701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134762214191200577815447601 101071660643400433361585701)
    ·
      refine ⟨18950936370637581255297319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101071660643400433361585701 18950936370637581255297319)
      ·
        refine ⟨28426404555956371882945979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18950936370637581255297319 28426404555956371882945979)
        ·
          refine ⟨42639606833934557824418969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28426404555956371882945979 42639606833934557824418969)
          ·
            refine ⟨31979705125450918368314227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42639606833934557824418969 31979705125450918368314227)
            ·
              refine ⟨47969557688176377552471341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31979705125450918368314227 47969557688176377552471341)
              ·
                refine ⟨17988584133066141582176753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47969557688176377552471341 17988584133066141582176753)
                ·
                  refine ⟨13491438099799606186632565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17988584133066141582176753 13491438099799606186632565)
                  ·
                    refine ⟨1264822321856213079996803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13491438099799606186632565 1264822321856213079996803)
                    ·
                      rfl

theorem cell22_3694849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_3694849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694849 prefixEnd_3694849 := by exact prefixLift 3694849
  have htrace : WordTrace (prefixWord ++ tailWord_3694849) baseStart_3694849 baseEnd_3694849 := by
    simpa [prefixWord, tailWord_3694849, baseEnd_3694849] using wordTrace_append hprefix tailTrace_3694849
  have hstable : (prefixWord ++ tailWord_3694849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694849).length < 2 ^ (prefixWord ++ tailWord_3694849).sum := by decide
  have hdescent : baseEnd_3694849 < baseStart_3694849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694851 : List Nat := [1, 1, 1, 3, 2, 3, 5, 1, 5]
def baseStart_3694851 : Nat := 118140960795 + 3694851 * 2 ^ 59
def prefixEnd_3694851 : Nat := 4983230072969 + 3 ^ 40 * 3694851 * 2
def baseEnd_3694851 : Nat := 421607668832361913815599

theorem tailTrace_3694851 : CollatzResearch.WordTrace tailWord_3694851 prefixEnd_3694851 421607668832361913815599 := by
  unfold tailWord_3694851
  simp only [CollatzResearch.WordTrace]
  refine ⟨134762287137193332157020407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89841524758128888104680271 134762287137193332157020407)
  ·
    refine ⟨202143430705789998235530611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134762287137193332157020407 202143430705789998235530611)
    ·
      refine ⟨303215146058684997353295917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202143430705789998235530611 303215146058684997353295917)
      ·
        refine ⟨113705679772006874007485969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303215146058684997353295917 113705679772006874007485969)
        ·
          refine ⟨85279259829005155505614477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113705679772006874007485969 85279259829005155505614477)
          ·
            refine ⟨31979722435876933314605429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85279259829005155505614477 31979722435876933314605429)
            ·
              refine ⟨2998098978363462498244259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31979722435876933314605429 2998098978363462498244259)
              ·
                refine ⟨4497148467545193747366389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998098978363462498244259 4497148467545193747366389)
                ·
                  refine ⟨421607668832361913815599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4497148467545193747366389 421607668832361913815599)
                  ·
                    rfl

theorem cell22_3694851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 5].length) (baseStart_3694851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694851 prefixEnd_3694851 := by exact prefixLift 3694851
  have htrace : WordTrace (prefixWord ++ tailWord_3694851) baseStart_3694851 baseEnd_3694851 := by
    simpa [prefixWord, tailWord_3694851, baseEnd_3694851] using wordTrace_append hprefix tailTrace_3694851
  have hstable : (prefixWord ++ tailWord_3694851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694851).length < 2 ^ (prefixWord ++ tailWord_3694851).sum := by decide
  have hdescent : baseEnd_3694851 < baseStart_3694851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694881 : List Nat := [1, 2, 3, 2, 1, 1, 4, 3, 1, 4]
def baseStart_3694881 : Nat := 118140960795 + 3694881 * 2 ^ 59
def prefixEnd_3694881 : Nat := 4983230072969 + 3 ^ 40 * 3694881 * 2
def baseEnd_3694881 : Nat := 1264833276110175663196705

theorem tailTrace_3694881 : CollatzResearch.WordTrace tailWord_3694881 prefixEnd_3694881 1264833276110175663196705 := by
  unfold tailWord_3694881
  simp only [CollatzResearch.WordTrace]
  refine ⟨134763381327084647280612497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89842254218056431520408331 134763381327084647280612497)
  ·
    refine ⟨101072535995313485460459373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134763381327084647280612497 101072535995313485460459373)
    ·
      refine ⟨37902200998242557047672265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101072535995313485460459373 37902200998242557047672265)
      ·
        refine ⟨28426650748681917785754199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37902200998242557047672265 28426650748681917785754199)
        ·
          refine ⟨42639976123022876678631299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28426650748681917785754199 42639976123022876678631299)
          ·
            refine ⟨63959964184534315017946949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42639976123022876678631299 63959964184534315017946949)
            ·
              refine ⟨11992493284600184065865053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63959964184534315017946949 11992493284600184065865053)
              ·
                refine ⟨4497184981725069024699395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11992493284600184065865053 4497184981725069024699395)
                ·
                  refine ⟨6745777472587603537049093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497184981725069024699395 6745777472587603537049093)
                  ·
                    refine ⟨1264833276110175663196705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6745777472587603537049093 1264833276110175663196705)
                    ·
                      rfl

theorem cell22_3694881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_3694881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694881 prefixEnd_3694881 := by exact prefixLift 3694881
  have htrace : WordTrace (prefixWord ++ tailWord_3694881) baseStart_3694881 baseEnd_3694881 := by
    simpa [prefixWord, tailWord_3694881, baseEnd_3694881] using wordTrace_append hprefix tailTrace_3694881
  have hstable : (prefixWord ++ tailWord_3694881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694881).length < 2 ^ (prefixWord ++ tailWord_3694881).sum := by decide
  have hdescent : baseEnd_3694881 < baseStart_3694881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694924 : List Nat := [2, 2, 1, 3, 2, 1, 1, 10]
def baseStart_3694924 : Nat := 118140960795 + 3694924 * 2 ^ 59
def prefixEnd_3694924 : Nat := 4983230072969 + 3 ^ 40 * 3694924 * 2
def baseEnd_3694924 : Nat := 140538666209881987152397

theorem tailTrace_3694924 : CollatzResearch.WordTrace tailWord_3694924 prefixEnd_3694924 140538666209881987152397 := by
  unfold tailWord_3694924
  simp only [CollatzResearch.WordTrace]
  refine ⟨67382474832964432812213913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89843299777285910416285217 67382474832964432812213913)
  ·
    refine ⟨50536856124723324609160435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67382474832964432812213913 50536856124723324609160435)
    ·
      refine ⟨75805284187084986913740653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50536856124723324609160435 75805284187084986913740653)
      ·
        refine ⟨28426981570156870092652745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75805284187084986913740653 28426981570156870092652745)
        ·
          refine ⟨21320236177617652569489559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28426981570156870092652745 21320236177617652569489559)
          ·
            refine ⟨31980354266426478854234339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21320236177617652569489559 31980354266426478854234339)
            ·
              refine ⟨47970531399639718281351509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31980354266426478854234339 47970531399639718281351509)
              ·
                refine ⟨140538666209881987152397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47970531399639718281351509 140538666209881987152397)
                ·
                  rfl

theorem cell22_3694924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 10].length) (baseStart_3694924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694924 prefixEnd_3694924 := by exact prefixLift 3694924
  have htrace : WordTrace (prefixWord ++ tailWord_3694924) baseStart_3694924 baseEnd_3694924 := by
    simpa [prefixWord, tailWord_3694924, baseEnd_3694924] using wordTrace_append hprefix tailTrace_3694924
  have hstable : (prefixWord ++ tailWord_3694924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694924).length < 2 ^ (prefixWord ++ tailWord_3694924).sum := by decide
  have hdescent : baseEnd_3694924 < baseStart_3694924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694941 : List Nat := [1, 4, 5, 12]
def baseStart_3694941 : Nat := 118140960795 + 3694941 * 2 ^ 59
def prefixEnd_3694941 : Nat := 4983230072969 + 3 ^ 40 * 3694941 * 2
def baseEnd_3694941 : Nat := 1735053244631489035249

theorem tailTrace_3694941 : CollatzResearch.WordTrace tailWord_3694941 prefixEnd_3694941 1735053244631489035249 := by
  unfold tailWord_3694941
  simp only [CollatzResearch.WordTrace]
  refine ⟨134765569706867277527796677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89843713137911518351864451 134765569706867277527796677)
  ·
    refine ⟨25268544320037614536461877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134765569706867277527796677 25268544320037614536461877)
    ·
      refine ⟨2368926030003526362793301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25268544320037614536461877 2368926030003526362793301)
      ·
        refine ⟨1735053244631489035249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2368926030003526362793301 1735053244631489035249)
        ·
          rfl

theorem cell22_3694941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 12].length) (baseStart_3694941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694941 prefixEnd_3694941 := by exact prefixLift 3694941
  have htrace : WordTrace (prefixWord ++ tailWord_3694941) baseStart_3694941 baseEnd_3694941 := by
    simpa [prefixWord, tailWord_3694941, baseEnd_3694941] using wordTrace_append hprefix tailTrace_3694941
  have hstable : (prefixWord ++ tailWord_3694941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694941).length < 2 ^ (prefixWord ++ tailWord_3694941).sum := by decide
  have hdescent : baseEnd_3694941 < baseStart_3694941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694969 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 9]
def baseStart_3694969 : Nat := 118140960795 + 3694969 * 2 ^ 59
def prefixEnd_3694969 : Nat := 4983230072969 + 3 ^ 40 * 3694969 * 2
def baseEnd_3694969 : Nat := 421621133436190922332145

theorem tailTrace_3694969 : CollatzResearch.WordTrace tailWord_3694969 prefixEnd_3694969 421621133436190922332145 := by
  unfold tailWord_3694969
  simp only [CollatzResearch.WordTrace]
  refine ⟨134766590950765838309815961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89844393967177225539877307 134766590950765838309815961)
  ·
    refine ⟨101074943213074378732361971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134766590950765838309815961 101074943213074378732361971)
    ·
      refine ⟨151612414819611568098542957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101074943213074378732361971 151612414819611568098542957)
      ·
        refine ⟨56854655557354338036953609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151612414819611568098542957 56854655557354338036953609)
        ·
          refine ⟨42640991668015753527715207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56854655557354338036953609 42640991668015753527715207)
          ·
            refine ⟨63961487502023630291572811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42640991668015753527715207 63961487502023630291572811)
            ·
              refine ⟨95942231253035445437359217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63961487502023630291572811 95942231253035445437359217)
              ·
                refine ⟨71956673439776584078019413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95942231253035445437359217 71956673439776584078019413)
                ·
                  refine ⟨421621133436190922332145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71956673439776584078019413 421621133436190922332145)
                  ·
                    rfl

theorem cell22_3694969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_3694969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694969 prefixEnd_3694969 := by exact prefixLift 3694969
  have htrace : WordTrace (prefixWord ++ tailWord_3694969) baseStart_3694969 baseEnd_3694969 := by
    simpa [prefixWord, tailWord_3694969, baseEnd_3694969] using wordTrace_append hprefix tailTrace_3694969
  have hstable : (prefixWord ++ tailWord_3694969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694969).length < 2 ^ (prefixWord ++ tailWord_3694969).sum := by decide
  have hdescent : baseEnd_3694969 < baseStart_3694969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3694973 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_3694973 : Nat := 118140960795 + 3694973 * 2 ^ 59
def prefixEnd_3694973 : Nat := 4983230072969 + 3 ^ 40 * 3694973 * 2
def baseEnd_3694973 : Nat := 1264864769590318089896423

theorem tailTrace_3694973 : CollatzResearch.WordTrace tailWord_3694973 prefixEnd_3694973 1264864769590318089896423 := by
  unfold tailWord_3694973
  simp only [CollatzResearch.WordTrace]
  refine ⟨134766736842751346992961573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89844491228500897995307715 134766736842751346992961573)
  ·
    refine ⟨25268763158015877561180295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134766736842751346992961573 25268763158015877561180295)
    ·
      refine ⟨37903144737023816341770443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25268763158015877561180295 37903144737023816341770443)
      ·
        refine ⟨56854717105535724512655665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37903144737023816341770443 56854717105535724512655665)
        ·
          refine ⟨42641037829151793384491749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56854717105535724512655665 42641037829151793384491749)
          ·
            refine ⟨7995194592965961259592203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42641037829151793384491749 7995194592965961259592203)
            ·
              refine ⟨11992791889448941889388305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7995194592965961259592203 11992791889448941889388305)
              ·
                refine ⟨8994593917086706417041229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11992791889448941889388305 8994593917086706417041229)
                ·
                  refine ⟨3372972718907514906390461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8994593917086706417041229 3372972718907514906390461)
                  ·
                    refine ⟨1264864769590318089896423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3372972718907514906390461 1264864769590318089896423)
                    ·
                      rfl

theorem cell22_3694973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_3694973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3694973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3694973 prefixEnd_3694973 := by exact prefixLift 3694973
  have htrace : WordTrace (prefixWord ++ tailWord_3694973) baseStart_3694973 baseEnd_3694973 := by
    simpa [prefixWord, tailWord_3694973, baseEnd_3694973] using wordTrace_append hprefix tailTrace_3694973
  have hstable : (prefixWord ++ tailWord_3694973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3694973).length < 2 ^ (prefixWord ++ tailWord_3694973).sum := by decide
  have hdescent : baseEnd_3694973 < baseStart_3694973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3694973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695031 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 6]
def baseStart_3695031 : Nat := 118140960795 + 3695031 * 2 ^ 59
def prefixEnd_3695031 : Nat := 4983230072969 + 3 ^ 40 * 3695031 * 2
def baseEnd_3695031 : Nat := 421628208058541757315415

theorem tailTrace_3695031 : CollatzResearch.WordTrace tailWord_3695031 prefixEnd_3695031 421628208058541757315415 := by
  unfold tailWord_3695031
  simp only [CollatzResearch.WordTrace]
  refine ⟨134768852276541222898572947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89845901517694148599048631 134768852276541222898572947)
  ·
    refine ⟨202153278414811834347859421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134768852276541222898572947 202153278414811834347859421)
    ·
      refine ⟨75807479405554437880447283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202153278414811834347859421 75807479405554437880447283)
      ·
        refine ⟨113711219108331656820670925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75807479405554437880447283 113711219108331656820670925)
        ·
          refine ⟨42641707165624371307751597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113711219108331656820670925 42641707165624371307751597)
          ·
            refine ⟨15990640187109139240406849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42641707165624371307751597 15990640187109139240406849)
            ·
              refine ⟨11992980140331854430305137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15990640187109139240406849 11992980140331854430305137)
              ·
                refine ⟨8994735105248890822728853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11992980140331854430305137 8994735105248890822728853)
                ·
                  refine ⟨421628208058541757315415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8994735105248890822728853 421628208058541757315415)
                  ·
                    rfl

theorem cell22_3695031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 6].length) (baseStart_3695031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695031 prefixEnd_3695031 := by exact prefixLift 3695031
  have htrace : WordTrace (prefixWord ++ tailWord_3695031) baseStart_3695031 baseEnd_3695031 := by
    simpa [prefixWord, tailWord_3695031, baseEnd_3695031] using wordTrace_append hprefix tailTrace_3695031
  have hstable : (prefixWord ++ tailWord_3695031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695031).length < 2 ^ (prefixWord ++ tailWord_3695031).sum := by decide
  have hdescent : baseEnd_3695031 < baseStart_3695031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695033 : List Nat := [1, 2, 1, 4, 3, 1, 1, 4, 1, 4]
def baseStart_3695033 : Nat := 118140960795 + 3695033 * 2 ^ 59
def prefixEnd_3695033 : Nat := 4983230072969 + 3 ^ 40 * 3695033 * 2
def baseEnd_3695033 : Nat := 1264885308816497933396239

theorem tailTrace_3695033 : CollatzResearch.WordTrace tailWord_3695033 prefixEnd_3695033 1264885308816497933396239 := by
  unfold tailWord_3695033
  simp only [CollatzResearch.WordTrace]
  refine ⟨134768925222533977240145753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89845950148355984826763835 134768925222533977240145753)
  ·
    refine ⟨101076693916900482930109315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134768925222533977240145753 101076693916900482930109315)
    ·
      refine ⟨151615040875350724395163973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101076693916900482930109315 151615040875350724395163973)
      ·
        refine ⟨28427820164128260824093245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151615040875350724395163973 28427820164128260824093245)
        ·
          refine ⟨10660432561548097809034967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28427820164128260824093245 10660432561548097809034967)
          ·
            refine ⟨15990648842322146713552451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10660432561548097809034967 15990648842322146713552451)
            ·
              refine ⟨23985973263483220070328677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15990648842322146713552451 23985973263483220070328677)
              ·
                refine ⟨4497369986903103763186627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23985973263483220070328677 4497369986903103763186627)
                ·
                  refine ⟨6746054980354655644779941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497369986903103763186627 6746054980354655644779941)
                  ·
                    refine ⟨1264885308816497933396239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6746054980354655644779941 1264885308816497933396239)
                    ·
                      rfl

theorem cell22_3695033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_3695033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695033 prefixEnd_3695033 := by exact prefixLift 3695033
  have htrace : WordTrace (prefixWord ++ tailWord_3695033) baseStart_3695033 baseEnd_3695033 := by
    simpa [prefixWord, tailWord_3695033, baseEnd_3695033] using wordTrace_append hprefix tailTrace_3695033
  have hstable : (prefixWord ++ tailWord_3695033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695033).length < 2 ^ (prefixWord ++ tailWord_3695033).sum := by decide
  have hdescent : baseEnd_3695033 < baseStart_3695033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695065 : List Nat := [1, 2, 1, 2, 4, 1, 5, 2, 4]
def baseStart_3695065 : Nat := 118140960795 + 3695065 * 2 ^ 59
def prefixEnd_3695065 : Nat := 4983230072969 + 3 ^ 40 * 3695065 * 2
def baseEnd_3695065 : Nat := 421632087690153505532047

theorem tailTrace_3695065 : CollatzResearch.WordTrace tailWord_3695065 prefixEnd_3695065 421632087690153505532047 := by
  unfold tailWord_3695065
  simp only [CollatzResearch.WordTrace]
  refine ⟨134770092358418046705310649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89846728238945364470207099 134770092358418046705310649)
  ·
    refine ⟨101077569268813535028982987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134770092358418046705310649 101077569268813535028982987)
    ·
      refine ⟨151616353903220302543474481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101077569268813535028982987 151616353903220302543474481)
      ·
        refine ⟨113712265427415226907605861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151616353903220302543474481 113712265427415226907605861)
        ·
          refine ⟨21321049767640355045176099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113712265427415226907605861 21321049767640355045176099)
          ·
            refine ⟨31981574651460532567764149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21321049767640355045176099 31981574651460532567764149)
            ·
              refine ⟨2998272623574424928227889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31981574651460532567764149 2998272623574424928227889)
              ·
                refine ⟨2248704467680818696170917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2998272623574424928227889 2248704467680818696170917)
                ·
                  refine ⟨421632087690153505532047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2248704467680818696170917 421632087690153505532047)
                  ·
                    rfl

theorem cell22_3695065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 4].length) (baseStart_3695065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695065 prefixEnd_3695065 := by exact prefixLift 3695065
  have htrace : WordTrace (prefixWord ++ tailWord_3695065) baseStart_3695065 baseEnd_3695065 := by
    simpa [prefixWord, tailWord_3695065, baseEnd_3695065] using wordTrace_append hprefix tailTrace_3695065
  have hstable : (prefixWord ++ tailWord_3695065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695065).length < 2 ^ (prefixWord ++ tailWord_3695065).sum := by decide
  have hdescent : baseEnd_3695065 < baseStart_3695065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695080 : List Nat := [2, 1, 4, 1, 1, 4, 1, 3, 2, 3]
def baseStart_3695080 : Nat := 118140960795 + 3695080 * 2 ^ 59
def prefixEnd_3695080 : Nat := 4983230072969 + 3 ^ 40 * 3695080 * 2
def baseEnd_3695080 : Nat := 1264901397877005477471095

theorem tailTrace_3695080 : CollatzResearch.WordTrace tailWord_3695080 prefixEnd_3695080 1264901397877005477471095 := by
  unfold tailWord_3695080
  simp only [CollatzResearch.WordTrace]
  refine ⟨67385319726681852133553347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89847092968909136178071129 67385319726681852133553347)
  ·
    refine ⟨101077979590022778200330021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67385319726681852133553347 101077979590022778200330021)
    ·
      refine ⟨18952121173129270912561879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101077979590022778200330021 18952121173129270912561879)
      ·
        refine ⟨28428181759693906368842819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18952121173129270912561879 28428181759693906368842819)
        ·
          refine ⟨42642272639540859553264229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28428181759693906368842819 42642272639540859553264229)
          ·
            refine ⟨7995426119913911166237043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42642272639540859553264229 7995426119913911166237043)
            ·
              refine ⟨11993139179870866749355565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7995426119913911166237043 11993139179870866749355565)
              ·
                refine ⟨4497427192451575031008337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11993139179870866749355565 4497427192451575031008337)
                ·
                  refine ⟨3373070394338681273256253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4497427192451575031008337 3373070394338681273256253)
                  ·
                    refine ⟨1264901397877005477471095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3373070394338681273256253 1264901397877005477471095)
                    ·
                      rfl

theorem cell22_3695080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_3695080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695080 prefixEnd_3695080 := by exact prefixLift 3695080
  have htrace : WordTrace (prefixWord ++ tailWord_3695080) baseStart_3695080 baseEnd_3695080 := by
    simpa [prefixWord, tailWord_3695080, baseEnd_3695080] using wordTrace_append hprefix tailTrace_3695080
  have hstable : (prefixWord ++ tailWord_3695080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695080).length < 2 ^ (prefixWord ++ tailWord_3695080).sum := by decide
  have hdescent : baseEnd_3695080 < baseStart_3695080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695127 : List Nat := [1, 1, 3, 6, 2, 1, 1, 7]
def baseStart_3695127 : Nat := 118140960795 + 3695127 * 2 ^ 59
def prefixEnd_3695127 : Nat := 4983230072969 + 3 ^ 40 * 3695127 * 2
def baseEnd_3695127 : Nat := 140546387437501446838439

theorem tailTrace_3695127 : CollatzResearch.WordTrace tailWord_3695127 prefixEnd_3695127 140546387437501446838439 := by
  unfold tailWord_3695127
  simp only [CollatzResearch.WordTrace]
  refine ⟨134772353684193431294067635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89848235789462287529378423 134772353684193431294067635)
  ·
    refine ⟨202158530526290146941101453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134772353684193431294067635 202158530526290146941101453)
    ·
      refine ⟨75809448947358805102913045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202158530526290146941101453 75809448947358805102913045)
      ·
        refine ⟨3553567919407443989199049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75809448947358805102913045 3553567919407443989199049)
        ·
          refine ⟨2665175939555582991899287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3553567919407443989199049 2665175939555582991899287)
          ·
            refine ⟨3997763909333374487848931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2665175939555582991899287 3997763909333374487848931)
            ·
              refine ⟨5996645864000061731773397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3997763909333374487848931 5996645864000061731773397)
              ·
                refine ⟨140546387437501446838439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5996645864000061731773397 140546387437501446838439)
                ·
                  rfl

theorem cell22_3695127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 7].length) (baseStart_3695127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695127 prefixEnd_3695127 := by exact prefixLift 3695127
  have htrace : WordTrace (prefixWord ++ tailWord_3695127) baseStart_3695127 baseEnd_3695127 := by
    simpa [prefixWord, tailWord_3695127, baseEnd_3695127] using wordTrace_append hprefix tailTrace_3695127
  have hstable : (prefixWord ++ tailWord_3695127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695127).length < 2 ^ (prefixWord ++ tailWord_3695127).sum := by decide
  have hdescent : baseEnd_3695127 < baseStart_3695127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695290 : List Nat := [3, 1, 1, 1, 2, 3, 4, 2, 5]
def baseStart_3695290 : Nat := 118140960795 + 3695290 * 2 ^ 59
def prefixEnd_3695290 : Nat := 4983230072969 + 3 ^ 40 * 3695290 * 2
def baseEnd_3695290 : Nat := 421657761722878309906817

theorem tailTrace_3695290 : CollatzResearch.WordTrace tailWord_3695290 prefixEnd_3695290 421657761722878309906817 := by
  unfold tailWord_3695290
  simp only [CollatzResearch.WordTrace]
  refine ⟨33694574695650727533062831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89852199188401940088167549 33694574695650727533062831)
  ·
    refine ⟨50541862043476091299594247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33694574695650727533062831 50541862043476091299594247)
    ·
      refine ⟨75812793065214136949391371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50541862043476091299594247 75812793065214136949391371)
      ·
        refine ⟨113719189597821205424087057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75812793065214136949391371 113719189597821205424087057)
        ·
          refine ⟨85289392198365904068065293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113719189597821205424087057 85289392198365904068065293)
          ·
            refine ⟨31983522074387214025524485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85289392198365904068065293 31983522074387214025524485)
            ·
              refine ⟨5996910388947602629785841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31983522074387214025524485 5996910388947602629785841)
              ·
                refine ⟨4497682791710701972339381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5996910388947602629785841 4497682791710701972339381)
                ·
                  refine ⟨421657761722878309906817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4497682791710701972339381 421657761722878309906817)
                  ·
                    rfl

theorem cell22_3695290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_3695290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695290 prefixEnd_3695290 := by exact prefixLift 3695290
  have htrace : WordTrace (prefixWord ++ tailWord_3695290) baseStart_3695290 baseEnd_3695290 := by
    simpa [prefixWord, tailWord_3695290, baseEnd_3695290] using wordTrace_append hprefix tailTrace_3695290
  have hstable : (prefixWord ++ tailWord_3695290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695290).length < 2 ^ (prefixWord ++ tailWord_3695290).sum := by decide
  have hdescent : baseEnd_3695290 < baseStart_3695290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695294 : List Nat := [4, 2, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_3695294 : Nat := 118140960795 + 3695294 * 2 ^ 59
def prefixEnd_3695294 : Nat := 4983230072969 + 3 ^ 40 * 3695294 * 2
def baseEnd_3695294 : Nat := 1264974654450380252620439

theorem tailTrace_3695294 : CollatzResearch.WordTrace tailWord_3695294 prefixEnd_3695294 1264974654450380252620439 := by
  unfold tailWord_3695294
  simp only [CollatzResearch.WordTrace]
  refine ⟨16847305584323552351924617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89852296449725612543597957 16847305584323552351924617)
  ·
    refine ⟨12635479188242664263943463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16847305584323552351924617 12635479188242664263943463)
    ·
      refine ⟨18953218782363996395915195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12635479188242664263943463 18953218782363996395915195)
      ·
        refine ⟨28429828173545994593872793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18953218782363996395915195 28429828173545994593872793)
        ·
          refine ⟨21322371130159495945404595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28429828173545994593872793 21322371130159495945404595)
          ·
            refine ⟨31983556695239243918106893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21322371130159495945404595 31983556695239243918106893)
            ·
              refine ⟨11993833760714716469290085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31983556695239243918106893 11993833760714716469290085)
              ·
                refine ⟨2248843830134009337991891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11993833760714716469290085 2248843830134009337991891)
                ·
                  refine ⟨3373265745201014006987837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248843830134009337991891 3373265745201014006987837)
                  ·
                    refine ⟨1264974654450380252620439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3373265745201014006987837 1264974654450380252620439)
                    ·
                      rfl

theorem cell22_3695294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_3695294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695294 prefixEnd_3695294 := by exact prefixLift 3695294
  have htrace : WordTrace (prefixWord ++ tailWord_3695294) baseStart_3695294 baseEnd_3695294 := by
    simpa [prefixWord, tailWord_3695294, baseEnd_3695294] using wordTrace_append hprefix tailTrace_3695294
  have hstable : (prefixWord ++ tailWord_3695294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695294).length < 2 ^ (prefixWord ++ tailWord_3695294).sum := by decide
  have hdescent : baseEnd_3695294 < baseStart_3695294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695320 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 3, 4]
def baseStart_3695320 : Nat := 118140960795 + 3695320 * 2 ^ 59
def prefixEnd_3695320 : Nat := 4983230072969 + 3 ^ 40 * 3695320 * 2
def baseEnd_3695320 : Nat := 1264983554781724851470359

theorem tailTrace_3695320 : CollatzResearch.WordTrace tailWord_3695320 prefixEnd_3695320 1264983554781724851470359 := by
  unfold tailWord_3695320
  simp only [CollatzResearch.WordTrace]
  refine ⟨67389696486247112627921707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89852928648329483503895609 67389696486247112627921707)
  ·
    refine ⟨101084544729370668941882561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67389696486247112627921707 101084544729370668941882561)
    ·
      refine ⟨75813408547028001706411921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101084544729370668941882561 75813408547028001706411921)
      ·
        refine ⟨56860056410271001279808941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75813408547028001706411921 56860056410271001279808941)
        ·
          refine ⟨21322521153851625479928353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56860056410271001279808941 21322521153851625479928353)
          ·
            refine ⟨15991890865388719109946265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21322521153851625479928353 15991890865388719109946265)
            ·
              refine ⟨11993918149041539332459699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15991890865388719109946265 11993918149041539332459699)
              ·
                refine ⟨17990877223562308998689549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11993918149041539332459699 17990877223562308998689549)
                ·
                  refine ⟨6746578958835865874508581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17990877223562308998689549 6746578958835865874508581)
                  ·
                    refine ⟨1264983554781724851470359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6746578958835865874508581 1264983554781724851470359)
                    ·
                      rfl

theorem cell22_3695320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_3695320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695320 prefixEnd_3695320 := by exact prefixLift 3695320
  have htrace : WordTrace (prefixWord ++ tailWord_3695320) baseStart_3695320 baseEnd_3695320 := by
    simpa [prefixWord, tailWord_3695320, baseEnd_3695320] using wordTrace_append hprefix tailTrace_3695320
  have hstable : (prefixWord ++ tailWord_3695320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695320).length < 2 ^ (prefixWord ++ tailWord_3695320).sum := by decide
  have hdescent : baseEnd_3695320 < baseStart_3695320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695337 : List Nat := [1, 2, 1, 1, 1, 2, 8, 1, 1, 4]
def baseStart_3695337 : Nat := 118140960795 + 3695337 * 2 ^ 59
def prefixEnd_3695337 : Nat := 4983230072969 + 3 ^ 40 * 3695337 * 2
def baseEnd_3695337 : Nat := 1264989374229142473795307

theorem tailTrace_3695337 : CollatzResearch.WordTrace tailWord_3695337 prefixEnd_3695337 1264989374229142473795307 := by
  unfold tailWord_3695337
  simp only [CollatzResearch.WordTrace]
  refine ⟨134780013013432637159212265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89853342008955091439474843 134780013013432637159212265)
  ·
    refine ⟨101085009760074477869409199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134780013013432637159212265 101085009760074477869409199)
    ·
      refine ⟨151627514640111716804113799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101085009760074477869409199 151627514640111716804113799)
      ·
        refine ⟨227441271960167575206170699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151627514640111716804113799 227441271960167575206170699)
        ·
          refine ⟨341161907940251362809256049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227441271960167575206170699 341161907940251362809256049)
          ·
            refine ⟨255871430955188522106942037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 341161907940251362809256049 255871430955188522106942037)
            ·
              refine ⟨2998493331506115493440727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 255871430955188522106942037 2998493331506115493440727)
              ·
                refine ⟨4497739997259173240161091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998493331506115493440727 4497739997259173240161091)
                ·
                  refine ⟨6746609995888759860241637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497739997259173240161091 6746609995888759860241637)
                  ·
                    refine ⟨1264989374229142473795307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6746609995888759860241637 1264989374229142473795307)
                    ·
                      rfl

theorem cell22_3695337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 1, 4].length) (baseStart_3695337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695337 prefixEnd_3695337 := by exact prefixLift 3695337
  have htrace : WordTrace (prefixWord ++ tailWord_3695337) baseStart_3695337 baseEnd_3695337 := by
    simpa [prefixWord, tailWord_3695337, baseEnd_3695337] using wordTrace_append hprefix tailTrace_3695337
  have hstable : (prefixWord ++ tailWord_3695337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695337).length < 2 ^ (prefixWord ++ tailWord_3695337).sum := by decide
  have hdescent : baseEnd_3695337 < baseStart_3695337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695363 : List Nat := [1, 1, 1, 3, 2, 2, 1, 11]
def baseStart_3695363 : Nat := 118140960795 + 3695363 * 2 ^ 59
def prefixEnd_3695363 : Nat := 4983230072969 + 3 ^ 40 * 3695363 * 2
def baseEnd_3695363 : Nat := 140555363840054119182803

theorem tailTrace_3695363 : CollatzResearch.WordTrace tailWord_3695363 prefixEnd_3695363 140555363840054119182803 := by
  unfold tailWord_3695363
  simp only [CollatzResearch.WordTrace]
  refine ⟨134780961311338443599658743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89853974207558962399772495 134780961311338443599658743)
  ·
    refine ⟨202171441967007665399488115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134780961311338443599658743 202171441967007665399488115)
    ·
      refine ⟨303257162950511498099232173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202171441967007665399488115 303257162950511498099232173)
      ·
        refine ⟨113721436106441811787212065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303257162950511498099232173 113721436106441811787212065)
        ·
          refine ⟨85291077079831358840409049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113721436106441811787212065 85291077079831358840409049)
          ·
            refine ⟨63968307809873519130306787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85291077079831358840409049 63968307809873519130306787)
            ·
              refine ⟨95952461714810278695460181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63968307809873519130306787 95952461714810278695460181)
              ·
                refine ⟨140555363840054119182803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 95952461714810278695460181 140555363840054119182803)
                ·
                  rfl

theorem cell22_3695363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 11].length) (baseStart_3695363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695363 prefixEnd_3695363 := by exact prefixLift 3695363
  have htrace : WordTrace (prefixWord ++ tailWord_3695363) baseStart_3695363 baseEnd_3695363 := by
    simpa [prefixWord, tailWord_3695363, baseEnd_3695363] using wordTrace_append hprefix tailTrace_3695363
  have hstable : (prefixWord ++ tailWord_3695363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695363).length < 2 ^ (prefixWord ++ tailWord_3695363).sum := by decide
  have hdescent : baseEnd_3695363 < baseStart_3695363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695367 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 1, 5]
def baseStart_3695367 : Nat := 118140960795 + 3695367 * 2 ^ 59
def prefixEnd_3695367 : Nat := 4983230072969 + 3 ^ 40 * 3695367 * 2
def baseEnd_3695367 : Nat := 1264999643842232395545215

theorem tailTrace_3695367 : CollatzResearch.WordTrace tailWord_3695367 prefixEnd_3695367 1264999643842232395545215 := by
  unfold tailWord_3695367
  simp only [CollatzResearch.WordTrace]
  refine ⟨134781107203323952282804355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89854071468882634855202903 134781107203323952282804355)
  ·
    refine ⟨202171660804985928424206533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134781107203323952282804355 202171660804985928424206533)
    ·
      refine ⟨37907186400934861579538725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202171660804985928424206533 37907186400934861579538725)
      ·
        refine ⟨7107597450175286546163511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37907186400934861579538725 7107597450175286546163511)
        ·
          refine ⟨10661396175262929819245267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7107597450175286546163511 10661396175262929819245267)
          ·
            refine ⟨15992094262894394728867901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10661396175262929819245267 15992094262894394728867901)
            ·
              refine ⟨5997035348585398023325463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15992094262894394728867901 5997035348585398023325463)
              ·
                refine ⟨8995553022878097034988195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5997035348585398023325463 8995553022878097034988195)
                ·
                  refine ⟨13493329534317145552482293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8995553022878097034988195 13493329534317145552482293)
                  ·
                    refine ⟨1264999643842232395545215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13493329534317145552482293 1264999643842232395545215)
                    ·
                      rfl

theorem cell22_3695367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_3695367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695367 prefixEnd_3695367 := by exact prefixLift 3695367
  have htrace : WordTrace (prefixWord ++ tailWord_3695367) baseStart_3695367 baseEnd_3695367 := by
    simpa [prefixWord, tailWord_3695367, baseEnd_3695367] using wordTrace_append hprefix tailTrace_3695367
  have hstable : (prefixWord ++ tailWord_3695367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695367).length < 2 ^ (prefixWord ++ tailWord_3695367).sum := by decide
  have hdescent : baseEnd_3695367 < baseStart_3695367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695410 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_3695410 : Nat := 118140960795 + 3695410 * 2 ^ 59
def prefixEnd_3695410 : Nat := 4983230072969 + 3 ^ 40 * 3695410 * 2
def baseEnd_3695410 : Nat := 1265014363620994616720083

theorem tailTrace_3695410 : CollatzResearch.WordTrace tailWord_3695410 prefixEnd_3695410 1265014363620994616720083 := by
  unfold tailWord_3695410
  simp only [CollatzResearch.WordTrace]
  refine ⟨33695668885542042656654921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89855117028112113751079789 33695668885542042656654921)
  ·
    refine ⟨25271751664156531992491191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33695668885542042656654921 25271751664156531992491191)
    ·
      refine ⟨37907627496234797988736787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25271751664156531992491191 37907627496234797988736787)
      ·
        refine ⟨56861441244352196983105181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37907627496234797988736787 56861441244352196983105181)
        ·
          refine ⟨21323040466632073868664443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56861441244352196983105181 21323040466632073868664443)
          ·
            refine ⟨31984560699948110802996665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21323040466632073868664443 31984560699948110802996665)
            ·
              refine ⟨23988420524961083102247499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31984560699948110802996665 23988420524961083102247499)
              ·
                refine ⟨35982630787441624653371249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23988420524961083102247499 35982630787441624653371249)
                ·
                  refine ⟨26986973090581218490028437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35982630787441624653371249 26986973090581218490028437)
                  ·
                    refine ⟨1265014363620994616720083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26986973090581218490028437 1265014363620994616720083)
                    ·
                      rfl

theorem cell22_3695410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_3695410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695410 prefixEnd_3695410 := by exact prefixLift 3695410
  have htrace : WordTrace (prefixWord ++ tailWord_3695410) baseStart_3695410 baseEnd_3695410 := by
    simpa [prefixWord, tailWord_3695410, baseEnd_3695410] using wordTrace_append hprefix tailTrace_3695410
  have hstable : (prefixWord ++ tailWord_3695410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695410).length < 2 ^ (prefixWord ++ tailWord_3695410).sum := by decide
  have hdescent : baseEnd_3695410 < baseStart_3695410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695414 : List Nat := [5, 1, 2, 2, 2, 1, 2, 7]
def baseStart_3695414 : Nat := 118140960795 + 3695414 * 2 ^ 59
def prefixEnd_3695414 : Nat := 4983230072969 + 3 ^ 40 * 3695414 * 2
def baseEnd_3695414 : Nat := 140557303655859993291119

theorem tailTrace_3695414 : CollatzResearch.WordTrace tailWord_3695414 prefixEnd_3695414 140557303655859993291119 := by
  unfold tailWord_3695414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8423926339634604956860331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89855214289435786206510197 8423926339634604956860331)
  ·
    refine ⟨12635889509451907435290497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8423926339634604956860331 12635889509451907435290497)
    ·
      refine ⟨9476917132088930576467873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12635889509451907435290497 9476917132088930576467873)
      ·
        refine ⟨7107687849066697932350905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9476917132088930576467873 7107687849066697932350905)
        ·
          refine ⟨5330765886800023449263179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7107687849066697932350905 5330765886800023449263179)
          ·
            refine ⟨7996148830200035173894769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5330765886800023449263179 7996148830200035173894769)
            ·
              refine ⟨5997111622650026380421077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7996148830200035173894769 5997111622650026380421077)
              ·
                refine ⟨140557303655859993291119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5997111622650026380421077 140557303655859993291119)
                ·
                  rfl

theorem cell22_3695414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_3695414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695414 prefixEnd_3695414 := by exact prefixLift 3695414
  have htrace : WordTrace (prefixWord ++ tailWord_3695414) baseStart_3695414 baseEnd_3695414 := by
    simpa [prefixWord, tailWord_3695414, baseEnd_3695414] using wordTrace_append hprefix tailTrace_3695414
  have hstable : (prefixWord ++ tailWord_3695414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695414).length < 2 ^ (prefixWord ++ tailWord_3695414).sum := by decide
  have hdescent : baseEnd_3695414 < baseStart_3695414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695418 : List Nat := [3, 1, 1, 1, 7, 1, 2, 1, 2, 3]
def baseStart_3695418 : Nat := 118140960795 + 3695418 * 2 ^ 59
def prefixEnd_3695418 : Nat := 4983230072969 + 3 ^ 40 * 3695418 * 2
def baseEnd_3695418 : Nat := 1265017102184485262520059

theorem tailTrace_3695418 : CollatzResearch.WordTrace tailWord_3695418 prefixEnd_3695418 1265017102184485262520059 := by
  unfold tailWord_3695418
  simp only [CollatzResearch.WordTrace]
  refine ⟨33695741831534796998227727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89855311550759458661940605 33695741831534796998227727)
  ·
    refine ⟨50543612747302195497341591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33695741831534796998227727 50543612747302195497341591)
    ·
      refine ⟨75815419120953293246012387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50543612747302195497341591 75815419120953293246012387)
      ·
        refine ⟨113723128681429939869018581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75815419120953293246012387 113723128681429939869018581)
        ·
          refine ⟨2665385828471014215680123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 113723128681429939869018581 2665385828471014215680123)
          ·
            refine ⟨3998078742706521323520185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2665385828471014215680123 3998078742706521323520185)
            ·
              refine ⟨2998559057029890992640139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3998078742706521323520185 2998559057029890992640139)
              ·
                refine ⟨4497838585544836488960209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2998559057029890992640139 4497838585544836488960209)
                ·
                  refine ⟨3373378939158627366720157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4497838585544836488960209 3373378939158627366720157)
                  ·
                    refine ⟨1265017102184485262520059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3373378939158627366720157 1265017102184485262520059)
                    ·
                      rfl

theorem cell22_3695418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_3695418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695418 prefixEnd_3695418 := by exact prefixLift 3695418
  have htrace : WordTrace (prefixWord ++ tailWord_3695418) baseStart_3695418 baseEnd_3695418 := by
    simpa [prefixWord, tailWord_3695418, baseEnd_3695418] using wordTrace_append hprefix tailTrace_3695418
  have hstable : (prefixWord ++ tailWord_3695418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695418).length < 2 ^ (prefixWord ++ tailWord_3695418).sum := by decide
  have hdescent : baseEnd_3695418 < baseStart_3695418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695463 : List Nat := [1, 1, 5, 1, 2, 4, 2, 2, 1, 3]
def baseStart_3695463 : Nat := 118140960795 + 3695463 * 2 ^ 59
def prefixEnd_3695463 : Nat := 4983230072969 + 3 ^ 40 * 3695463 * 2
def baseEnd_3695463 : Nat := 1265032506604120145144921

theorem tailTrace_3695463 : CollatzResearch.WordTrace tailWord_3695463 prefixEnd_3695463 1265032506604120145144921 := by
  unfold tailWord_3695463
  simp only [CollatzResearch.WordTrace]
  refine ⟨134784608610976160678299043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89856405740650773785532695 134784608610976160678299043)
  ·
    refine ⟨202176912916464241017448565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134784608610976160678299043 202176912916464241017448565)
    ·
      refine ⟨18954085585918522595385803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202176912916464241017448565 18954085585918522595385803)
      ·
        refine ⟨28431128378877783893078705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18954085585918522595385803 28431128378877783893078705)
        ·
          refine ⟨21323346284158337919809029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28431128378877783893078705 21323346284158337919809029)
          ·
            refine ⟨3998127428279688359964193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21323346284158337919809029 3998127428279688359964193)
            ·
              refine ⟨2998595571209766269973145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3998127428279688359964193 2998595571209766269973145)
              ·
                refine ⟨2248946678407324702479859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2998595571209766269973145 2248946678407324702479859)
                ·
                  refine ⟨3373420017610987053719789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2248946678407324702479859 3373420017610987053719789)
                  ·
                    refine ⟨1265032506604120145144921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3373420017610987053719789 1265032506604120145144921)
                    ·
                      rfl

theorem cell22_3695463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_3695463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695463 prefixEnd_3695463 := by exact prefixLift 3695463
  have htrace : WordTrace (prefixWord ++ tailWord_3695463) baseStart_3695463 baseEnd_3695463 := by
    simpa [prefixWord, tailWord_3695463, baseEnd_3695463] using wordTrace_append hprefix tailTrace_3695463
  have hstable : (prefixWord ++ tailWord_3695463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695463).length < 2 ^ (prefixWord ++ tailWord_3695463).sum := by decide
  have hdescent : baseEnd_3695463 < baseStart_3695463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695506 : List Nat := [3, 2, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_3695506 : Nat := 118140960795 + 3695506 * 2 ^ 59
def prefixEnd_3695506 : Nat := 4983230072969 + 3 ^ 40 * 3695506 * 2
def baseEnd_3695506 : Nat := 1265047226382882366319789

theorem tailTrace_3695506 : CollatzResearch.WordTrace tailWord_3695506 prefixEnd_3695506 1265047226382882366319789 := by
  unfold tailWord_3695506
  simp only [CollatzResearch.WordTrace]
  refine ⟨33696544237455094755528593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89857451299880252681409581 33696544237455094755528593)
  ·
    refine ⟨25272408178091321066646445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33696544237455094755528593 25272408178091321066646445)
    ·
      refine ⟨9477153066784245399992417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25272408178091321066646445 9477153066784245399992417)
      ·
        refine ⟨7107864800088184049994313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9477153066784245399992417 7107864800088184049994313)
        ·
          refine ⟨5330898600066138037495735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7107864800088184049994313 5330898600066138037495735)
          ·
            refine ⟨7996347900099207056243603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5330898600066138037495735 7996347900099207056243603)
            ·
              refine ⟨11994521850148810584365405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7996347900099207056243603 11994521850148810584365405)
              ·
                refine ⟨4497945693805803969137027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11994521850148810584365405 4497945693805803969137027)
                ·
                  refine ⟨6746918540708705953705541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4497945693805803969137027 6746918540708705953705541)
                  ·
                    refine ⟨1265047226382882366319789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6746918540708705953705541 1265047226382882366319789)
                    ·
                      rfl

theorem cell22_3695506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_3695506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695506 prefixEnd_3695506 := by exact prefixLift 3695506
  have htrace : WordTrace (prefixWord ++ tailWord_3695506) baseStart_3695506 baseEnd_3695506 := by
    simpa [prefixWord, tailWord_3695506, baseEnd_3695506] using wordTrace_append hprefix tailTrace_3695506
  have hstable : (prefixWord ++ tailWord_3695506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695506).length < 2 ^ (prefixWord ++ tailWord_3695506).sum := by decide
  have hdescent : baseEnd_3695506 < baseStart_3695506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695517 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_3695517 : Nat := 118140960795 + 3695517 * 2 ^ 59
def prefixEnd_3695517 : Nat := 4983230072969 + 3 ^ 40 * 3695517 * 2
def baseEnd_3695517 : Nat := 1265050991907682004294755

theorem tailTrace_3695517 : CollatzResearch.WordTrace tailWord_3695517 prefixEnd_3695517 1265050991907682004294755 := by
  unfold tailWord_3695517
  simp only [CollatzResearch.WordTrace]
  refine ⟨134786578152780527900764805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89857718768520351933843203 134786578152780527900764805)
  ·
    refine ⟨25272483403646348981393401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134786578152780527900764805 25272483403646348981393401)
    ·
      refine ⟨18954362552734761736045051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25272483403646348981393401 18954362552734761736045051)
      ·
        refine ⟨28431543829102142604067577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18954362552734761736045051 28431543829102142604067577)
        ·
          refine ⟨21323657871826606953050683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28431543829102142604067577 21323657871826606953050683)
          ·
            refine ⟨31985486807739910429576025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21323657871826606953050683 31985486807739910429576025)
            ·
              refine ⟨23989115105804932822182019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31985486807739910429576025 23989115105804932822182019)
              ·
                refine ⟨35983672658707399233273029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23989115105804932822182019 35983672658707399233273029)
                ·
                  refine ⟨6746938623507637356238693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35983672658707399233273029 6746938623507637356238693)
                  ·
                    refine ⟨1265050991907682004294755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6746938623507637356238693 1265050991907682004294755)
                    ·
                      rfl

theorem cell22_3695517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_3695517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695517 prefixEnd_3695517 := by exact prefixLift 3695517
  have htrace : WordTrace (prefixWord ++ tailWord_3695517) baseStart_3695517 baseEnd_3695517 := by
    simpa [prefixWord, tailWord_3695517, baseEnd_3695517] using wordTrace_append hprefix tailTrace_3695517
  have hstable : (prefixWord ++ tailWord_3695517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695517).length < 2 ^ (prefixWord ++ tailWord_3695517).sum := by decide
  have hdescent : baseEnd_3695517 < baseStart_3695517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695519 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 4, 3]
def baseStart_3695519 : Nat := 118140960795 + 3695519 * 2 ^ 59
def prefixEnd_3695519 : Nat := 4983230072969 + 3 ^ 40 * 3695519 * 2
def baseEnd_3695519 : Nat := 1265051676548554665744749

theorem tailTrace_3695519 : CollatzResearch.WordTrace tailWord_3695519 prefixEnd_3695519 1265051676548554665744749 := by
  unfold tailWord_3695519
  simp only [CollatzResearch.WordTrace]
  refine ⟨134786651098773282242337611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89857767399182188161558407 134786651098773282242337611)
  ·
    refine ⟨202179976648159923363506417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134786651098773282242337611 202179976648159923363506417)
    ·
      refine ⟨151634982486119942522629813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202179976648159923363506417 151634982486119942522629813)
      ·
        refine ⟨14215779608073744611496545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151634982486119942522629813 14215779608073744611496545)
        ·
          refine ⟨10661834706055308458622409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14215779608073744611496545 10661834706055308458622409)
          ·
            refine ⟨7996376029541481343966807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10661834706055308458622409 7996376029541481343966807)
            ·
              refine ⟨11994564044312222015950211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7996376029541481343966807 11994564044312222015950211)
              ·
                refine ⟨17991846066468333023925317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11994564044312222015950211 17991846066468333023925317)
                ·
                  refine ⟨3373471137462812441985997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17991846066468333023925317 3373471137462812441985997)
                  ·
                    refine ⟨1265051676548554665744749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3373471137462812441985997 1265051676548554665744749)
                    ·
                      rfl

theorem cell22_3695519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 3].length) (baseStart_3695519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695519 prefixEnd_3695519 := by exact prefixLift 3695519
  have htrace : WordTrace (prefixWord ++ tailWord_3695519) baseStart_3695519 baseEnd_3695519 := by
    simpa [prefixWord, tailWord_3695519, baseEnd_3695519] using wordTrace_append hprefix tailTrace_3695519
  have hstable : (prefixWord ++ tailWord_3695519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695519).length < 2 ^ (prefixWord ++ tailWord_3695519).sum := by decide
  have hdescent : baseEnd_3695519 < baseStart_3695519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695577 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 7]
def baseStart_3695577 : Nat := 118140960795 + 3695577 * 2 ^ 59
def prefixEnd_3695577 : Nat := 4983230072969 + 3 ^ 40 * 3695577 * 2
def baseEnd_3695577 : Nat := 421690510377953949264857

theorem tailTrace_3695577 : CollatzResearch.WordTrace tailWord_3695577 prefixEnd_3695577 421690510377953949264857 := by
  unfold tailWord_3695577
  simp only [CollatzResearch.WordTrace]
  refine ⟨134788766532563158147948985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89859177688375438765299323 134788766532563158147948985)
  ·
    refine ⟨101091574899422368610961739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134788766532563158147948985 101091574899422368610961739)
    ·
      refine ⟨151637362349133552916442609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101091574899422368610961739 151637362349133552916442609)
      ·
        refine ⟨113728021761850164687331957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151637362349133552916442609 113728021761850164687331957)
        ·
          refine ⟨10662002040173452939437371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113728021761850164687331957 10662002040173452939437371)
          ·
            refine ⟨15993003060260179409156057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10662002040173452939437371 15993003060260179409156057)
            ·
              refine ⟨11994752295195134556867043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15993003060260179409156057 11994752295195134556867043)
              ·
                refine ⟨17992128442792701835300565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11994752295195134556867043 17992128442792701835300565)
                ·
                  refine ⟨421690510377953949264857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17992128442792701835300565 421690510377953949264857)
                  ·
                    rfl

theorem cell22_3695577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 7].length) (baseStart_3695577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695577 prefixEnd_3695577 := by exact prefixLift 3695577
  have htrace : WordTrace (prefixWord ++ tailWord_3695577) baseStart_3695577 baseEnd_3695577 := by
    simpa [prefixWord, tailWord_3695577, baseEnd_3695577] using wordTrace_append hprefix tailTrace_3695577
  have hstable : (prefixWord ++ tailWord_3695577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695577).length < 2 ^ (prefixWord ++ tailWord_3695577).sum := by decide
  have hdescent : baseEnd_3695577 < baseStart_3695577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695581 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_3695581 : Nat := 118140960795 + 3695581 * 2 ^ 59
def prefixEnd_3695581 : Nat := 4983230072969 + 3 ^ 40 * 3695581 * 2
def baseEnd_3695581 : Nat := 1265072900415607170694559

theorem tailTrace_3695581 : CollatzResearch.WordTrace tailWord_3695581 prefixEnd_3695581 1265072900415607170694559 := by
  unfold tailWord_3695581
  simp only [CollatzResearch.WordTrace]
  refine ⟨134788912424548666831094597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89859274949699111220729731 134788912424548666831094597)
  ·
    refine ⟨25272921079602875030830237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134788912424548666831094597 25272921079602875030830237)
    ·
      refine ⟨9477345404851078136561339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25272921079602875030830237 9477345404851078136561339)
      ·
        refine ⟨14216018107276617204842009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9477345404851078136561339 14216018107276617204842009)
        ·
          refine ⟨10662013580457462903631507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14216018107276617204842009 10662013580457462903631507)
          ·
            refine ⟨15993020370686194355447261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10662013580457462903631507 15993020370686194355447261)
            ·
              refine ⟨5997382639007322883292723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15993020370686194355447261 5997382639007322883292723)
              ·
                refine ⟨8996073958510984324939085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5997382639007322883292723 8996073958510984324939085)
                ·
                  refine ⟨3373527734441619121852157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8996073958510984324939085 3373527734441619121852157)
                  ·
                    refine ⟨1265072900415607170694559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3373527734441619121852157 1265072900415607170694559)
                    ·
                      rfl

theorem cell22_3695581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_3695581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695581 prefixEnd_3695581 := by exact prefixLift 3695581
  have htrace : WordTrace (prefixWord ++ tailWord_3695581) baseStart_3695581 baseEnd_3695581 := by
    simpa [prefixWord, tailWord_3695581, baseEnd_3695581] using wordTrace_append hprefix tailTrace_3695581
  have hstable : (prefixWord ++ tailWord_3695581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695581).length < 2 ^ (prefixWord ++ tailWord_3695581).sum := by decide
  have hdescent : baseEnd_3695581 < baseStart_3695581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695592 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 2, 5]
def baseStart_3695592 : Nat := 118140960795 + 3695592 * 2 ^ 59
def prefixEnd_3695592 : Nat := 4983230072969 + 3 ^ 40 * 3695592 * 2
def baseEnd_3695592 : Nat := 1265076665940406808669525

theorem tailTrace_3695592 : CollatzResearch.WordTrace tailWord_3695592 prefixEnd_3695592 1265076665940406808669525 := by
  unfold tailWord_3695592
  simp only [CollatzResearch.WordTrace]
  refine ⟨67394656813754407854872515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89859542418339210473163353 67394656813754407854872515)
  ·
    refine ⟨101091985220631611782308773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67394656813754407854872515 101091985220631611782308773)
    ·
      refine ⟨18954747228868427209182895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101091985220631611782308773 18954747228868427209182895)
      ·
        refine ⟨28432120843302640813774343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18954747228868427209182895 28432120843302640813774343)
        ·
          refine ⟨42648181264953961220661515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28432120843302640813774343 42648181264953961220661515)
          ·
            refine ⟨63972271897430941830992273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42648181264953961220661515 63972271897430941830992273)
            ·
              refine ⟨47979203923073206373244205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63972271897430941830992273 47979203923073206373244205)
              ·
                refine ⟨17992201471152452389966577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47979203923073206373244205 17992201471152452389966577)
                ·
                  refine ⟨13494151103364339292474933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17992201471152452389966577 13494151103364339292474933)
                  ·
                    refine ⟨1265076665940406808669525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13494151103364339292474933 1265076665940406808669525)
                    ·
                      rfl

theorem cell22_3695592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_3695592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695592 prefixEnd_3695592 := by exact prefixLift 3695592
  have htrace : WordTrace (prefixWord ++ tailWord_3695592) baseStart_3695592 baseEnd_3695592 := by
    simpa [prefixWord, tailWord_3695592, baseEnd_3695592] using wordTrace_append hprefix tailTrace_3695592
  have hstable : (prefixWord ++ tailWord_3695592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695592).length < 2 ^ (prefixWord ++ tailWord_3695592).sum := by decide
  have hdescent : baseEnd_3695592 < baseStart_3695592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695594 : List Nat := [3, 1, 3, 1, 2, 3, 1, 3, 5]
def baseStart_3695594 : Nat := 118140960795 + 3695594 * 2 ^ 59
def prefixEnd_3695594 : Nat := 4983230072969 + 3 ^ 40 * 3695594 * 2
def baseEnd_3695594 : Nat := 421692450193759823373173

theorem tailTrace_3695594 : CollatzResearch.WordTrace tailWord_3695594 prefixEnd_3695594 421692450193759823373173 := by
  unfold tailWord_3695594
  simp only [CollatzResearch.WordTrace]
  refine ⟨33697346643375392512829459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89859591049001046700878557 33697346643375392512829459)
  ·
    refine ⟨50546019965063088769244189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33697346643375392512829459 50546019965063088769244189)
    ·
      refine ⟨18954757486898658288466571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50546019965063088769244189 18954757486898658288466571)
      ·
        refine ⟨28432136230347987432699857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18954757486898658288466571 28432136230347987432699857)
        ·
          refine ⟨21324102172760990574524893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28432136230347987432699857 21324102172760990574524893)
          ·
            refine ⟨7996538314785371465446835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21324102172760990574524893 7996538314785371465446835)
            ·
              refine ⟨11994807472178057198170253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7996538314785371465446835 11994807472178057198170253)
              ·
                refine ⟨4498052802066771449313845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11994807472178057198170253 4498052802066771449313845)
                ·
                  refine ⟨421692450193759823373173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4498052802066771449313845 421692450193759823373173)
                  ·
                    rfl

theorem cell22_3695594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_3695594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695594 prefixEnd_3695594 := by exact prefixLift 3695594
  have htrace : WordTrace (prefixWord ++ tailWord_3695594) baseStart_3695594 baseEnd_3695594 := by
    simpa [prefixWord, tailWord_3695594, baseEnd_3695594] using wordTrace_append hprefix tailTrace_3695594
  have hstable : (prefixWord ++ tailWord_3695594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695594).length < 2 ^ (prefixWord ++ tailWord_3695594).sum := by decide
  have hdescent : baseEnd_3695594 < baseStart_3695594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695697 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 1, 8]
def baseStart_3695697 : Nat := 118140960795 + 3695697 * 2 ^ 59
def prefixEnd_3695697 : Nat := 4983230072969 + 3 ^ 40 * 3695697 * 2
def baseEnd_3695697 : Nat := 1265112609586221534794203

theorem tailTrace_3695697 : CollatzResearch.WordTrace tailWord_3695697 prefixEnd_3695697 1265112609586221534794203 := by
  unfold tailWord_3695697
  simp only [CollatzResearch.WordTrace]
  refine ⟨134793143292128418642317345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89862095528085612428211563 134793143292128418642317345)
  ·
    refine ⟨101094857469096313981738009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134793143292128418642317345 101094857469096313981738009)
    ·
      refine ⟨75821143101822235486303507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101094857469096313981738009 75821143101822235486303507)
      ·
        refine ⟨113731714652733353229455261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75821143101822235486303507 113731714652733353229455261)
        ·
          refine ⟨42649392994775007461045723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113731714652733353229455261 42649392994775007461045723)
          ·
            refine ⟨63974089492162511191568585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42649392994775007461045723 63974089492162511191568585)
            ·
              refine ⟨47980567119121883393676439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63974089492162511191568585 47980567119121883393676439)
              ·
                refine ⟨71970850678682825090514659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47980567119121883393676439 71970850678682825090514659)
                ·
                  refine ⟨107956276018024237635771989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71970850678682825090514659 107956276018024237635771989)
                  ·
                    refine ⟨1265112609586221534794203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107956276018024237635771989 1265112609586221534794203)
                    ·
                      rfl

theorem cell22_3695697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_3695697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695697 prefixEnd_3695697 := by exact prefixLift 3695697
  have htrace : WordTrace (prefixWord ++ tailWord_3695697) baseStart_3695697 baseEnd_3695697 := by
    simpa [prefixWord, tailWord_3695697, baseEnd_3695697] using wordTrace_append hprefix tailTrace_3695697
  have hstable : (prefixWord ++ tailWord_3695697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695697).length < 2 ^ (prefixWord ++ tailWord_3695697).sum := by decide
  have hdescent : baseEnd_3695697 < baseStart_3695697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695699 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 3, 3]
def baseStart_3695699 : Nat := 118140960795 + 3695699 * 2 ^ 59
def prefixEnd_3695699 : Nat := 4983230072969 + 3 ^ 40 * 3695699 * 2
def baseEnd_3695699 : Nat := 1265113294227094196244197

theorem tailTrace_3695699 : CollatzResearch.WordTrace tailWord_3695699 prefixEnd_3695699 1265113294227094196244197 := by
  unfold tailWord_3695699
  simp only [CollatzResearch.WordTrace]
  refine ⟨134793216238121172983890151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89862144158747448655926767 134793216238121172983890151)
  ·
    refine ⟨202189824357181759475835227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134793216238121172983890151 202189824357181759475835227)
    ·
      refine ⟨303284736535772639213752841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202189824357181759475835227 303284736535772639213752841)
      ·
        refine ⟨227463552401829479410314631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303284736535772639213752841 227463552401829479410314631)
        ·
          refine ⟨341195328602744219115471947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227463552401829479410314631 341195328602744219115471947)
          ·
            refine ⟨511792992904116328673207921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341195328602744219115471947 511792992904116328673207921)
            ·
              refine ⟨383844744678087246504905941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511792992904116328673207921 383844744678087246504905941)
              ·
                refine ⟨8996361203392669839958733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 383844744678087246504905941 8996361203392669839958733)
                ·
                  refine ⟨3373635451272251189984525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8996361203392669839958733 3373635451272251189984525)
                  ·
                    refine ⟨1265113294227094196244197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3373635451272251189984525 1265113294227094196244197)
                    ·
                      rfl

theorem cell22_3695699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 3].length) (baseStart_3695699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695699 prefixEnd_3695699 := by exact prefixLift 3695699
  have htrace : WordTrace (prefixWord ++ tailWord_3695699) baseStart_3695699 baseEnd_3695699 := by
    simpa [prefixWord, tailWord_3695699, baseEnd_3695699] using wordTrace_append hprefix tailTrace_3695699
  have hstable : (prefixWord ++ tailWord_3695699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695699).length < 2 ^ (prefixWord ++ tailWord_3695699).sum := by decide
  have hdescent : baseEnd_3695699 < baseStart_3695699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3695808 : List Nat := [2, 1, 1, 2, 6, 1, 1, 4, 4]
def baseStart_3695808 : Nat := 118140960795 + 3695808 * 2 ^ 59
def prefixEnd_3695808 : Nat := 4983230072969 + 3 ^ 40 * 3695808 * 2
def baseEnd_3695808 : Nat := 421716869051551415089621

theorem tailTrace_3695808 : CollatzResearch.WordTrace tailWord_3695808 prefixEnd_3695808 421716869051551415089621 := by
  unfold tailWord_3695808
  simp only [CollatzResearch.WordTrace]
  refine ⟨67398595897363142299804039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89864794529817523066405385 67398595897363142299804039)
  ·
    refine ⟨101097893846044713449706059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67398595897363142299804039 101097893846044713449706059)
    ·
      refine ⟨151646840769067070174559089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101097893846044713449706059 151646840769067070174559089)
      ·
        refine ⟨113735130576800302630919317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151646840769067070174559089 113735130576800302630919317)
        ·
          refine ⟨5331334245787514185824343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113735130576800302630919317 5331334245787514185824343)
          ·
            refine ⟨7997001368681271278736515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5331334245787514185824343 7997001368681271278736515)
            ·
              refine ⟨11995502053021906918104773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7997001368681271278736515 11995502053021906918104773)
              ·
                refine ⟨2249156634941607547144645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11995502053021906918104773 2249156634941607547144645)
                ·
                  refine ⟨421716869051551415089621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2249156634941607547144645 421716869051551415089621)
                  ·
                    rfl

theorem cell22_3695808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 4].length) (baseStart_3695808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3695808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3695808 prefixEnd_3695808 := by exact prefixLift 3695808
  have htrace : WordTrace (prefixWord ++ tailWord_3695808) baseStart_3695808 baseEnd_3695808 := by
    simpa [prefixWord, tailWord_3695808, baseEnd_3695808] using wordTrace_append hprefix tailTrace_3695808
  have hstable : (prefixWord ++ tailWord_3695808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3695808).length < 2 ^ (prefixWord ++ tailWord_3695808).sum := by decide
  have hdescent : baseEnd_3695808 < baseStart_3695808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3695808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696003 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 5, 3]
def baseStart_3696003 : Nat := 118140960795 + 3696003 * 2 ^ 59
def prefixEnd_3696003 : Nat := 4983230072969 + 3 ^ 40 * 3696003 * 2
def baseEnd_3696003 : Nat := 1265217359639738736643265

theorem tailTrace_3696003 : CollatzResearch.WordTrace tailWord_3696003 prefixEnd_3696003 1265217359639738736643265 := by
  unfold tailWord_3696003
  simp only [CollatzResearch.WordTrace]
  refine ⟨134804304029019832902956663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89869536019346555268637775 134804304029019832902956663)
  ·
    refine ⟨202206456043529749354434995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134804304029019832902956663 202206456043529749354434995)
    ·
      refine ⟨303309684065294624031652493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202206456043529749354434995 303309684065294624031652493)
      ·
        refine ⟨113741131524485484011869685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303309684065294624031652493 113741131524485484011869685)
        ·
          refine ⟨10663231080420514126112783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113741131524485484011869685 10663231080420514126112783)
          ·
            refine ⟨15994846620630771189169175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10663231080420514126112783 15994846620630771189169175)
            ·
              refine ⟨23992269930946156783753763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15994846620630771189169175 23992269930946156783753763)
              ·
                refine ⟨35988404896419235175630645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23992269930946156783753763 35988404896419235175630645)
                ·
                  refine ⟨3373912959039303297715373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35988404896419235175630645 3373912959039303297715373)
                  ·
                    refine ⟨1265217359639738736643265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3373912959039303297715373 1265217359639738736643265)
                    ·
                      rfl

theorem cell22_3696003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 3].length) (baseStart_3696003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696003 prefixEnd_3696003 := by exact prefixLift 3696003
  have htrace : WordTrace (prefixWord ++ tailWord_3696003) baseStart_3696003 baseEnd_3696003 := by
    simpa [prefixWord, tailWord_3696003, baseEnd_3696003] using wordTrace_append hprefix tailTrace_3696003
  have hstable : (prefixWord ++ tailWord_3696003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696003).length < 2 ^ (prefixWord ++ tailWord_3696003).sum := by decide
  have hdescent : baseEnd_3696003 < baseStart_3696003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696125 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_3696125 : Nat := 118140960795 + 3696125 * 2 ^ 59
def prefixEnd_3696125 : Nat := 4983230072969 + 3 ^ 40 * 3696125 * 2
def baseEnd_3696125 : Nat := 1265259122732971085092891

theorem tailTrace_3696125 : CollatzResearch.WordTrace tailWord_3696125 prefixEnd_3696125 1265259122732971085092891 := by
  unfold tailWord_3696125
  simp only [CollatzResearch.WordTrace]
  refine ⟨134808753734577847738897829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89872502489718565159265219 134808753734577847738897829)
  ·
    refine ⟨25276641325233346451043343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134808753734577847738897829 25276641325233346451043343)
    ·
      refine ⟨37914961987850019676565015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25276641325233346451043343 37914961987850019676565015)
      ·
        refine ⟨56872442981775029514847523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37914961987850019676565015 56872442981775029514847523)
        ·
          refine ⟨85308664472662544272271285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56872442981775029514847523 85308664472662544272271285)
          ·
            refine ⟨7997687294312113525525433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85308664472662544272271285 7997687294312113525525433)
            ·
              refine ⟨5998265470734085144144075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7997687294312113525525433 5998265470734085144144075)
              ·
                refine ⟨8997398206101127716216113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5998265470734085144144075 8997398206101127716216113)
                ·
                  refine ⟨6748048654575845787162085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8997398206101127716216113 6748048654575845787162085)
                  ·
                    refine ⟨1265259122732971085092891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6748048654575845787162085 1265259122732971085092891)
                    ·
                      rfl

theorem cell22_3696125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_3696125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696125 prefixEnd_3696125 := by exact prefixLift 3696125
  have htrace : WordTrace (prefixWord ++ tailWord_3696125) baseStart_3696125 baseEnd_3696125 := by
    simpa [prefixWord, tailWord_3696125, baseEnd_3696125] using wordTrace_append hprefix tailTrace_3696125
  have hstable : (prefixWord ++ tailWord_3696125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696125).length < 2 ^ (prefixWord ++ tailWord_3696125).sum := by decide
  have hdescent : baseEnd_3696125 < baseStart_3696125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696232 : List Nat := [2, 1, 4, 3, 1, 1, 1, 4, 1, 4]
def baseStart_3696232 : Nat := 118140960795 + 3696232 * 2 ^ 59
def prefixEnd_3696232 : Nat := 4983230072969 + 3 ^ 40 * 3696232 * 2
def baseEnd_3696232 : Nat := 1265295751019658472667563

theorem tailTrace_3696232 : CollatzResearch.WordTrace tailWord_3696232 prefixEnd_3696232 1265295751019658472667563 := by
  unfold tailWord_3696232
  simp only [CollatzResearch.WordTrace]
  refine ⟨67406328172595102506521475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89875104230126803342028633 67406328172595102506521475)
  ·
    refine ⟨101109492258892653759782213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67406328172595102506521475 101109492258892653759782213)
    ·
      refine ⟨18958029798542372579959165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101109492258892653759782213 18958029798542372579959165)
      ·
        refine ⟨7109261174453389717484687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18958029798542372579959165 7109261174453389717484687)
        ·
          refine ⟨10663891761680084576227031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7109261174453389717484687 10663891761680084576227031)
          ·
            refine ⟨15995837642520126864340547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10663891761680084576227031 15995837642520126864340547)
            ·
              refine ⟨23993756463780190296510821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15995837642520126864340547 23993756463780190296510821)
              ·
                refine ⟨4498829336958785680595779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23993756463780190296510821 4498829336958785680595779)
                ·
                  refine ⟨6748244005438178520893669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498829336958785680595779 6748244005438178520893669)
                  ·
                    refine ⟨1265295751019658472667563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6748244005438178520893669 1265295751019658472667563)
                    ·
                      rfl

theorem cell22_3696232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_3696232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696232 prefixEnd_3696232 := by exact prefixLift 3696232
  have htrace : WordTrace (prefixWord ++ tailWord_3696232) baseStart_3696232 baseEnd_3696232 := by
    simpa [prefixWord, tailWord_3696232, baseEnd_3696232] using wordTrace_append hprefix tailTrace_3696232
  have hstable : (prefixWord ++ tailWord_3696232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696232).length < 2 ^ (prefixWord ++ tailWord_3696232).sum := by decide
  have hdescent : baseEnd_3696232 < baseStart_3696232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696264 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 6]
def baseStart_3696264 : Nat := 118140960795 + 3696264 * 2 ^ 59
def prefixEnd_3696264 : Nat := 4983230072969 + 3 ^ 40 * 3696264 * 2
def baseEnd_3696264 : Nat := 421768901757873685289155

theorem tailTrace_3696264 : CollatzResearch.WordTrace tailWord_3696264 prefixEnd_3696264 421768901757873685289155 := by
  unfold tailWord_3696264
  simp only [CollatzResearch.WordTrace]
  refine ⟨67406911740537137239103923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89875882320716182985471897 67406911740537137239103923)
  ·
    refine ⟨101110367610805705858655885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67406911740537137239103923 101110367610805705858655885)
    ·
      refine ⟨37916387854052139696995957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101110367610805705858655885 37916387854052139696995957)
      ·
        refine ⟨3554661361317388096593371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37916387854052139696995957 3554661361317388096593371)
        ·
          refine ⟨5331992041976082144890057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3554661361317388096593371 5331992041976082144890057)
          ·
            refine ⟨3998994031482061608667543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5331992041976082144890057 3998994031482061608667543)
            ·
              refine ⟨5998491047223092413001315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3998994031482061608667543 5998491047223092413001315)
              ·
                refine ⟨8997736570834638619501973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5998491047223092413001315 8997736570834638619501973)
                ·
                  refine ⟨421768901757873685289155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8997736570834638619501973 421768901757873685289155)
                  ·
                    rfl

theorem cell22_3696264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 6].length) (baseStart_3696264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696264 prefixEnd_3696264 := by exact prefixLift 3696264
  have htrace : WordTrace (prefixWord ++ tailWord_3696264) baseStart_3696264 baseEnd_3696264 := by
    simpa [prefixWord, tailWord_3696264, baseEnd_3696264] using wordTrace_append hprefix tailTrace_3696264
  have hstable : (prefixWord ++ tailWord_3696264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696264).length < 2 ^ (prefixWord ++ tailWord_3696264).sum := by decide
  have hdescent : baseEnd_3696264 < baseStart_3696264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696273 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 2, 7]
def baseStart_3696273 : Nat := 118140960795 + 3696273 * 2 ^ 59
def prefixEnd_3696273 : Nat := 4983230072969 + 3 ^ 40 * 3696273 * 2
def baseEnd_3696273 : Nat := 1265309786157548032392437

theorem tailTrace_3696273 : CollatzResearch.WordTrace tailWord_3696273 prefixEnd_3696273 1265309786157548032392437 := by
  unfold tailWord_3696273
  simp only [CollatzResearch.WordTrace]
  refine ⟨134814151738041669015285473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89876101158694446010190315 134814151738041669015285473)
  ·
    refine ⟨101110613803531251761464105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134814151738041669015285473 101110613803531251761464105)
    ·
      refine ⟨75832960352648438821098079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101110613803531251761464105 75832960352648438821098079)
      ·
        refine ⟨113749440528972658231647119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75832960352648438821098079 113749440528972658231647119)
        ·
          refine ⟨170624160793458987347470679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113749440528972658231647119 170624160793458987347470679)
          ·
            refine ⟨255936241190188481021206019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170624160793458987347470679 255936241190188481021206019)
            ·
              refine ⟨383904361785282721531809029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255936241190188481021206019 383904361785282721531809029)
              ·
                refine ⟨71982067834740510287214193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 383904361785282721531809029 71982067834740510287214193)
                ·
                  refine ⟨53986550876055382715410645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71982067834740510287214193 53986550876055382715410645)
                  ·
                    refine ⟨1265309786157548032392437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53986550876055382715410645 1265309786157548032392437)
                    ·
                      rfl

theorem cell22_3696273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_3696273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696273 prefixEnd_3696273 := by exact prefixLift 3696273
  have htrace : WordTrace (prefixWord ++ tailWord_3696273) baseStart_3696273 baseEnd_3696273 := by
    simpa [prefixWord, tailWord_3696273, baseEnd_3696273] using wordTrace_append hprefix tailTrace_3696273
  have hstable : (prefixWord ++ tailWord_3696273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696273).length < 2 ^ (prefixWord ++ tailWord_3696273).sum := by decide
  have hdescent : baseEnd_3696273 < baseStart_3696273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696279 : List Nat := [1, 1, 3, 3, 2, 2, 4, 1, 2, 3]
def baseStart_3696279 : Nat := 118140960795 + 3696279 * 2 ^ 59
def prefixEnd_3696279 : Nat := 4983230072969 + 3 ^ 40 * 3696279 * 2
def baseEnd_3696279 : Nat := 1265311840080166016742419

theorem tailTrace_3696279 : CollatzResearch.WordTrace tailWord_3696279 prefixEnd_3696279 1265311840080166016742419 := by
  unfold tailWord_3696279
  simp only [CollatzResearch.WordTrace]
  refine ⟨134814370576019932040003891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89876247050679954693335927 134814370576019932040003891)
  ·
    refine ⟨202221555864029898060005837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134814370576019932040003891 202221555864029898060005837)
    ·
      refine ⟨75833083449011211772502189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202221555864029898060005837 75833083449011211772502189)
      ·
        refine ⟨28437406293379204414688321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75833083449011211772502189 28437406293379204414688321)
        ·
          refine ⟨21328054720034403311016241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28437406293379204414688321 21328054720034403311016241)
          ·
            refine ⟨15996041040025802483262181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21328054720034403311016241 15996041040025802483262181)
            ·
              refine ⟨2999257695004837965611659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15996041040025802483262181 2999257695004837965611659)
              ·
                refine ⟨4498886542507256948417489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999257695004837965611659 4498886542507256948417489)
                ·
                  refine ⟨3374164906880442711313117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4498886542507256948417489 3374164906880442711313117)
                  ·
                    refine ⟨1265311840080166016742419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3374164906880442711313117 1265311840080166016742419)
                    ·
                      rfl

theorem cell22_3696279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_3696279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696279 prefixEnd_3696279 := by exact prefixLift 3696279
  have htrace : WordTrace (prefixWord ++ tailWord_3696279) baseStart_3696279 baseEnd_3696279 := by
    simpa [prefixWord, tailWord_3696279, baseEnd_3696279] using wordTrace_append hprefix tailTrace_3696279
  have hstable : (prefixWord ++ tailWord_3696279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696279).length < 2 ^ (prefixWord ++ tailWord_3696279).sum := by decide
  have hdescent : baseEnd_3696279 < baseStart_3696279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696296 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3696296 : Nat := 118140960795 + 3696296 * 2 ^ 59
def prefixEnd_3696296 : Nat := 4983230072969 + 3 ^ 40 * 3696296 * 2
def baseEnd_3696296 : Nat := 1265317659527583639067367

theorem tailTrace_3696296 : CollatzResearch.WordTrace tailWord_3696296 prefixEnd_3696296 1265317659527583639067367 := by
  unfold tailWord_3696296
  simp only [CollatzResearch.WordTrace]
  refine ⟨67407495308479171971686371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89876660411305562628915161 67407495308479171971686371)
  ·
    refine ⟨101111242962718757957529557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67407495308479171971686371 101111242962718757957529557)
    ·
      refine ⟨2369794756938720889629599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 101111242962718757957529557 2369794756938720889629599)
      ·
        refine ⟨3554692135408081334444399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2369794756938720889629599 3554692135408081334444399)
        ·
          refine ⟨5332038203112122001666599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3554692135408081334444399 5332038203112122001666599)
          ·
            refine ⟨7998057304668183002499899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332038203112122001666599 7998057304668183002499899)
            ·
              refine ⟨11997085957002274503749849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998057304668183002499899 11997085957002274503749849)
              ·
                refine ⟨8997814467751705877812387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11997085957002274503749849 8997814467751705877812387)
                ·
                  refine ⟨13496721701627558816718581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8997814467751705877812387 13496721701627558816718581)
                  ·
                    refine ⟨1265317659527583639067367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13496721701627558816718581 1265317659527583639067367)
                    ·
                      rfl

theorem cell22_3696296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3696296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696296 prefixEnd_3696296 := by exact prefixLift 3696296
  have htrace : WordTrace (prefixWord ++ tailWord_3696296) baseStart_3696296 baseEnd_3696296 := by
    simpa [prefixWord, tailWord_3696296, baseEnd_3696296] using wordTrace_append hprefix tailTrace_3696296
  have hstable : (prefixWord ++ tailWord_3696296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696296).length < 2 ^ (prefixWord ++ tailWord_3696296).sum := by decide
  have hdescent : baseEnd_3696296 < baseStart_3696296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696326 : List Nat := [6, 1, 2, 1, 1, 3, 1, 7]
def baseStart_3696326 : Nat := 118140960795 + 3696326 * 2 ^ 59
def prefixEnd_3696326 : Nat := 4983230072969 + 3 ^ 40 * 3696326 * 2
def baseEnd_3696326 : Nat := 140591992126741506757475

theorem tailTrace_3696326 : CollatzResearch.WordTrace tailWord_3696326 prefixEnd_3696326 140591992126741506757475 := by
  unfold tailWord_3696326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4213002650214051845842651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89877389871233106044643221 4213002650214051845842651)
  ·
    refine ⟨6319503975321077768763977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4213002650214051845842651 6319503975321077768763977)
    ·
      refine ⟨4739627981490808326572983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6319503975321077768763977 4739627981490808326572983)
      ·
        refine ⟨7109441972236212489859475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4739627981490808326572983 7109441972236212489859475)
        ·
          refine ⟨10664162958354318734789213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7109441972236212489859475 10664162958354318734789213)
          ·
            refine ⟨3999061109382869525545955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10664162958354318734789213 3999061109382869525545955)
            ·
              refine ⟨5998591664074304288318933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3999061109382869525545955 5998591664074304288318933)
              ·
                refine ⟨140591992126741506757475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5998591664074304288318933 140591992126741506757475)
                ·
                  rfl

theorem cell22_3696326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_3696326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696326 prefixEnd_3696326 := by exact prefixLift 3696326
  have htrace : WordTrace (prefixWord ++ tailWord_3696326) baseStart_3696326 baseEnd_3696326 := by
    simpa [prefixWord, tailWord_3696326, baseEnd_3696326] using wordTrace_append hprefix tailTrace_3696326
  have hstable : (prefixWord ++ tailWord_3696326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696326).length < 2 ^ (prefixWord ++ tailWord_3696326).sum := by decide
  have hdescent : baseEnd_3696326 < baseStart_3696326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696367 : List Nat := [1, 1, 2, 1, 5, 1, 3, 3, 1, 4]
def baseStart_3696367 : Nat := 118140960795 + 3696367 * 2 ^ 59
def prefixEnd_3696367 : Nat := 4983230072969 + 3 ^ 40 * 3696367 * 2
def baseEnd_3696367 : Nat := 1265341964278563120542149

theorem tailTrace_3696367 : CollatzResearch.WordTrace tailWord_3696367 prefixEnd_3696367 1265341964278563120542149 := by
  unfold tailWord_3696367
  simp only [CollatzResearch.WordTrace]
  refine ⟨134817580199701123069207355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89878386799800748712804903 134817580199701123069207355)
  ·
    refine ⟨202226370299551684603811033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134817580199701123069207355 202226370299551684603811033)
    ·
      refine ⟨151669777724663763452858275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202226370299551684603811033 151669777724663763452858275)
      ·
        refine ⟨227504666586995645179287413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151669777724663763452858275 227504666586995645179287413)
        ·
          refine ⟨21328562492530841735558195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227504666586995645179287413 21328562492530841735558195)
          ·
            refine ⟨31992843738796262603337293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21328562492530841735558195 31992843738796262603337293)
            ·
              refine ⟨11997316402048598476251485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31992843738796262603337293 11997316402048598476251485)
              ·
                refine ⟨4498993650768224428594307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11997316402048598476251485 4498993650768224428594307)
                ·
                  refine ⟨6748490476152336642891461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4498993650768224428594307 6748490476152336642891461)
                  ·
                    refine ⟨1265341964278563120542149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6748490476152336642891461 1265341964278563120542149)
                    ·
                      rfl

theorem cell22_3696367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_3696367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696367 prefixEnd_3696367 := by exact prefixLift 3696367
  have htrace : WordTrace (prefixWord ++ tailWord_3696367) baseStart_3696367 baseEnd_3696367 := by
    simpa [prefixWord, tailWord_3696367, baseEnd_3696367] using wordTrace_append hprefix tailTrace_3696367
  have hstable : (prefixWord ++ tailWord_3696367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696367).length < 2 ^ (prefixWord ++ tailWord_3696367).sum := by decide
  have hdescent : baseEnd_3696367 < baseStart_3696367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696395 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 1, 6]
def baseStart_3696395 : Nat := 118140960795 + 3696395 * 2 ^ 59
def prefixEnd_3696395 : Nat := 4983230072969 + 3 ^ 40 * 3696395 * 2
def baseEnd_3696395 : Nat := 1265351549250780380842063

theorem tailTrace_3696395 : CollatzResearch.WordTrace tailWord_3696395 prefixEnd_3696395 1265351549250780380842063 := by
  unfold tailWord_3696395
  simp only [CollatzResearch.WordTrace]
  refine ⟨134818601443599683851226639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89879067629066455900817759 134818601443599683851226639)
  ·
    refine ⟨202227902165399525776839959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134818601443599683851226639 202227902165399525776839959)
    ·
      refine ⟨303341853248099288665259939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202227902165399525776839959 303341853248099288665259939)
      ·
        refine ⟨455012779872148932997889909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303341853248099288665259939 455012779872148932997889909)
        ·
          refine ⟨42657448113013962468552179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 455012779872148932997889909 42657448113013962468552179)
          ·
            refine ⟨63986172169520943702828269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42657448113013962468552179 63986172169520943702828269)
            ·
              refine ⟨23994814563570353888560601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63986172169520943702828269 23994814563570353888560601)
              ·
                refine ⟨17996110922677765416420451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23994814563570353888560601 17996110922677765416420451)
                ·
                  refine ⟨26994166384016648124630677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17996110922677765416420451 26994166384016648124630677)
                  ·
                    refine ⟨1265351549250780380842063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26994166384016648124630677 1265351549250780380842063)
                    ·
                      rfl

theorem cell22_3696395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 6].length) (baseStart_3696395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696395 prefixEnd_3696395 := by exact prefixLift 3696395
  have htrace : WordTrace (prefixWord ++ tailWord_3696395) baseStart_3696395 baseEnd_3696395 := by
    simpa [prefixWord, tailWord_3696395, baseEnd_3696395] using wordTrace_append hprefix tailTrace_3696395
  have hstable : (prefixWord ++ tailWord_3696395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696395).length < 2 ^ (prefixWord ++ tailWord_3696395).sum := by decide
  have hdescent : baseEnd_3696395 < baseStart_3696395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696412 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_3696412 : Nat := 118140960795 + 3696412 * 2 ^ 59
def prefixEnd_3696412 : Nat := 4983230072969 + 3 ^ 40 * 3696412 * 2
def baseEnd_3696412 : Nat := 1265357368698198003167011

theorem tailTrace_3696412 : CollatzResearch.WordTrace tailWord_3696412 prefixEnd_3696412 1265357368698198003167011 := by
  unfold tailWord_3696412
  simp only [CollatzResearch.WordTrace]
  refine ⟨67409610742269047877297745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89879480989692063836396993 67409610742269047877297745)
  ·
    refine ⟨50557208056701785907973309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67409610742269047877297745 50557208056701785907973309)
    ·
      refine ⟨18958953021263169715489991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50557208056701785907973309 18958953021263169715489991)
      ·
        refine ⟨28438429531894754573234987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18958953021263169715489991 28438429531894754573234987)
        ·
          refine ⟨42657644297842131859852481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28438429531894754573234987 42657644297842131859852481)
          ·
            refine ⟨31993233223381598894889361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42657644297842131859852481 31993233223381598894889361)
            ·
              refine ⟨23994924917536199171167021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31993233223381598894889361 23994924917536199171167021)
              ·
                refine ⟨8998096844076074689187633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23994924917536199171167021 8998096844076074689187633)
                ·
                  refine ⟨6748572633057056016890725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8998096844076074689187633 6748572633057056016890725)
                  ·
                    refine ⟨1265357368698198003167011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6748572633057056016890725 1265357368698198003167011)
                    ·
                      rfl

theorem cell22_3696412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_3696412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696412 prefixEnd_3696412 := by exact prefixLift 3696412
  have htrace : WordTrace (prefixWord ++ tailWord_3696412) baseStart_3696412 baseEnd_3696412 := by
    simpa [prefixWord, tailWord_3696412, baseEnd_3696412] using wordTrace_append hprefix tailTrace_3696412
  have hstable : (prefixWord ++ tailWord_3696412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696412).length < 2 ^ (prefixWord ++ tailWord_3696412).sum := by decide
  have hdescent : baseEnd_3696412 < baseStart_3696412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696487 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3696487 : Nat := 118140960795 + 3696487 * 2 ^ 59
def prefixEnd_3696487 : Nat := 4983230072969 + 3 ^ 40 * 3696487 * 2
def baseEnd_3696487 : Nat := 1265383042730922807541781

theorem tailTrace_3696487 : CollatzResearch.WordTrace tailWord_3696487 prefixEnd_3696487 1265383042730922807541781 := by
  unfold tailWord_3696487
  simp only [CollatzResearch.WordTrace]
  refine ⟨134821956959266383563575715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89881304639510922375717143 134821956959266383563575715)
  ·
    refine ⟨202232935438899575345363573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134821956959266383563575715 202232935438899575345363573)
    ·
      refine ⟨18959337697396835188627835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202232935438899575345363573 18959337697396835188627835)
      ·
        refine ⟨28439006546095252782941753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18959337697396835188627835 28439006546095252782941753)
        ·
          refine ⟨21329254909571439587206315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28439006546095252782941753 21329254909571439587206315)
          ·
            refine ⟨31993882364357159380809473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21329254909571439587206315 31993882364357159380809473)
            ·
              refine ⟨23995411773267869535607105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31993882364357159380809473 23995411773267869535607105)
              ·
                refine ⟨17996558829950902151705329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23995411773267869535607105 17996558829950902151705329)
                ·
                  refine ⟨13497419122463176613778997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17996558829950902151705329 13497419122463176613778997)
                  ·
                    refine ⟨1265383042730922807541781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13497419122463176613778997 1265383042730922807541781)
                    ·
                      rfl

theorem cell22_3696487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3696487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696487 prefixEnd_3696487 := by exact prefixLift 3696487
  have htrace : WordTrace (prefixWord ++ tailWord_3696487) baseStart_3696487 baseEnd_3696487 := by
    simpa [prefixWord, tailWord_3696487, baseEnd_3696487] using wordTrace_append hprefix tailTrace_3696487
  have hstable : (prefixWord ++ tailWord_3696487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696487).length < 2 ^ (prefixWord ++ tailWord_3696487).sum := by decide
  have hdescent : baseEnd_3696487 < baseStart_3696487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696493 : List Nat := [1, 5, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_3696493 : Nat := 118140960795 + 3696493 * 2 ^ 59
def prefixEnd_3696493 : Nat := 4983230072969 + 3 ^ 40 * 3696493 * 2
def baseEnd_3696493 : Nat := 1265385096653540791891763

theorem tailTrace_3696493 : CollatzResearch.WordTrace tailWord_3696493 prefixEnd_3696493 1265385096653540791891763 := by
  unfold tailWord_3696493
  simp only [CollatzResearch.WordTrace]
  refine ⟨134822175797244646588294133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89881450531496431058862755 134822175797244646588294133)
  ·
    refine ⟨12639578980991685617652575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134822175797244646588294133 12639578980991685617652575)
    ·
      refine ⟨18959368471487528426478863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12639578980991685617652575 18959368471487528426478863)
      ·
        refine ⟨28439052707231292639718295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18959368471487528426478863 28439052707231292639718295)
        ·
          refine ⟨42658579060846938959577443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28439052707231292639718295 42658579060846938959577443)
          ·
            refine ⟨63987868591270408439366165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42658579060846938959577443 63987868591270408439366165)
            ·
              refine ⟨2999431340215800395595289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63987868591270408439366165 2999431340215800395595289)
              ·
                refine ⟨2249573505161850296696467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2999431340215800395595289 2249573505161850296696467)
                ·
                  refine ⟨3374360257742775445044701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249573505161850296696467 3374360257742775445044701)
                  ·
                    refine ⟨1265385096653540791891763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3374360257742775445044701 1265385096653540791891763)
                    ·
                      rfl

theorem cell22_3696493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_3696493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696493 prefixEnd_3696493 := by exact prefixLift 3696493
  have htrace : WordTrace (prefixWord ++ tailWord_3696493) baseStart_3696493 baseEnd_3696493 := by
    simpa [prefixWord, tailWord_3696493, baseEnd_3696493] using wordTrace_append hprefix tailTrace_3696493
  have hstable : (prefixWord ++ tailWord_3696493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696493).length < 2 ^ (prefixWord ++ tailWord_3696493).sum := by decide
  have hdescent : baseEnd_3696493 < baseStart_3696493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696517 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 6]
def baseStart_3696517 : Nat := 118140960795 + 3696517 * 2 ^ 59
def prefixEnd_3696517 : Nat := 4983230072969 + 3 ^ 40 * 3696517 * 2
def baseEnd_3696517 : Nat := 421797770781337576430563

theorem tailTrace_3696517 : CollatzResearch.WordTrace tailWord_3696517 prefixEnd_3696517 421797770781337576430563 := by
  unfold tailWord_3696517
  simp only [CollatzResearch.WordTrace]
  refine ⟨134823051149157698687167805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89882034099438465791445203 134823051149157698687167805)
  ·
    refine ⟨50558644180934137007687927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134823051149157698687167805 50558644180934137007687927)
    ·
      refine ⟨75837966271401205511531891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50558644180934137007687927 75837966271401205511531891)
      ·
        refine ⟨113756949407101808267297837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75837966271401205511531891 113756949407101808267297837)
        ·
          refine ⟨42658856027663178100236689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113756949407101808267297837 42658856027663178100236689)
          ·
            refine ⟨31994142020747383575177517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42658856027663178100236689 31994142020747383575177517)
            ·
              refine ⟨11997803257780268840691569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31994142020747383575177517 11997803257780268840691569)
              ·
                refine ⟨8998352443335201630518677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11997803257780268840691569 8998352443335201630518677)
                ·
                  refine ⟨421797770781337576430563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8998352443335201630518677 421797770781337576430563)
                  ·
                    rfl

theorem cell22_3696517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_3696517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696517 prefixEnd_3696517 := by exact prefixLift 3696517
  have htrace : WordTrace (prefixWord ++ tailWord_3696517) baseStart_3696517 baseEnd_3696517 := by
    simpa [prefixWord, tailWord_3696517, baseEnd_3696517] using wordTrace_append hprefix tailTrace_3696517
  have hstable : (prefixWord ++ tailWord_3696517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696517).length < 2 ^ (prefixWord ++ tailWord_3696517).sum := by decide
  have hdescent : baseEnd_3696517 < baseStart_3696517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696547 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 4, 4]
def baseStart_3696547 : Nat := 118140960795 + 3696547 * 2 ^ 59
def prefixEnd_3696547 : Nat := 4983230072969 + 3 ^ 40 * 3696547 * 2
def baseEnd_3696547 : Nat := 1265403581957102651041597

theorem tailTrace_3696547 : CollatzResearch.WordTrace tailWord_3696547 prefixEnd_3696547 1265403581957102651041597 := by
  unfold tailWord_3696547
  simp only [CollatzResearch.WordTrace]
  refine ⟨134824145339049013810759895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89882763559366009207173263 134824145339049013810759895)
  ·
    refine ⟨202236218008573520716139843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134824145339049013810759895 202236218008573520716139843)
    ·
      refine ⟨303354327012860281074209765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202236218008573520716139843 303354327012860281074209765)
      ·
        refine ⟨56878936314911302701414331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303354327012860281074209765 56878936314911302701414331)
        ·
          refine ⟨85318404472366954052121497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56878936314911302701414331 85318404472366954052121497)
          ·
            refine ⟨63988803354275215539091123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85318404472366954052121497 63988803354275215539091123)
            ·
              refine ⟨95983205031412823308636685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63988803354275215539091123 95983205031412823308636685)
              ·
                refine ⟨35993701886779808740738757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95983205031412823308636685 35993701886779808740738757)
                ·
                  refine ⟨6748819103771214138888517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35993701886779808740738757 6748819103771214138888517)
                  ·
                    refine ⟨1265403581957102651041597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6748819103771214138888517 1265403581957102651041597)
                    ·
                      rfl

theorem cell22_3696547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 4].length) (baseStart_3696547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696547 prefixEnd_3696547 := by exact prefixLift 3696547
  have htrace : WordTrace (prefixWord ++ tailWord_3696547) baseStart_3696547 baseEnd_3696547 := by
    simpa [prefixWord, tailWord_3696547, baseEnd_3696547] using wordTrace_append hprefix tailTrace_3696547
  have hstable : (prefixWord ++ tailWord_3696547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696547).length < 2 ^ (prefixWord ++ tailWord_3696547).sum := by decide
  have hdescent : baseEnd_3696547 < baseStart_3696547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696551 : List Nat := [1, 1, 6, 1, 2, 1, 2, 4, 4]
def baseStart_3696551 : Nat := 118140960795 + 3696551 * 2 ^ 59
def prefixEnd_3696551 : Nat := 4983230072969 + 3 ^ 40 * 3696551 * 2
def baseEnd_3696551 : Nat := 421801650412949324647195

theorem tailTrace_3696551 : CollatzResearch.WordTrace tailWord_3696551 prefixEnd_3696551 421801650412949324647195 := by
  unfold tailWord_3696551
  simp only [CollatzResearch.WordTrace]
  refine ⟨134824291231034522493905507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89882860820689681662603671 134824291231034522493905507)
  ·
    refine ⟨202236436846551783740858261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134824291231034522493905507 202236436846551783740858261)
    ·
      refine ⟨9479832977182114862852731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 202236436846551783740858261 9479832977182114862852731)
      ·
        refine ⟨14219749465773172294279097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9479832977182114862852731 14219749465773172294279097)
        ·
          refine ⟨10664812099329879220709323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14219749465773172294279097 10664812099329879220709323)
          ·
            refine ⟨15997218148994818831063985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10664812099329879220709323 15997218148994818831063985)
            ·
              refine ⟨11997913611746114123297989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15997218148994818831063985 11997913611746114123297989)
              ·
                refine ⟨2249608802202396398118373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11997913611746114123297989 2249608802202396398118373)
                ·
                  refine ⟨421801650412949324647195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2249608802202396398118373 421801650412949324647195)
                  ·
                    rfl

theorem cell22_3696551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 4].length) (baseStart_3696551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696551 prefixEnd_3696551 := by exact prefixLift 3696551
  have htrace : WordTrace (prefixWord ++ tailWord_3696551) baseStart_3696551 baseEnd_3696551 := by
    simpa [prefixWord, tailWord_3696551, baseEnd_3696551] using wordTrace_append hprefix tailTrace_3696551
  have hstable : (prefixWord ++ tailWord_3696551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696551).length < 2 ^ (prefixWord ++ tailWord_3696551).sum := by decide
  have hdescent : baseEnd_3696551 < baseStart_3696551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696598 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3696598 : Nat := 118140960795 + 3696598 * 2 ^ 59
def prefixEnd_3696598 : Nat := 4983230072969 + 3 ^ 40 * 3696598 * 2
def baseEnd_3696598 : Nat := 1265421040299355518016441

theorem tailTrace_3696598 : CollatzResearch.WordTrace tailWord_3696598 prefixEnd_3696598 1265421040299355518016441 := by
  unfold tailWord_3696598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8426625341366515595054153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89884003641242833013910965 8426625341366515595054153)
  ·
    refine ⟨6319969006024886696290615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8426625341366515595054153 6319969006024886696290615)
    ·
      refine ⟨9479953509037330044435923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6319969006024886696290615 9479953509037330044435923)
      ·
        refine ⟨14219930263555995066653885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9479953509037330044435923 14219930263555995066653885)
        ·
          refine ⟨5332473848833498149995207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14219930263555995066653885 5332473848833498149995207)
          ·
            refine ⟨7998710773250247224992811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5332473848833498149995207 7998710773250247224992811)
            ·
              refine ⟨11998066159875370837489217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998710773250247224992811 11998066159875370837489217)
              ·
                refine ⟨8998549619906528128116913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11998066159875370837489217 8998549619906528128116913)
                ·
                  refine ⟨6748912214929896096087685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8998549619906528128116913 6748912214929896096087685)
                  ·
                    refine ⟨1265421040299355518016441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6748912214929896096087685 1265421040299355518016441)
                    ·
                      rfl

theorem cell22_3696598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3696598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696598 prefixEnd_3696598 := by exact prefixLift 3696598
  have htrace : WordTrace (prefixWord ++ tailWord_3696598) baseStart_3696598 baseEnd_3696598 := by
    simpa [prefixWord, tailWord_3696598, baseEnd_3696598] using wordTrace_append hprefix tailTrace_3696598
  have hstable : (prefixWord ++ tailWord_3696598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696598).length < 2 ^ (prefixWord ++ tailWord_3696598).sum := by decide
  have hdescent : baseEnd_3696598 < baseStart_3696598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696611 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 3, 3]
def baseStart_3696611 : Nat := 118140960795 + 3696611 * 2 ^ 59
def prefixEnd_3696611 : Nat := 4983230072969 + 3 ^ 40 * 3696611 * 2
def baseEnd_3696611 : Nat := 1265425490465027817441401

theorem tailTrace_3696611 : CollatzResearch.WordTrace tailWord_3696611 prefixEnd_3696611 1265425490465027817441401 := by
  unfold tailWord_3696611
  simp only [CollatzResearch.WordTrace]
  refine ⟨134826479610817152741089687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89884319740544768494059791 134826479610817152741089687)
  ·
    refine ⟨202239719416225729111634531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134826479610817152741089687 202239719416225729111634531)
    ·
      refine ⟨303359579124338593667451797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202239719416225729111634531 303359579124338593667451797)
      ·
        refine ⟨14219980271453371578161803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 303359579124338593667451797 14219980271453371578161803)
        ·
          refine ⟨21329970407180057367242705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14219980271453371578161803 21329970407180057367242705)
          ·
            refine ⟨15997477805385043025432029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21329970407180057367242705 15997477805385043025432029)
            ·
              refine ⟨5999054177019391134537011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15997477805385043025432029 5999054177019391134537011)
              ·
                refine ⟨8998581265529086701805517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5999054177019391134537011 8998581265529086701805517)
                ·
                  refine ⟨3374467974573407513177069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8998581265529086701805517 3374467974573407513177069)
                  ·
                    refine ⟨1265425490465027817441401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3374467974573407513177069 1265425490465027817441401)
                    ·
                      rfl

theorem cell22_3696611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 3].length) (baseStart_3696611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696611 prefixEnd_3696611 := by exact prefixLift 3696611
  have htrace : WordTrace (prefixWord ++ tailWord_3696611) baseStart_3696611 baseEnd_3696611 := by
    simpa [prefixWord, tailWord_3696611, baseEnd_3696611] using wordTrace_append hprefix tailTrace_3696611
  have hstable : (prefixWord ++ tailWord_3696611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696611).length < 2 ^ (prefixWord ++ tailWord_3696611).sum := by decide
  have hdescent : baseEnd_3696611 < baseStart_3696611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696686 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_3696686 : Nat := 118140960795 + 3696686 * 2 ^ 59
def prefixEnd_3696686 : Nat := 4983230072969 + 3 ^ 40 * 3696686 * 2
def baseEnd_3696686 : Nat := 421817054832584207272057

theorem tailTrace_3696686 : CollatzResearch.WordTrace tailWord_3696686 prefixEnd_3696686 421817054832584207272057 := by
  unfold tailWord_3696686
  simp only [CollatzResearch.WordTrace]
  refine ⟨16853651885693180068758739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89886143390363627033379941 16853651885693180068758739)
  ·
    refine ⟨25280477828539770103138109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16853651885693180068758739 25280477828539770103138109)
    ·
      refine ⟨9480179185702413788676791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25280477828539770103138109 9480179185702413788676791)
      ·
        refine ⟨14220268778553620683015187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9480179185702413788676791 14220268778553620683015187)
        ·
          refine ⟨21330403167830431024522781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14220268778553620683015187 21330403167830431024522781)
          ·
            refine ⟨7998901187936411634196043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21330403167830431024522781 7998901187936411634196043)
            ·
              refine ⟨11998351781904617451294065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7998901187936411634196043 11998351781904617451294065)
              ·
                refine ⟨8998763836428463088470549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11998351781904617451294065 8998763836428463088470549)
                ·
                  refine ⟨421817054832584207272057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8998763836428463088470549 421817054832584207272057)
                  ·
                    rfl

theorem cell22_3696686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_3696686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696686 prefixEnd_3696686 := by exact prefixLift 3696686
  have htrace : WordTrace (prefixWord ++ tailWord_3696686) baseStart_3696686 baseEnd_3696686 := by
    simpa [prefixWord, tailWord_3696686, baseEnd_3696686] using wordTrace_append hprefix tailTrace_3696686
  have hstable : (prefixWord ++ tailWord_3696686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696686).length < 2 ^ (prefixWord ++ tailWord_3696686).sum := by decide
  have hdescent : baseEnd_3696686 < baseStart_3696686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696701 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_3696701 : Nat := 118140960795 + 3696701 * 2 ^ 59
def prefixEnd_3696701 : Nat := 4983230072969 + 3 ^ 40 * 3696701 * 2
def baseEnd_3696701 : Nat := 1265456299304297582691125

theorem tailTrace_3696701 : CollatzResearch.WordTrace tailWord_3696701 prefixEnd_3696701 1265456299304297582691125 := by
  unfold tailWord_3696701
  simp only [CollatzResearch.WordTrace]
  refine ⟨134829762180491098111865957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89886508120327398741243971 134829762180491098111865957)
  ·
    refine ⟨25280580408842080895974867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134829762180491098111865957 25280580408842080895974867)
    ·
      refine ⟨37920870613263121343962301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25280580408842080895974867 37920870613263121343962301)
      ·
        refine ⟨14220326479973670503985863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37920870613263121343962301 14220326479973670503985863)
        ·
          refine ⟨21330489719960505755978795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14220326479973670503985863 21330489719960505755978795)
          ·
            refine ⟨31995734579940758633968193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21330489719960505755978795 31995734579940758633968193)
            ·
              refine ⟨23996800934955568975476145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31995734579940758633968193 23996800934955568975476145)
              ·
                refine ⟨17997600701216676731607109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23996800934955568975476145 17997600701216676731607109)
                ·
                  refine ⟨3374550131478126887176333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17997600701216676731607109 3374550131478126887176333)
                  ·
                    refine ⟨1265456299304297582691125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3374550131478126887176333 1265456299304297582691125)
                    ·
                      rfl

theorem cell22_3696701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_3696701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696701 prefixEnd_3696701 := by exact prefixLift 3696701
  have htrace : WordTrace (prefixWord ++ tailWord_3696701) baseStart_3696701 baseEnd_3696701 := by
    simpa [prefixWord, tailWord_3696701, baseEnd_3696701] using wordTrace_append hprefix tailTrace_3696701
  have hstable : (prefixWord ++ tailWord_3696701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696701).length < 2 ^ (prefixWord ++ tailWord_3696701).sum := by decide
  have hdescent : baseEnd_3696701 < baseStart_3696701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696705 : List Nat := [1, 2, 5, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3696705 : Nat := 118140960795 + 3696705 * 2 ^ 59
def prefixEnd_3696705 : Nat := 4983230072969 + 3 ^ 40 * 3696705 * 2
def baseEnd_3696705 : Nat := 1265457668586042905591113

theorem tailTrace_3696705 : CollatzResearch.WordTrace tailWord_3696705 prefixEnd_3696705 1265457668586042905591113 := by
  unfold tailWord_3696705
  simp only [CollatzResearch.WordTrace]
  refine ⟨134829908072476606795011569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89886605381651071196674379 134829908072476606795011569)
  ·
    refine ⟨101122431054357455096258677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134829908072476606795011569 101122431054357455096258677)
    ·
      refine ⟨9480227911346011415274251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101122431054357455096258677 9480227911346011415274251)
      ·
        refine ⟨14220341867019017122911377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9480227911346011415274251 14220341867019017122911377)
        ·
          refine ⟨10665256400264262842183533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14220341867019017122911377 10665256400264262842183533)
          ·
            refine ⟨3999471150099098565818825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10665256400264262842183533 3999471150099098565818825)
            ·
              refine ⟨2999603362574323924364119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3999471150099098565818825 2999603362574323924364119)
              ·
                refine ⟨4499405043861485886546179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999603362574323924364119 4499405043861485886546179)
                ·
                  refine ⟨6749107565792228829819269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4499405043861485886546179 6749107565792228829819269)
                  ·
                    refine ⟨1265457668586042905591113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6749107565792228829819269 1265457668586042905591113)
                    ·
                      rfl

theorem cell22_3696705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3696705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696705 prefixEnd_3696705 := by exact prefixLift 3696705
  have htrace : WordTrace (prefixWord ++ tailWord_3696705) baseStart_3696705 baseEnd_3696705 := by
    simpa [prefixWord, tailWord_3696705, baseEnd_3696705] using wordTrace_append hprefix tailTrace_3696705
  have hstable : (prefixWord ++ tailWord_3696705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696705).length < 2 ^ (prefixWord ++ tailWord_3696705).sum := by decide
  have hdescent : baseEnd_3696705 < baseStart_3696705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696718 : List Nat := [4, 1, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_3696718 : Nat := 118140960795 + 3696718 * 2 ^ 59
def prefixEnd_3696718 : Nat := 4983230072969 + 3 ^ 40 * 3696718 * 2
def baseEnd_3696718 : Nat := 1265462118751715205016073

theorem tailTrace_3696718 : CollatzResearch.WordTrace tailWord_3696718 prefixEnd_3696718 1265462118751715205016073 := by
  unfold tailWord_3696718
  simp only [CollatzResearch.WordTrace]
  refine ⟨16853797777678688751904351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89886921480953006676823205 16853797777678688751904351)
  ·
    refine ⟨25280696666518033127856527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16853797777678688751904351 25280696666518033127856527)
    ·
      refine ⟨37921044999777049691784791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25280696666518033127856527 37921044999777049691784791)
      ·
        refine ⟨56881567499665574537677187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37921044999777049691784791 56881567499665574537677187)
        ·
          refine ⟨85322351249498361806515781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56881567499665574537677187 85322351249498361806515781)
          ·
            refine ⟨15997940859280942838721709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85322351249498361806515781 15997940859280942838721709)
            ·
              refine ⟨5999227822230353564520641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15997940859280942838721709 5999227822230353564520641)
              ·
                refine ⟨4499420866672765173390481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5999227822230353564520641 4499420866672765173390481)
                ·
                  refine ⟨3374565650004573880042861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4499420866672765173390481 3374565650004573880042861)
                  ·
                    refine ⟨1265462118751715205016073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3374565650004573880042861 1265462118751715205016073)
                    ·
                      rfl

theorem cell22_3696718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_3696718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696718 prefixEnd_3696718 := by exact prefixLift 3696718
  have htrace : WordTrace (prefixWord ++ tailWord_3696718) baseStart_3696718 baseEnd_3696718 := by
    simpa [prefixWord, tailWord_3696718, baseEnd_3696718] using wordTrace_append hprefix tailTrace_3696718
  have hstable : (prefixWord ++ tailWord_3696718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696718).length < 2 ^ (prefixWord ++ tailWord_3696718).sum := by decide
  have hdescent : baseEnd_3696718 < baseStart_3696718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696759 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 7]
def baseStart_3696759 : Nat := 118140960795 + 3696759 * 2 ^ 59
def prefixEnd_3696759 : Nat := 4983230072969 + 3 ^ 40 * 3696759 * 2
def baseEnd_3696759 : Nat := 421825384629868254913649

theorem tailTrace_3696759 : CollatzResearch.WordTrace tailWord_3696759 prefixEnd_3696759 421825384629868254913649 := by
  unfold tailWord_3696759
  simp only [CollatzResearch.WordTrace]
  refine ⟨134831877614280974017477331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89887918409520649344984887 134831877614280974017477331)
  ·
    refine ⟨202247816421421461026215997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134831877614280974017477331 202247816421421461026215997)
    ·
      refine ⟨75842931158033047884830999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202247816421421461026215997 75842931158033047884830999)
      ·
        refine ⟨113764396737049571827246499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75842931158033047884830999 113764396737049571827246499)
        ·
          refine ⟨170646595105574357740869749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113764396737049571827246499 170646595105574357740869749)
          ·
            refine ⟨15998118291147596038206539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170646595105574357740869749 15998118291147596038206539)
            ·
              refine ⟨23997177436721394057309809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15998118291147596038206539 23997177436721394057309809)
              ·
                refine ⟨17997883077541045542982357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23997177436721394057309809 17997883077541045542982357)
                ·
                  refine ⟨421825384629868254913649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17997883077541045542982357 421825384629868254913649)
                  ·
                    rfl

theorem cell22_3696759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 7].length) (baseStart_3696759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696759 prefixEnd_3696759 := by exact prefixLift 3696759
  have htrace : WordTrace (prefixWord ++ tailWord_3696759) baseStart_3696759 baseEnd_3696759 := by
    simpa [prefixWord, tailWord_3696759, baseEnd_3696759] using wordTrace_append hprefix tailTrace_3696759
  have hstable : (prefixWord ++ tailWord_3696759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696759).length < 2 ^ (prefixWord ++ tailWord_3696759).sum := by decide
  have hdescent : baseEnd_3696759 < baseStart_3696759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696776 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 7]
def baseStart_3696776 : Nat := 118140960795 + 3696776 * 2 ^ 59
def prefixEnd_3696776 : Nat := 4983230072969 + 3 ^ 40 * 3696776 * 2
def baseEnd_3696776 : Nat := 421827324445674129021965

theorem tailTrace_3696776 : CollatzResearch.WordTrace tailWord_3696776 prefixEnd_3696776 421827324445674129021965 := by
  unfold tailWord_3696776
  simp only [CollatzResearch.WordTrace]
  refine ⟨67416248827609692960423091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89888331770146257280564121 67416248827609692960423091)
  ·
    refine ⟨101124373241414539440634637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67416248827609692960423091 101124373241414539440634637)
    ·
      refine ⟨37921639965530452290237989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101124373241414539440634637 37921639965530452290237989)
      ·
        refine ⟨7110307493536959804419623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37921639965530452290237989 7110307493536959804419623)
        ·
          refine ⟨10665461240305439706629435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7110307493536959804419623 10665461240305439706629435)
          ·
            refine ⟨15998191860458159559944153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10665461240305439706629435 15998191860458159559944153)
            ·
              refine ⟨11998643895343619669958115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15998191860458159559944153 11998643895343619669958115)
              ·
                refine ⟨17997965843015429504937173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11998643895343619669958115 17997965843015429504937173)
                ·
                  refine ⟨421827324445674129021965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17997965843015429504937173 421827324445674129021965)
                  ·
                    rfl

theorem cell22_3696776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 7].length) (baseStart_3696776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696776 prefixEnd_3696776 := by exact prefixLift 3696776
  have htrace : WordTrace (prefixWord ++ tailWord_3696776) baseStart_3696776 baseEnd_3696776 := by
    simpa [prefixWord, tailWord_3696776, baseEnd_3696776] using wordTrace_append hprefix tailTrace_3696776
  have hstable : (prefixWord ++ tailWord_3696776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696776).length < 2 ^ (prefixWord ++ tailWord_3696776).sum := by decide
  have hdescent : baseEnd_3696776 < baseStart_3696776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696911 : List Nat := [1, 1, 2, 1, 1, 1, 3, 7, 5]
def baseStart_3696911 : Nat := 118140960795 + 3696911 * 2 ^ 59
def prefixEnd_3696911 : Nat := 4983230072969 + 3 ^ 40 * 3696911 * 2
def baseEnd_3696911 : Nat := 421842728865309011646827

theorem tailTrace_3696911 : CollatzResearch.WordTrace tailWord_3696911 prefixEnd_3696911 421842728865309011646827 := by
  unfold tailWord_3696911
  simp only [CollatzResearch.WordTrace]
  refine ⟨134837421509730303977010587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89891614339820202651340391 134837421509730303977010587)
  ·
    refine ⟨202256132264595455965515881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134837421509730303977010587 202256132264595455965515881)
    ·
      refine ⟨151692099198446591974136911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202256132264595455965515881 151692099198446591974136911)
      ·
        refine ⟨227538148797669887961205367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151692099198446591974136911 227538148797669887961205367)
        ·
          refine ⟨341307223196504831941808051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227538148797669887961205367 341307223196504831941808051)
          ·
            refine ⟨511960834794757247912712077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341307223196504831941808051 511960834794757247912712077)
            ·
              refine ⟨191985313048033967967267029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 511960834794757247912712077 191985313048033967967267029)
              ·
                refine ⟨4499655774563296124232821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 191985313048033967967267029 4499655774563296124232821)
                ·
                  refine ⟨421842728865309011646827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4499655774563296124232821 421842728865309011646827)
                  ·
                    rfl

theorem cell22_3696911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 5].length) (baseStart_3696911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696911 prefixEnd_3696911 := by exact prefixLift 3696911
  have htrace : WordTrace (prefixWord ++ tailWord_3696911) baseStart_3696911 baseEnd_3696911 := by
    simpa [prefixWord, tailWord_3696911, baseEnd_3696911] using wordTrace_append hprefix tailTrace_3696911
  have hstable : (prefixWord ++ tailWord_3696911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696911).length < 2 ^ (prefixWord ++ tailWord_3696911).sum := by decide
  have hdescent : baseEnd_3696911 < baseStart_3696911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696932 : List Nat := [2, 3, 1, 3, 1, 2, 3, 3, 1, 3]
def baseStart_3696932 : Nat := 118140960795 + 3696932 * 2 ^ 59
def prefixEnd_3696932 : Nat := 4983230072969 + 3 ^ 40 * 3696932 * 2
def baseEnd_3696932 : Nat := 1265535375325089980165417

theorem tailTrace_3696932 : CollatzResearch.WordTrace tailWord_3696932 prefixEnd_3696932 1265535375325089980165417 := by
  unfold tailWord_3696932
  simp only [CollatzResearch.WordTrace]
  refine ⟨67419093721327112281762525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89892124961769483042350033 67419093721327112281762525)
  ·
    refine ⟨25282160145497667105660947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67419093721327112281762525 25282160145497667105660947)
    ·
      refine ⟨37923240218246500658491421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25282160145497667105660947 37923240218246500658491421)
      ·
        refine ⟨14221215081842437746934283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37923240218246500658491421 14221215081842437746934283)
        ·
          refine ⟨21331822622763656620401425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14221215081842437746934283 21331822622763656620401425)
          ·
            refine ⟨15998866967072742465301069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21331822622763656620401425 15998866967072742465301069)
            ·
              refine ⟨5999575112652278424487901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15998866967072742465301069 5999575112652278424487901)
              ·
                refine ⟨2249840667244604409182963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5999575112652278424487901 2249840667244604409182963)
                ·
                  refine ⟨3374761000866906613774445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2249840667244604409182963 3374761000866906613774445)
                  ·
                    refine ⟨1265535375325089980165417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3374761000866906613774445 1265535375325089980165417)
                    ·
                      rfl

theorem cell22_3696932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_3696932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696932 prefixEnd_3696932 := by exact prefixLift 3696932
  have htrace : WordTrace (prefixWord ++ tailWord_3696932) baseStart_3696932 baseEnd_3696932 := by
    simpa [prefixWord, tailWord_3696932, baseEnd_3696932] using wordTrace_append hprefix tailTrace_3696932
  have hstable : (prefixWord ++ tailWord_3696932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696932).length < 2 ^ (prefixWord ++ tailWord_3696932).sum := by decide
  have hdescent : baseEnd_3696932 < baseStart_3696932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3696992 : List Nat := [2, 1, 1, 3, 5, 1, 3, 1, 1, 4]
def baseStart_3696992 : Nat := 118140960795 + 3696992 * 2 ^ 59
def prefixEnd_3696992 : Nat := 4983230072969 + 3 ^ 40 * 3696992 * 2
def baseEnd_3696992 : Nat := 1265555914551269823665233

theorem tailTrace_3696992 : CollatzResearch.WordTrace tailWord_3696992 prefixEnd_3696992 1265555914551269823665233 := by
  unfold tailWord_3696992
  simp only [CollatzResearch.WordTrace]
  refine ⟨67420187911218427405354615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89893583881624569873806153 67420187911218427405354615)
  ·
    refine ⟨101130281866827641108031923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67420187911218427405354615 101130281866827641108031923)
    ·
      refine ⟨151695422800241461662047885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101130281866827641108031923 151695422800241461662047885)
      ·
        refine ⟨56885783550090548123267957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151695422800241461662047885 56885783550090548123267957)
        ·
          refine ⟨5333042207820988886556371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56885783550090548123267957 5333042207820988886556371)
          ·
            refine ⟨7999563311731483329834557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5333042207820988886556371 7999563311731483329834557)
            ·
              refine ⟨2999836241899306248687959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7999563311731483329834557 2999836241899306248687959)
              ·
                refine ⟨4499754362848959373031939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2999836241899306248687959 4499754362848959373031939)
                ·
                  refine ⟨6749631544273439059547909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4499754362848959373031939 6749631544273439059547909)
                  ·
                    refine ⟨1265555914551269823665233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6749631544273439059547909 1265555914551269823665233)
                    ·
                      rfl

theorem cell22_3696992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 1, 4].length) (baseStart_3696992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3696992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3696992 prefixEnd_3696992 := by exact prefixLift 3696992
  have htrace : WordTrace (prefixWord ++ tailWord_3696992) baseStart_3696992 baseEnd_3696992 := by
    simpa [prefixWord, tailWord_3696992, baseEnd_3696992] using wordTrace_append hprefix tailTrace_3696992
  have hstable : (prefixWord ++ tailWord_3696992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3696992).length < 2 ^ (prefixWord ++ tailWord_3696992).sum := by decide
  have hdescent : baseEnd_3696992 < baseStart_3696992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3696992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697155 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 2, 4]
def baseStart_3697155 : Nat := 118140960795 + 3697155 * 2 ^ 59
def prefixEnd_3697155 : Nat := 4983230072969 + 3 ^ 40 * 3697155 * 2
def baseEnd_3697155 : Nat := 1265611712782391731839733

theorem tailTrace_3697155 : CollatzResearch.WordTrace tailWord_3697155 prefixEnd_3697155 1265611712782391731839733 := by
  unfold tailWord_3697155
  simp only [CollatzResearch.WordTrace]
  refine ⟨134846320920846333648892919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89897547280564222432595279 134846320920846333648892919)
  ·
    refine ⟨202269481381269500473339379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134846320920846333648892919 202269481381269500473339379)
    ·
      refine ⟨303404222071904250710009069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202269481381269500473339379 303404222071904250710009069)
      ·
        refine ⟨113776583276964094016253401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303404222071904250710009069 113776583276964094016253401)
        ·
          refine ⟨85332437457723070512190051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113776583276964094016253401 85332437457723070512190051)
          ·
            refine ⟨127998656186584605768285077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85332437457723070512190051 127998656186584605768285077)
            ·
              refine ⟨5999937008746153395388363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127998656186584605768285077 5999937008746153395388363)
              ·
                refine ⟨8999905513119230093082545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5999937008746153395388363 8999905513119230093082545)
                ·
                  refine ⟨6749929134839422569811909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8999905513119230093082545 6749929134839422569811909)
                  ·
                    refine ⟨1265611712782391731839733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6749929134839422569811909 1265611712782391731839733)
                    ·
                      rfl

theorem cell22_3697155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 4].length) (baseStart_3697155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697155 prefixEnd_3697155 := by exact prefixLift 3697155
  have htrace : WordTrace (prefixWord ++ tailWord_3697155) baseStart_3697155 baseEnd_3697155 := by
    simpa [prefixWord, tailWord_3697155, baseEnd_3697155] using wordTrace_append hprefix tailTrace_3697155
  have hstable : (prefixWord ++ tailWord_3697155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697155).length < 2 ^ (prefixWord ++ tailWord_3697155).sum := by decide
  have hdescent : baseEnd_3697155 < baseStart_3697155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697230 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_3697230 : Nat := 118140960795 + 3697230 * 2 ^ 59
def prefixEnd_3697230 : Nat := 4983230072969 + 3 ^ 40 * 3697230 * 2
def baseEnd_3697230 : Nat := 1265637386815116536214503

theorem tailTrace_3697230 : CollatzResearch.WordTrace tailWord_3697230 prefixEnd_3697230 1265637386815116536214503 := by
  unfold tailWord_3697230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16856132049446827682234143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89899370930383080971915429 16856132049446827682234143)
  ·
    refine ⟨25284198074170241523351215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16856132049446827682234143 25284198074170241523351215)
    ·
      refine ⟨37926297111255362285026823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25284198074170241523351215 37926297111255362285026823)
      ·
        refine ⟨56889445666883043427540235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37926297111255362285026823 56889445666883043427540235)
        ·
          refine ⟨85334168500324565141310353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56889445666883043427540235 85334168500324565141310353)
          ·
            refine ⟨64000626375243423855982765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85334168500324565141310353 64000626375243423855982765)
            ·
              refine ⟨24000234890716283945993537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64000626375243423855982765 24000234890716283945993537)
              ·
                refine ⟨18000176168037212959495153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24000234890716283945993537 18000176168037212959495153)
                ·
                  refine ⟨13500132126027909719621365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18000176168037212959495153 13500132126027909719621365)
                  ·
                    refine ⟨1265637386815116536214503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13500132126027909719621365 1265637386815116536214503)
                    ·
                      rfl

theorem cell22_3697230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_3697230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697230 prefixEnd_3697230 := by exact prefixLift 3697230
  have htrace : WordTrace (prefixWord ++ tailWord_3697230) baseStart_3697230 baseEnd_3697230 := by
    simpa [prefixWord, tailWord_3697230, baseEnd_3697230] using wordTrace_append hprefix tailTrace_3697230
  have hstable : (prefixWord ++ tailWord_3697230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697230).length < 2 ^ (prefixWord ++ tailWord_3697230).sum := by decide
  have hdescent : baseEnd_3697230 < baseStart_3697230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697260 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 6]
def baseStart_3697260 : Nat := 118140960795 + 3697260 * 2 ^ 59
def prefixEnd_3697260 : Nat := 4983230072969 + 3 ^ 40 * 3697260 * 2
def baseEnd_3697260 : Nat := 421882552142735485988137

theorem tailTrace_3697260 : CollatzResearch.WordTrace tailWord_3697260 prefixEnd_3697260 421882552142735485988137 := by
  unfold tailWord_3697260
  simp only [CollatzResearch.WordTrace]
  refine ⟨67425075292732968290732617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89900100390310624387643489 67425075292732968290732617)
  ·
    refine ⟨50568806469549726218049463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67425075292732968290732617 50568806469549726218049463)
    ·
      refine ⟨75853209704324589327074195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50568806469549726218049463 75853209704324589327074195)
      ·
        refine ⟨113779814556486883990611293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75853209704324589327074195 113779814556486883990611293)
        ·
          refine ⟨42667430458682581496479235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113779814556486883990611293 42667430458682581496479235)
          ·
            refine ⟨64001145688023872244718853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42667430458682581496479235 64001145688023872244718853)
            ·
              refine ⟨12000214816504476045884785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64001145688023872244718853 12000214816504476045884785)
              ·
                refine ⟨9000161112378357034413589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12000214816504476045884785 9000161112378357034413589)
                ·
                  refine ⟨421882552142735485988137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9000161112378357034413589 421882552142735485988137)
                  ·
                    rfl

theorem cell22_3697260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_3697260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697260 prefixEnd_3697260 := by exact prefixLift 3697260
  have htrace : WordTrace (prefixWord ++ tailWord_3697260) baseStart_3697260 baseEnd_3697260 := by
    simpa [prefixWord, tailWord_3697260, baseEnd_3697260] using wordTrace_append hprefix tailTrace_3697260
  have hstable : (prefixWord ++ tailWord_3697260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697260).length < 2 ^ (prefixWord ++ tailWord_3697260).sum := by decide
  have hdescent : baseEnd_3697260 < baseStart_3697260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697270 : List Nat := [5, 1, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_3697270 : Nat := 118140960795 + 3697270 * 2 ^ 59
def prefixEnd_3697270 : Nat := 4983230072969 + 3 ^ 40 * 3697270 * 2
def baseEnd_3697270 : Nat := 1265651079632569765214381

theorem tailTrace_3697270 : CollatzResearch.WordTrace tailWord_3697270 prefixEnd_3697270 1265651079632569765214381 := by
  unfold tailWord_3697270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8428157207214356768083079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89900343543619805526219509 8428157207214356768083079)
  ·
    refine ⟨12642235810821535152124619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8428157207214356768083079 12642235810821535152124619)
    ·
      refine ⟨18963353716232302728186929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12642235810821535152124619 18963353716232302728186929)
      ·
        refine ⟨14222515287174227046140197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18963353716232302728186929 14222515287174227046140197)
        ·
          refine ⟨2666721616345167571151287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14222515287174227046140197 2666721616345167571151287)
          ·
            refine ⟨4000082424517751356726931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2666721616345167571151287 4000082424517751356726931)
            ·
              refine ⟨6000123636776627035090397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4000082424517751356726931 6000123636776627035090397)
              ·
                refine ⟨2250046363791235138158899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6000123636776627035090397 2250046363791235138158899)
                ·
                  refine ⟨3375069545686852707238349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250046363791235138158899 3375069545686852707238349)
                  ·
                    refine ⟨1265651079632569765214381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3375069545686852707238349 1265651079632569765214381)
                    ·
                      rfl

theorem cell22_3697270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_3697270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697270 prefixEnd_3697270 := by exact prefixLift 3697270
  have htrace : WordTrace (prefixWord ++ tailWord_3697270) baseStart_3697270 baseEnd_3697270 := by
    simpa [prefixWord, tailWord_3697270, baseEnd_3697270] using wordTrace_append hprefix tailTrace_3697270
  have hstable : (prefixWord ++ tailWord_3697270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697270).length < 2 ^ (prefixWord ++ tailWord_3697270).sum := by decide
  have hdescent : baseEnd_3697270 < baseStart_3697270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697305 : List Nat := [1, 2, 1, 2, 1, 2, 6, 7]
def baseStart_3697305 : Nat := 118140960795 + 3697305 * 2 ^ 59
def prefixEnd_3697305 : Nat := 4983230072969 + 3 ^ 40 * 3697305 * 2
def baseEnd_3697305 : Nat := 140629228983093482287697

theorem tailTrace_3697305 : CollatzResearch.WordTrace tailWord_3697305 prefixEnd_3697305 140629228983093482287697 := by
  unfold tailWord_3697305
  simp only [CollatzResearch.WordTrace]
  refine ⟨134851791870302909266853369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89901194580201939511235579 134851791870302909266853369)
  ·
    refine ⟨101138843902727181950140027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134851791870302909266853369 101138843902727181950140027)
    ·
      refine ⟨151708265854090772925210041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101138843902727181950140027 151708265854090772925210041)
      ·
        refine ⟨113781199390568079693907531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151708265854090772925210041 113781199390568079693907531)
        ·
          refine ⟨170671799085852119540861297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113781199390568079693907531 170671799085852119540861297)
          ·
            refine ⟨128003849314389089655645973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170671799085852119540861297 128003849314389089655645973)
            ·
              refine ⟨6000180436611988577608405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128003849314389089655645973 6000180436611988577608405)
              ·
                refine ⟨140629228983093482287697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6000180436611988577608405 140629228983093482287697)
                ·
                  rfl

theorem cell22_3697305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 7].length) (baseStart_3697305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697305 prefixEnd_3697305 := by exact prefixLift 3697305
  have htrace : WordTrace (prefixWord ++ tailWord_3697305) baseStart_3697305 baseEnd_3697305 := by
    simpa [prefixWord, tailWord_3697305, baseEnd_3697305] using wordTrace_append hprefix tailTrace_3697305
  have hstable : (prefixWord ++ tailWord_3697305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697305).length < 2 ^ (prefixWord ++ tailWord_3697305).sum := by decide
  have hdescent : baseEnd_3697305 < baseStart_3697305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697345 : List Nat := [1, 2, 6, 2, 1, 2, 2, 2, 4]
def baseStart_3697345 : Nat := 118140960795 + 3697345 * 2 ^ 59
def prefixEnd_3697345 : Nat := 4983230072969 + 3 ^ 40 * 3697345 * 2
def baseEnd_3697345 : Nat := 421892251221764856529717

theorem tailTrace_3697345 : CollatzResearch.WordTrace tailWord_3697345 prefixEnd_3697345 421892251221764856529717 := by
  unfold tailWord_3697345
  simp only [CollatzResearch.WordTrace]
  refine ⟨134853250790157996098309489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89902167193438664065539659 134853250790157996098309489)
  ·
    refine ⟨101139938092618497073732117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134853250790157996098309489 101139938092618497073732117)
    ·
      refine ⟨4740934598091492050331193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101139938092618497073732117 4740934598091492050331193)
      ·
        refine ⟨3555700948568619037748395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4740934598091492050331193 3555700948568619037748395)
        ·
          refine ⟨5333551422852928556622593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3555700948568619037748395 5333551422852928556622593)
          ·
            refine ⟨4000163567139696417466945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5333551422852928556622593 4000163567139696417466945)
            ·
              refine ⟨3000122675354772313100209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4000163567139696417466945 3000122675354772313100209)
              ·
                refine ⟨2250092006516079234825157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3000122675354772313100209 2250092006516079234825157)
                ·
                  refine ⟨421892251221764856529717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2250092006516079234825157 421892251221764856529717)
                  ·
                    rfl

theorem cell22_3697345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 4].length) (baseStart_3697345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697345 prefixEnd_3697345 := by exact prefixLift 3697345
  have htrace : WordTrace (prefixWord ++ tailWord_3697345) baseStart_3697345 baseEnd_3697345 := by
    simpa [prefixWord, tailWord_3697345, baseEnd_3697345] using wordTrace_append hprefix tailTrace_3697345
  have hstable : (prefixWord ++ tailWord_3697345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697345).length < 2 ^ (prefixWord ++ tailWord_3697345).sum := by decide
  have hdescent : baseEnd_3697345 < baseStart_3697345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697367 : List Nat := [1, 1, 3, 2, 1, 4, 2, 3, 5]
def baseStart_3697367 : Nat := 118140960795 + 3697367 * 2 ^ 59
def prefixEnd_3697367 : Nat := 4983230072969 + 3 ^ 40 * 3697367 * 2
def baseEnd_3697367 : Nat := 421894761571631281846361

theorem tailTrace_3697367 : CollatzResearch.WordTrace tailWord_3697367 prefixEnd_3697367 421894761571631281846361 := by
  unfold tailWord_3697367
  simp only [CollatzResearch.WordTrace]
  refine ⟨134854053196078293855610355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89902702130718862570406903 134854053196078293855610355)
  ·
    refine ⟨202281079794117440783415533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134854053196078293855610355 202281079794117440783415533)
    ·
      refine ⟨75855404922794040293780825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202281079794117440783415533 75855404922794040293780825)
      ·
        refine ⟨56891553692095530220335619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75855404922794040293780825 56891553692095530220335619)
        ·
          refine ⟨85337330538143295330503429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56891553692095530220335619 85337330538143295330503429)
          ·
            refine ⟨16000749475901867874469393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85337330538143295330503429 16000749475901867874469393)
            ·
              refine ⟨12000562106926400905852045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16000749475901867874469393 12000562106926400905852045)
              ·
                refine ⟨4500210790097400339694517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12000562106926400905852045 4500210790097400339694517)
                ·
                  refine ⟨421894761571631281846361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4500210790097400339694517 421894761571631281846361)
                  ·
                    rfl

theorem cell22_3697367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 5].length) (baseStart_3697367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697367 prefixEnd_3697367 := by exact prefixLift 3697367
  have htrace : WordTrace (prefixWord ++ tailWord_3697367) baseStart_3697367 baseEnd_3697367 := by
    simpa [prefixWord, tailWord_3697367, baseEnd_3697367] using wordTrace_append hprefix tailTrace_3697367
  have hstable : (prefixWord ++ tailWord_3697367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697367).length < 2 ^ (prefixWord ++ tailWord_3697367).sum := by decide
  have hdescent : baseEnd_3697367 < baseStart_3697367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697395 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 10]
def baseStart_3697395 : Nat := 118140960795 + 3697395 * 2 ^ 59
def prefixEnd_3697395 : Nat := 4983230072969 + 3 ^ 40 * 3697395 * 2
def baseEnd_3697395 : Nat := 421897956562370368612999

theorem tailTrace_3697395 : CollatzResearch.WordTrace tailWord_3697395 prefixEnd_3697395 421897956562370368612999 := by
  unfold tailWord_3697395
  simp only [CollatzResearch.WordTrace]
  refine ⟨134855074439976854637629639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89903382959984569758419759 134855074439976854637629639)
  ·
    refine ⟨202282611659965281956444459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134855074439976854637629639 202282611659965281956444459)
    ·
      refine ⟨303423917489947922934666689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202282611659965281956444459 303423917489947922934666689)
      ·
        refine ⟨227567938117460942201000017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303423917489947922934666689 227567938117460942201000017)
        ·
          refine ⟨170675953588095706650750013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227567938117460942201000017 170675953588095706650750013)
          ·
            refine ⟨64003482595535889994031255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170675953588095706650750013 64003482595535889994031255)
            ·
              refine ⟨96005223893303834991046883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64003482595535889994031255 96005223893303834991046883)
              ·
                refine ⟨144007835839955752486570325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96005223893303834991046883 144007835839955752486570325)
                ·
                  refine ⟨421897956562370368612999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 144007835839955752486570325 421897956562370368612999)
                  ·
                    rfl

theorem cell22_3697395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 10].length) (baseStart_3697395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697395 prefixEnd_3697395 := by exact prefixLift 3697395
  have htrace : WordTrace (prefixWord ++ tailWord_3697395) baseStart_3697395 baseEnd_3697395 := by
    simpa [prefixWord, tailWord_3697395, baseEnd_3697395] using wordTrace_append hprefix tailTrace_3697395
  have hstable : (prefixWord ++ tailWord_3697395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697395).length < 2 ^ (prefixWord ++ tailWord_3697395).sum := by decide
  have hdescent : baseEnd_3697395 < baseStart_3697395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697431 : List Nat := [1, 1, 3, 4, 3, 1, 2, 2, 1, 4]
def baseStart_3697431 : Nat := 118140960795 + 3697431 * 2 ^ 59
def prefixEnd_3697431 : Nat := 4983230072969 + 3 ^ 40 * 3697431 * 2
def baseEnd_3697431 : Nat := 1265706193222819011938887

theorem tailTrace_3697431 : CollatzResearch.WordTrace tailWord_3697431 prefixEnd_3697431 1265706193222819011938887 := by
  unfold tailWord_3697431
  simp only [CollatzResearch.WordTrace]
  refine ⟨134856387467846432785940147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89904258311897621857293431 134856387467846432785940147)
  ·
    refine ⟨202284581201769649178910221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134856387467846432785940147 202284581201769649178910221)
    ·
      refine ⟨75856717950663618442091333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202284581201769649178910221 75856717950663618442091333)
      ·
        refine ⟨14223134615749428457892125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75856717950663618442091333 14223134615749428457892125)
        ·
          refine ⟨5333675480906035671709547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14223134615749428457892125 5333675480906035671709547)
          ·
            refine ⟨8000513221359053507564321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5333675480906035671709547 8000513221359053507564321)
            ·
              refine ⟨6000384916019290130673241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8000513221359053507564321 6000384916019290130673241)
              ·
                refine ⟨4500288687014467598004931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6000384916019290130673241 4500288687014467598004931)
                ·
                  refine ⟨6750433030521701397007397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500288687014467598004931 6750433030521701397007397)
                  ·
                    refine ⟨1265706193222819011938887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6750433030521701397007397 1265706193222819011938887)
                    ·
                      rfl

theorem cell22_3697431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_3697431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697431 prefixEnd_3697431 := by exact prefixLift 3697431
  have htrace : WordTrace (prefixWord ++ tailWord_3697431) baseStart_3697431 baseEnd_3697431 := by
    simpa [prefixWord, tailWord_3697431, baseEnd_3697431] using wordTrace_append hprefix tailTrace_3697431
  have hstable : (prefixWord ++ tailWord_3697431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697431).length < 2 ^ (prefixWord ++ tailWord_3697431).sum := by decide
  have hdescent : baseEnd_3697431 < baseStart_3697431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697459 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 2, 4]
def baseStart_3697459 : Nat := 118140960795 + 3697459 * 2 ^ 59
def prefixEnd_3697459 : Nat := 4983230072969 + 3 ^ 40 * 3697459 * 2
def baseEnd_3697459 : Nat := 1265715778195036272238801

theorem tailTrace_3697459 : CollatzResearch.WordTrace tailWord_3697459 prefixEnd_3697459 1265715778195036272238801 := by
  unfold tailWord_3697459
  simp only [CollatzResearch.WordTrace]
  refine ⟨134857408711744993567959431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89904939141163329045306287 134857408711744993567959431)
  ·
    refine ⟨202286113067617490351939147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134857408711744993567959431 202286113067617490351939147)
    ·
      refine ⟨303429169601426235527908721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202286113067617490351939147 303429169601426235527908721)
      ·
        refine ⟨227571877201069676645931541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303429169601426235527908721 227571877201069676645931541)
        ·
          refine ⟨10667431743800141092778041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 227571877201069676645931541 10667431743800141092778041)
          ·
            refine ⟨8000573807850105819583531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10667431743800141092778041 8000573807850105819583531)
            ·
              refine ⟨12000860711775158729375297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8000573807850105819583531 12000860711775158729375297)
              ·
                refine ⟨9000645533831369047031473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12000860711775158729375297 9000645533831369047031473)
                ·
                  refine ⟨6750484150373526785273605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9000645533831369047031473 6750484150373526785273605)
                  ·
                    refine ⟨1265715778195036272238801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6750484150373526785273605 1265715778195036272238801)
                    ·
                      rfl

theorem cell22_3697459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 4].length) (baseStart_3697459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697459 prefixEnd_3697459 := by exact prefixLift 3697459
  have htrace : WordTrace (prefixWord ++ tailWord_3697459) baseStart_3697459 baseEnd_3697459 := by
    simpa [prefixWord, tailWord_3697459, baseEnd_3697459] using wordTrace_append hprefix tailTrace_3697459
  have hstable : (prefixWord ++ tailWord_3697459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697459).length < 2 ^ (prefixWord ++ tailWord_3697459).sum := by decide
  have hdescent : baseEnd_3697459 < baseStart_3697459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697523 : List Nat := [1, 1, 1, 2, 2, 1, 8, 2, 1, 3]
def baseStart_3697523 : Nat := 118140960795 + 3697523 * 2 ^ 59
def prefixEnd_3697523 : Nat := 4983230072969 + 3 ^ 40 * 3697523 * 2
def baseEnd_3697523 : Nat := 1265737686702961438638605

theorem tailTrace_3697523 : CollatzResearch.WordTrace tailWord_3697523 prefixEnd_3697523 1265737686702961438638605 := by
  unfold tailWord_3697523
  simp only [CollatzResearch.WordTrace]
  refine ⟨134859742983513132498289223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89906495322342088332192815 134859742983513132498289223)
  ·
    refine ⟨202289614475269698747433835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134859742983513132498289223 202289614475269698747433835)
    ·
      refine ⟨303434421712904548121150753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202289614475269698747433835 303434421712904548121150753)
      ·
        refine ⟨227575816284678411090863065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303434421712904548121150753 227575816284678411090863065)
        ·
          refine ⟨170681862213508808318147299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227575816284678411090863065 170681862213508808318147299)
          ·
            refine ⟨256022793320263212477220949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170681862213508808318147299 256022793320263212477220949)
            ·
              refine ⟨3000267109221834521217433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 256022793320263212477220949 3000267109221834521217433)
              ·
                refine ⟨2250200331916375890913075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3000267109221834521217433 2250200331916375890913075)
                ·
                  refine ⟨3375300497874563836369613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250200331916375890913075 3375300497874563836369613)
                  ·
                    refine ⟨1265737686702961438638605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3375300497874563836369613 1265737686702961438638605)
                    ·
                      rfl

theorem cell22_3697523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 1, 3].length) (baseStart_3697523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697523 prefixEnd_3697523 := by exact prefixLift 3697523
  have htrace : WordTrace (prefixWord ++ tailWord_3697523) baseStart_3697523 baseEnd_3697523 := by
    simpa [prefixWord, tailWord_3697523, baseEnd_3697523] using wordTrace_append hprefix tailTrace_3697523
  have hstable : (prefixWord ++ tailWord_3697523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697523).length < 2 ^ (prefixWord ++ tailWord_3697523).sum := by decide
  have hdescent : baseEnd_3697523 < baseStart_3697523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697547 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 8]
def baseStart_3697547 : Nat := 118140960795 + 3697547 * 2 ^ 59
def prefixEnd_3697547 : Nat := 4983230072969 + 3 ^ 40 * 3697547 * 2
def baseEnd_3697547 : Nat := 421915300797811125346177

theorem tailTrace_3697547 : CollatzResearch.WordTrace tailWord_3697547 prefixEnd_3697547 421915300797811125346177 := by
  unfold tailWord_3697547
  simp only [CollatzResearch.WordTrace]
  refine ⟨134860618335426184597162895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89907078890284123064775263 134860618335426184597162895)
  ·
    refine ⟨202290927503139276895744343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134860618335426184597162895 202290927503139276895744343)
    ·
      refine ⟨303436391254708915343616515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202290927503139276895744343 303436391254708915343616515)
      ·
        refine ⟨455154586882063373015424773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303436391254708915343616515 455154586882063373015424773)
        ·
          refine ⟨85341485040386882440392145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 455154586882063373015424773 85341485040386882440392145)
          ·
            refine ⟨64006113780290161830294109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85341485040386882440392145 64006113780290161830294109)
            ·
              refine ⟨24002292667608810686360291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64006113780290161830294109 24002292667608810686360291)
              ·
                refine ⟨36003439001413216029540437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24002292667608810686360291 36003439001413216029540437)
                ·
                  refine ⟨421915300797811125346177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36003439001413216029540437 421915300797811125346177)
                  ·
                    rfl

theorem cell22_3697547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 8].length) (baseStart_3697547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697547 prefixEnd_3697547 := by exact prefixLift 3697547
  have htrace : WordTrace (prefixWord ++ tailWord_3697547) baseStart_3697547 baseEnd_3697547 := by
    simpa [prefixWord, tailWord_3697547, baseEnd_3697547] using wordTrace_append hprefix tailTrace_3697547
  have hstable : (prefixWord ++ tailWord_3697547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697547).length < 2 ^ (prefixWord ++ tailWord_3697547).sum := by decide
  have hdescent : baseEnd_3697547 < baseStart_3697547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697579 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 4, 3]
def baseStart_3697579 : Nat := 118140960795 + 3697579 * 2 ^ 59
def prefixEnd_3697579 : Nat := 4983230072969 + 3 ^ 40 * 3697579 * 2
def baseEnd_3697579 : Nat := 1265756856647395959238433

theorem tailTrace_3697579 : CollatzResearch.WordTrace tailWord_3697579 prefixEnd_3697579 1265756856647395959238433 := by
  unfold tailWord_3697579
  simp only [CollatzResearch.WordTrace]
  refine ⟨134861785471310254062327791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89907856980873502708218527 134861785471310254062327791)
  ·
    refine ⟨202292678206965381093491687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134861785471310254062327791 202292678206965381093491687)
    ·
      refine ⟨303439017310448071640237531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202292678206965381093491687 303439017310448071640237531)
      ·
        refine ⟨455158525965672107460356297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303439017310448071640237531 455158525965672107460356297)
        ·
          refine ⟨341368894474254080595267223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455158525965672107460356297 341368894474254080595267223)
          ·
            refine ⟨512053341711381120892900835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341368894474254080595267223 512053341711381120892900835)
            ·
              refine ⟨768080012567071681339351253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 512053341711381120892900835 768080012567071681339351253)
              ·
                refine ⟨18001875294540742531391045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 768080012567071681339351253 18001875294540742531391045)
                ·
                  refine ⟨3375351617726389224635821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18001875294540742531391045 3375351617726389224635821)
                  ·
                    refine ⟨1265756856647395959238433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3375351617726389224635821 1265756856647395959238433)
                    ·
                      rfl

theorem cell22_3697579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 3].length) (baseStart_3697579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697579 prefixEnd_3697579 := by exact prefixLift 3697579
  have htrace : WordTrace (prefixWord ++ tailWord_3697579) baseStart_3697579 baseEnd_3697579 := by
    simpa [prefixWord, tailWord_3697579, baseEnd_3697579] using wordTrace_append hprefix tailTrace_3697579
  have hstable : (prefixWord ++ tailWord_3697579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697579).length < 2 ^ (prefixWord ++ tailWord_3697579).sum := by decide
  have hdescent : baseEnd_3697579 < baseStart_3697579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697703 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3697703 : Nat := 118140960795 + 3697703 * 2 ^ 59
def prefixEnd_3697703 : Nat := 4983230072969 + 3 ^ 40 * 3697703 * 2
def baseEnd_3697703 : Nat := 1265799304381500969138053

theorem tailTrace_3697703 : CollatzResearch.WordTrace tailWord_3697703 prefixEnd_3697703 1265799304381500969138053 := by
  unfold tailWord_3697703
  simp only [CollatzResearch.WordTrace]
  refine ⟨134866308122861023239841763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89910872081907348826561175 134866308122861023239841763)
  ·
    refine ⟨202299462184291534859762645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134866308122861023239841763 202299462184291534859762645)
    ·
      refine ⟨4741393644944332848275687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 202299462184291534859762645 4741393644944332848275687)
      ·
        refine ⟨7112090467416499272413531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4741393644944332848275687 7112090467416499272413531)
        ·
          refine ⟨10668135701124748908620297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7112090467416499272413531 10668135701124748908620297)
          ·
            refine ⟨8001101775843561681465223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10668135701124748908620297 8001101775843561681465223)
            ·
              refine ⟨12001652663765342522197835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8001101775843561681465223 12001652663765342522197835)
              ·
                refine ⟨18002478995648013783296753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12001652663765342522197835 18002478995648013783296753)
                ·
                  refine ⟨13501859246736010337472565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18002478995648013783296753 13501859246736010337472565)
                  ·
                    refine ⟨1265799304381500969138053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13501859246736010337472565 1265799304381500969138053)
                    ·
                      rfl

theorem cell22_3697703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3697703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697703 prefixEnd_3697703 := by exact prefixLift 3697703
  have htrace : WordTrace (prefixWord ++ tailWord_3697703) baseStart_3697703 baseEnd_3697703 := by
    simpa [prefixWord, tailWord_3697703, baseEnd_3697703] using wordTrace_append hprefix tailTrace_3697703
  have hstable : (prefixWord ++ tailWord_3697703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697703).length < 2 ^ (prefixWord ++ tailWord_3697703).sum := by decide
  have hdescent : baseEnd_3697703 < baseStart_3697703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697718 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3697718 : Nat := 118140960795 + 3697718 * 2 ^ 59
def prefixEnd_3697718 : Nat := 4983230072969 + 3 ^ 40 * 3697718 * 2
def baseEnd_3697718 : Nat := 1265804439188045930013007

theorem tailTrace_3697718 : CollatzResearch.WordTrace tailWord_3697718 prefixEnd_3697718 1265804439188045930013007 := by
  unfold tailWord_3697718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429178451112917550102363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89911236811871120534425205 8429178451112917550102363)
  ·
    refine ⟨12643767676669376325153545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8429178451112917550102363 12643767676669376325153545)
    ·
      refine ⟨9482825757502032243865159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12643767676669376325153545 9482825757502032243865159)
      ·
        refine ⟨14224238636253048365797739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9482825757502032243865159 14224238636253048365797739)
        ·
          refine ⟨21336357954379572548696609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14224238636253048365797739 21336357954379572548696609)
          ·
            refine ⟨16002268465784679411522457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21336357954379572548696609 16002268465784679411522457)
            ·
              refine ⟨12001701349338509558641843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16002268465784679411522457 12001701349338509558641843)
              ·
                refine ⟨18002552024007764337962765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12001701349338509558641843 18002552024007764337962765)
                ·
                  refine ⟨6750957009002911626736037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18002552024007764337962765 6750957009002911626736037)
                  ·
                    refine ⟨1265804439188045930013007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6750957009002911626736037 1265804439188045930013007)
                    ·
                      rfl

theorem cell22_3697718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3697718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697718 prefixEnd_3697718 := by exact prefixLift 3697718
  have htrace : WordTrace (prefixWord ++ tailWord_3697718) baseStart_3697718 baseEnd_3697718 := by
    simpa [prefixWord, tailWord_3697718, baseEnd_3697718] using wordTrace_append hprefix tailTrace_3697718
  have hstable : (prefixWord ++ tailWord_3697718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697718).length < 2 ^ (prefixWord ++ tailWord_3697718).sum := by decide
  have hdescent : baseEnd_3697718 < baseStart_3697718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697731 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 4, 3]
def baseStart_3697731 : Nat := 118140960795 + 3697731 * 2 ^ 59
def prefixEnd_3697731 : Nat := 4983230072969 + 3 ^ 40 * 3697731 * 2
def baseEnd_3697731 : Nat := 1265808889353718229437967

theorem tailTrace_3697731 : CollatzResearch.WordTrace tailWord_3697731 prefixEnd_3697731 1265808889353718229437967 := by
  unfold tailWord_3697731
  simp only [CollatzResearch.WordTrace]
  refine ⟨134867329366759584021861047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89911552911173056014574031 134867329366759584021861047)
  ·
    refine ⟨202300994050139376032791571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134867329366759584021861047 202300994050139376032791571)
    ·
      refine ⟨303451491075209064049187357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202300994050139376032791571 303451491075209064049187357)
      ·
        refine ⟨113794309153203399018445259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303451491075209064049187357 113794309153203399018445259)
        ·
          refine ⟨170691463729805098527667889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113794309153203399018445259 170691463729805098527667889)
          ·
            refine ⟨128018597797353823895750917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170691463729805098527667889 128018597797353823895750917)
            ·
              refine ⟨24003487087003841980453297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128018597797353823895750917 24003487087003841980453297)
              ·
                refine ⟨18002615315252881485339973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24003487087003841980453297 18002615315252881485339973)
                ·
                  refine ⟨3375490371609915278501245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18002615315252881485339973 3375490371609915278501245)
                  ·
                    refine ⟨1265808889353718229437967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3375490371609915278501245 1265808889353718229437967)
                    ·
                      rfl

theorem cell22_3697731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 3].length) (baseStart_3697731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697731 prefixEnd_3697731 := by exact prefixLift 3697731
  have htrace : WordTrace (prefixWord ++ tailWord_3697731) baseStart_3697731 baseEnd_3697731 := by
    simpa [prefixWord, tailWord_3697731, baseEnd_3697731] using wordTrace_append hprefix tailTrace_3697731
  have hstable : (prefixWord ++ tailWord_3697731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697731).length < 2 ^ (prefixWord ++ tailWord_3697731).sum := by decide
  have hdescent : baseEnd_3697731 < baseStart_3697731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697735 : List Nat := [1, 1, 4, 1, 3, 4, 2, 1, 1, 4]
def baseStart_3697735 : Nat := 118140960795 + 3697735 * 2 ^ 59
def prefixEnd_3697735 : Nat := 4983230072969 + 3 ^ 40 * 3697735 * 2
def baseEnd_3697735 : Nat := 1265810258635463552337955

theorem tailTrace_3697735 : CollatzResearch.WordTrace tailWord_3697735 prefixEnd_3697735 1265810258635463552337955 := by
  unfold tailWord_3697735
  simp only [CollatzResearch.WordTrace]
  refine ⟨134867475258745092705006659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89911650172496728470004439 134867475258745092705006659)
  ·
    refine ⟨202301212888117639057509989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134867475258745092705006659 202301212888117639057509989)
    ·
      refine ⟨37931477416522057323283123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202301212888117639057509989 37931477416522057323283123)
      ·
        refine ⟨56897216124783085984924685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37931477416522057323283123 56897216124783085984924685)
        ·
          refine ⟨21336456046793657244346757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56897216124783085984924685 21336456046793657244346757)
          ·
            refine ⟨4000585508773810733315017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21336456046793657244346757 4000585508773810733315017)
            ·
              refine ⟨3000439131580358049986263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4000585508773810733315017 3000439131580358049986263)
              ·
                refine ⟨4500658697370537074979395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3000439131580358049986263 4500658697370537074979395)
                ·
                  refine ⟨6750988046055805612469093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500658697370537074979395 6750988046055805612469093)
                  ·
                    refine ⟨1265810258635463552337955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6750988046055805612469093 1265810258635463552337955)
                    ·
                      rfl

theorem cell22_3697735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_3697735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697735 prefixEnd_3697735 := by exact prefixLift 3697735
  have htrace : WordTrace (prefixWord ++ tailWord_3697735) baseStart_3697735 baseEnd_3697735 := by
    simpa [prefixWord, tailWord_3697735, baseEnd_3697735] using wordTrace_append hprefix tailTrace_3697735
  have hstable : (prefixWord ++ tailWord_3697735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697735).length < 2 ^ (prefixWord ++ tailWord_3697735).sum := by decide
  have hdescent : baseEnd_3697735 < baseStart_3697735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697765 : List Nat := [1, 3, 1, 3, 2, 1, 5, 1, 2, 3]
def baseStart_3697765 : Nat := 118140960795 + 3697765 * 2 ^ 59
def prefixEnd_3697765 : Nat := 4983230072969 + 3 ^ 40 * 3697765 * 2
def baseEnd_3697765 : Nat := 1265820528248553474087863

theorem tailTrace_3697765 : CollatzResearch.WordTrace tailWord_3697765 prefixEnd_3697765 1265820528248553474087863 := by
  unfold tailWord_3697765
  simp only [CollatzResearch.WordTrace]
  refine ⟨134868569448636407828598749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89912379632424271885732499 134868569448636407828598749)
  ·
    refine ⟨50575713543238652935724531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134868569448636407828598749 50575713543238652935724531)
    ·
      refine ⟨75863570314857979403586797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50575713543238652935724531 75863570314857979403586797)
      ·
        refine ⟨28448838868071742276345049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75863570314857979403586797 28448838868071742276345049)
        ·
          refine ⟨21336629151053806707258787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28448838868071742276345049 21336629151053806707258787)
          ·
            refine ⟨32004943726580710060888181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21336629151053806707258787 32004943726580710060888181)
            ·
              refine ⟨3000463474366941568208267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32004943726580710060888181 3000463474366941568208267)
              ·
                refine ⟨4500695211550412352312401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3000463474366941568208267 4500695211550412352312401)
                ·
                  refine ⟨3375521408662809264234301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4500695211550412352312401 3375521408662809264234301)
                  ·
                    refine ⟨1265820528248553474087863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3375521408662809264234301 1265820528248553474087863)
                    ·
                      rfl

theorem cell22_3697765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_3697765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697765 prefixEnd_3697765 := by exact prefixLift 3697765
  have htrace : WordTrace (prefixWord ++ tailWord_3697765) baseStart_3697765 baseEnd_3697765 := by
    simpa [prefixWord, tailWord_3697765, baseEnd_3697765] using wordTrace_append hprefix tailTrace_3697765
  have hstable : (prefixWord ++ tailWord_3697765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697765).length < 2 ^ (prefixWord ++ tailWord_3697765).sum := by decide
  have hdescent : baseEnd_3697765 < baseStart_3697765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697810 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_3697810 : Nat := 118140960795 + 3697810 * 2 ^ 59
def prefixEnd_3697810 : Nat := 4983230072969 + 3 ^ 40 * 3697810 * 2
def baseEnd_3697810 : Nat := 1265835932668188356712725

theorem tailTrace_3697810 : CollatzResearch.WordTrace tailWord_3697810 prefixEnd_3697810 1265835932668188356712725 := by
  unfold tailWord_3697810
  simp only [CollatzResearch.WordTrace]
  refine ⟨33717552683368345128496721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89913473822315587009324589 33717552683368345128496721)
  ·
    refine ⟨25288164512526258846372541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33717552683368345128496721 25288164512526258846372541)
    ·
      refine ⟨9483061692197347067389703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25288164512526258846372541 9483061692197347067389703)
      ·
        refine ⟨14224592538296020601084555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9483061692197347067389703 14224592538296020601084555)
        ·
          refine ⟨21336888807444030901626833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14224592538296020601084555 21336888807444030901626833)
          ·
            refine ⟨16002666605583023176220125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21336888807444030901626833 16002666605583023176220125)
            ·
              refine ⟨6000999977093633691082547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16002666605583023176220125 6000999977093633691082547)
              ·
                refine ⟨9001499965640450536623821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6000999977093633691082547 9001499965640450536623821)
                ·
                  refine ⟨3375562487115168951233933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9001499965640450536623821 3375562487115168951233933)
                  ·
                    refine ⟨1265835932668188356712725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3375562487115168951233933 1265835932668188356712725)
                    ·
                      rfl

theorem cell22_3697810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_3697810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697810 prefixEnd_3697810 := by exact prefixLift 3697810
  have htrace : WordTrace (prefixWord ++ tailWord_3697810) baseStart_3697810 baseEnd_3697810 := by
    simpa [prefixWord, tailWord_3697810, baseEnd_3697810] using wordTrace_append hprefix tailTrace_3697810
  have hstable : (prefixWord ++ tailWord_3697810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697810).length < 2 ^ (prefixWord ++ tailWord_3697810).sum := by decide
  have hdescent : baseEnd_3697810 < baseStart_3697810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697821 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3697821 : Nat := 118140960795 + 3697821 * 2 ^ 59
def prefixEnd_3697821 : Nat := 4983230072969 + 3 ^ 40 * 3697821 * 2
def baseEnd_3697821 : Nat := 1265839698192987994687691

theorem tailTrace_3697821 : CollatzResearch.WordTrace tailWord_3697821 prefixEnd_3697821 1265839698192987994687691 := by
  unfold tailWord_3697821
  simp only [CollatzResearch.WordTrace]
  refine ⟨134870611936433529392637317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89913741290955686261758211 134870611936433529392637317)
  ·
    refine ⟨25288239738081286761119497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134870611936433529392637317 25288239738081286761119497)
    ·
      refine ⟨18966179803560965070839623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25288239738081286761119497 18966179803560965070839623)
      ·
        refine ⟨28449269705341447606259435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18966179803560965070839623 28449269705341447606259435)
        ·
          refine ⟨42673904558012171409389153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28449269705341447606259435 42673904558012171409389153)
          ·
            refine ⟨32005428418509128557041865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42673904558012171409389153 32005428418509128557041865)
            ·
              refine ⟨24004071313881846417781399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32005428418509128557041865 24004071313881846417781399)
              ·
                refine ⟨36006106970822769626672099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24004071313881846417781399 36006106970822769626672099)
                ·
                  refine ⟨54009160456234154440008149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36006106970822769626672099 54009160456234154440008149)
                  ·
                    refine ⟨1265839698192987994687691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54009160456234154440008149 1265839698192987994687691)
                    ·
                      rfl

theorem cell22_3697821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3697821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697821 prefixEnd_3697821 := by exact prefixLift 3697821
  have htrace : WordTrace (prefixWord ++ tailWord_3697821) baseStart_3697821 baseEnd_3697821 := by
    simpa [prefixWord, tailWord_3697821, baseEnd_3697821] using wordTrace_append hprefix tailTrace_3697821
  have hstable : (prefixWord ++ tailWord_3697821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697821).length < 2 ^ (prefixWord ++ tailWord_3697821).sum := by decide
  have hdescent : baseEnd_3697821 < baseStart_3697821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697853 : List Nat := [1, 4, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_3697853 : Nat := 118140960795 + 3697853 * 2 ^ 59
def prefixEnd_3697853 : Nat := 4983230072969 + 3 ^ 40 * 3697853 * 2
def baseEnd_3697853 : Nat := 1265850652446950577887593

theorem tailTrace_3697853 : CollatzResearch.WordTrace tailWord_3697853 prefixEnd_3697853 1265850652446950577887593 := by
  unfold tailWord_3697853
  simp only [CollatzResearch.WordTrace]
  refine ⟨134871779072317598857802213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89914519381545065905201475 134871779072317598857802213)
  ·
    refine ⟨25288458576059549785837915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134871779072317598857802213 25288458576059549785837915)
    ·
      refine ⟨37932687864089324678756873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25288458576059549785837915 37932687864089324678756873)
      ·
        refine ⟨28449515898066993509067655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37932687864089324678756873 28449515898066993509067655)
        ·
          refine ⟨42674273847100490263601483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28449515898066993509067655 42674273847100490263601483)
          ·
            refine ⟨64011410770650735395402225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42674273847100490263601483 64011410770650735395402225)
            ·
              refine ⟨48008558077988051546551669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64011410770650735395402225 48008558077988051546551669)
              ·
                refine ⟨4500802319811379832489219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48008558077988051546551669 4500802319811379832489219)
                ·
                  refine ⟨6751203479717069748733829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4500802319811379832489219 6751203479717069748733829)
                  ·
                    refine ⟨1265850652446950577887593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6751203479717069748733829 1265850652446950577887593)
                    ·
                      rfl

theorem cell22_3697853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_3697853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697853 prefixEnd_3697853 := by exact prefixLift 3697853
  have htrace : WordTrace (prefixWord ++ tailWord_3697853) baseStart_3697853 baseEnd_3697853 := by
    simpa [prefixWord, tailWord_3697853, baseEnd_3697853] using wordTrace_append hprefix tailTrace_3697853
  have hstable : (prefixWord ++ tailWord_3697853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697853).length < 2 ^ (prefixWord ++ tailWord_3697853).sum := by decide
  have hdescent : baseEnd_3697853 < baseStart_3697853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697881 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 1, 6]
def baseStart_3697881 : Nat := 118140960795 + 3697881 * 2 ^ 59
def prefixEnd_3697881 : Nat := 4983230072969 + 3 ^ 40 * 3697881 * 2
def baseEnd_3697881 : Nat := 1265860237419167838187507

theorem tailTrace_3697881 : CollatzResearch.WordTrace tailWord_3697881 prefixEnd_3697881 1265860237419167838187507 := by
  unfold tailWord_3697881
  simp only [CollatzResearch.WordTrace]
  refine ⟨134872800316216159639821497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89915200210810773093214331 134872800316216159639821497)
  ·
    refine ⟨101154600237162119729866123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134872800316216159639821497 101154600237162119729866123)
    ·
      refine ⟨151731900355743179594799185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101154600237162119729866123 151731900355743179594799185)
      ·
        refine ⟨113798925266807384696099389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151731900355743179594799185 113798925266807384696099389)
        ·
          refine ⟨42674596975052769261037271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113798925266807384696099389 42674596975052769261037271)
          ·
            refine ⟨64011895462579153891555907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42674596975052769261037271 64011895462579153891555907)
            ·
              refine ⟨96017843193868730837333861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64011895462579153891555907 96017843193868730837333861)
              ·
                refine ⟨18003345598850387032000099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96017843193868730837333861 18003345598850387032000099)
                ·
                  refine ⟨27005018398275580548000149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18003345598850387032000099 27005018398275580548000149)
                  ·
                    refine ⟨1265860237419167838187507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27005018398275580548000149 1265860237419167838187507)
                    ·
                      rfl

theorem cell22_3697881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_3697881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697881 prefixEnd_3697881 := by exact prefixLift 3697881
  have htrace : WordTrace (prefixWord ++ tailWord_3697881) baseStart_3697881 baseEnd_3697881 := by
    simpa [prefixWord, tailWord_3697881, baseEnd_3697881] using wordTrace_append hprefix tailTrace_3697881
  have hstable : (prefixWord ++ tailWord_3697881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697881).length < 2 ^ (prefixWord ++ tailWord_3697881).sum := by decide
  have hdescent : baseEnd_3697881 < baseStart_3697881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697885 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 6]
def baseStart_3697885 : Nat := 118140960795 + 3697885 * 2 ^ 59
def prefixEnd_3697885 : Nat := 4983230072969 + 3 ^ 40 * 3697885 * 2
def baseEnd_3697885 : Nat := 421953868900304387029165

theorem tailTrace_3697885 : CollatzResearch.WordTrace tailWord_3697885 prefixEnd_3697885 421953868900304387029165 := by
  unfold tailWord_3697885
  simp only [CollatzResearch.WordTrace]
  refine ⟨134872946208201668322967109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89915297472134445548644739 134872946208201668322967109)
  ·
    refine ⟨25288677414037812810556333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134872946208201668322967109 25288677414037812810556333)
    ·
      refine ⟨9483254030264179803958625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25288677414037812810556333 9483254030264179803958625)
      ·
        refine ⟨7112440522698134852968969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9483254030264179803958625 7112440522698134852968969)
        ·
          refine ⟨5334330392023601139726727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7112440522698134852968969 5334330392023601139726727)
          ·
            refine ⟨8001495588035401709590091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5334330392023601139726727 8001495588035401709590091)
            ·
              refine ⟨12002243382053102564385137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8001495588035401709590091 12002243382053102564385137)
              ·
                refine ⟨9001682536539826923288853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12002243382053102564385137 9001682536539826923288853)
                ·
                  refine ⟨421953868900304387029165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9001682536539826923288853 421953868900304387029165)
                  ·
                    rfl

theorem cell22_3697885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_3697885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697885 prefixEnd_3697885 := by exact prefixLift 3697885
  have htrace : WordTrace (prefixWord ++ tailWord_3697885) baseStart_3697885 baseEnd_3697885 := by
    simpa [prefixWord, tailWord_3697885, baseEnd_3697885] using wordTrace_append hprefix tailTrace_3697885
  have hstable : (prefixWord ++ tailWord_3697885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697885).length < 2 ^ (prefixWord ++ tailWord_3697885).sum := by decide
  have hdescent : baseEnd_3697885 < baseStart_3697885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3697898 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_3697898 : Nat := 118140960795 + 3697898 * 2 ^ 59
def prefixEnd_3697898 : Nat := 4983230072969 + 3 ^ 40 * 3697898 * 2
def baseEnd_3697898 : Nat := 1265866056866585460512455

theorem tailTrace_3697898 : CollatzResearch.WordTrace tailWord_3697898 prefixEnd_3697898 1265866056866585460512455 := by
  unfold tailWord_3697898
  simp only [CollatzResearch.WordTrace]
  refine ⟨33718355089288642885797587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89915613571436381028793565 33718355089288642885797587)
  ·
    refine ⟨50577532633932964328696381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33718355089288642885797587 50577532633932964328696381)
    ·
      refine ⟨18966574737724861623261143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50577532633932964328696381 18966574737724861623261143)
      ·
        refine ⟨28449862106587292434891715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18966574737724861623261143 28449862106587292434891715)
        ·
          refine ⟨42674793159880938652337573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28449862106587292434891715 42674793159880938652337573)
          ·
            refine ⟨8001523717477675997313295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42674793159880938652337573 8001523717477675997313295)
            ·
              refine ⟨12002285576216513995969943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8001523717477675997313295 12002285576216513995969943)
              ·
                refine ⟨18003428364324770993954915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12002285576216513995969943 18003428364324770993954915)
                ·
                  refine ⟨27005142546487156490932373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18003428364324770993954915 27005142546487156490932373)
                  ·
                    refine ⟨1265866056866585460512455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27005142546487156490932373 1265866056866585460512455)
                    ·
                      rfl

theorem cell22_3697898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_3697898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3697898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3697898 prefixEnd_3697898 := by exact prefixLift 3697898
  have htrace : WordTrace (prefixWord ++ tailWord_3697898) baseStart_3697898 baseEnd_3697898 := by
    simpa [prefixWord, tailWord_3697898, baseEnd_3697898] using wordTrace_append hprefix tailTrace_3697898
  have hstable : (prefixWord ++ tailWord_3697898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3697898).length < 2 ^ (prefixWord ++ tailWord_3697898).sum := by decide
  have hdescent : baseEnd_3697898 < baseStart_3697898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3697898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698005 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_3698005 : Nat := 118140960795 + 3698005 * 2 ^ 59
def prefixEnd_3698005 : Nat := 4983230072969 + 3 ^ 40 * 3698005 * 2
def baseEnd_3698005 : Nat := 1265902685153272848087127

theorem tailTrace_3698005 : CollatzResearch.WordTrace tailWord_3698005 prefixEnd_3698005 1265902685153272848087127 := by
  unfold tailWord_3698005
  simp only [CollatzResearch.WordTrace]
  refine ⟨134877322967766928817335469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89918215311844619211556979 134877322967766928817335469)
  ·
    refine ⟨50578996112912598306500801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134877322967766928817335469 50578996112912598306500801)
    ·
      refine ⟨37934247084684448729875601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50578996112912598306500801 37934247084684448729875601)
      ·
        refine ⟨28450685313513336547406701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37934247084684448729875601 28450685313513336547406701)
        ·
          refine ⟨10669006992567501205277513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28450685313513336547406701 10669006992567501205277513)
          ·
            refine ⟨8001755244425625903958135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10669006992567501205277513 8001755244425625903958135)
            ·
              refine ⟨12002632866638438855937203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8001755244425625903958135 12002632866638438855937203)
              ·
                refine ⟨18003949299957658283905805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12002632866638438855937203 18003949299957658283905805)
                ·
                  refine ⟨6751480987484121856464677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18003949299957658283905805 6751480987484121856464677)
                  ·
                    refine ⟨1265902685153272848087127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6751480987484121856464677 1265902685153272848087127)
                    ·
                      rfl

theorem cell22_3698005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_3698005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698005 prefixEnd_3698005 := by exact prefixLift 3698005
  have htrace : WordTrace (prefixWord ++ tailWord_3698005) baseStart_3698005 baseEnd_3698005 := by
    simpa [prefixWord, tailWord_3698005, baseEnd_3698005] using wordTrace_append hprefix tailTrace_3698005
  have hstable : (prefixWord ++ tailWord_3698005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698005).length < 2 ^ (prefixWord ++ tailWord_3698005).sum := by decide
  have hdescent : baseEnd_3698005 < baseStart_3698005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698030 : List Nat := [4, 1, 2, 4, 2, 1, 2, 2, 1, 3]
def baseStart_3698030 : Nat := 118140960795 + 3698030 * 2 ^ 59
def prefixEnd_3698030 : Nat := 4983230072969 + 3 ^ 40 * 3698030 * 2
def baseEnd_3698030 : Nat := 1265911243164181116212051

theorem tailTrace_3698030 : CollatzResearch.WordTrace tailWord_3698030 prefixEnd_3698030 1265911243164181116212051 := by
  unfold tailWord_3698030
  simp only [CollatzResearch.WordTrace]
  refine ⟨16859779349084544760874443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89918823195117572057997029 16859779349084544760874443)
  ·
    refine ⟨25289669023626817141311665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16859779349084544760874443 25289669023626817141311665)
    ·
      refine ⟨18967251767720112855983749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25289669023626817141311665 18967251767720112855983749)
      ·
        refine ⟨3556359706447521160496953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18967251767720112855983749 3556359706447521160496953)
        ·
          refine ⟨2667269779835640870372715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3556359706447521160496953 2667269779835640870372715)
          ·
            refine ⟨4000904669753461305559073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667269779835640870372715 4000904669753461305559073)
            ·
              refine ⟨3000678502315095979169305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4000904669753461305559073 3000678502315095979169305)
              ·
                refine ⟨2250508876736321984376979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3000678502315095979169305 2250508876736321984376979)
                ·
                  refine ⟨3375763315104482976565469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250508876736321984376979 3375763315104482976565469)
                  ·
                    refine ⟨1265911243164181116212051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3375763315104482976565469 1265911243164181116212051)
                    ·
                      rfl

theorem cell22_3698030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_3698030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698030 prefixEnd_3698030 := by exact prefixLift 3698030
  have htrace : WordTrace (prefixWord ++ tailWord_3698030) baseStart_3698030 baseEnd_3698030 := by
    simpa [prefixWord, tailWord_3698030, baseEnd_3698030] using wordTrace_append hprefix tailTrace_3698030
  have hstable : (prefixWord ++ tailWord_3698030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698030).length < 2 ^ (prefixWord ++ tailWord_3698030).sum := by decide
  have hdescent : baseEnd_3698030 < baseStart_3698030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698052 : List Nat := [2, 3, 2, 1, 1, 3, 2, 3, 2, 3]
def baseStart_3698052 : Nat := 118140960795 + 3698052 * 2 ^ 59
def prefixEnd_3698052 : Nat := 4983230072969 + 3 ^ 40 * 3698052 * 2
def baseEnd_3698052 : Nat := 1265918774213780392161983

theorem tailTrace_3698052 : CollatzResearch.WordTrace tailWord_3698052 prefixEnd_3698052 1265918774213780392161983 := by
  unfold tailWord_3698052
  simp only [CollatzResearch.WordTrace]
  refine ⟨67439518599298327922148205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89919358132397770562864273 67439518599298327922148205)
  ·
    refine ⟨25289819474736872970805577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67439518599298327922148205 25289819474736872970805577)
    ·
      refine ⟨18967364606052654728104183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25289819474736872970805577 18967364606052654728104183)
      ·
        refine ⟨28451046909078982092156275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18967364606052654728104183 28451046909078982092156275)
        ·
          refine ⟨42676570363618473138234413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28451046909078982092156275 42676570363618473138234413)
          ·
            refine ⟨16003713886356927426837905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42676570363618473138234413 16003713886356927426837905)
            ·
              refine ⟨12002785414767695570128429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16003713886356927426837905 12002785414767695570128429)
              ·
                refine ⟨4501044530537885838798161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12002785414767695570128429 4501044530537885838798161)
                ·
                  refine ⟨3375783397903414379098621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4501044530537885838798161 3375783397903414379098621)
                  ·
                    refine ⟨1265918774213780392161983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3375783397903414379098621 1265918774213780392161983)
                    ·
                      rfl

theorem cell22_3698052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_3698052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698052 prefixEnd_3698052 := by exact prefixLift 3698052
  have htrace : WordTrace (prefixWord ++ tailWord_3698052) baseStart_3698052 baseEnd_3698052 := by
    simpa [prefixWord, tailWord_3698052, baseEnd_3698052] using wordTrace_append hprefix tailTrace_3698052
  have hstable : (prefixWord ++ tailWord_3698052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698052).length < 2 ^ (prefixWord ++ tailWord_3698052).sum := by decide
  have hdescent : baseEnd_3698052 < baseStart_3698052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698080 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 5, 3]
def baseStart_3698080 : Nat := 118140960795 + 3698080 * 2 ^ 59
def prefixEnd_3698080 : Nat := 4983230072969 + 3 ^ 40 * 3698080 * 2
def baseEnd_3698080 : Nat := 1265928359185997652461897

theorem tailTrace_3698080 : CollatzResearch.WordTrace tailWord_3698080 prefixEnd_3698080 1265928359185997652461897 := by
  unfold tailWord_3698080
  simp only [CollatzResearch.WordTrace]
  refine ⟨67440029221247608313157847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89920038961663477750877129 67440029221247608313157847)
  ·
    refine ⟨101160043831871412469736771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67440029221247608313157847 101160043831871412469736771)
    ·
      refine ⟨151740065747807118704605157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101160043831871412469736771 151740065747807118704605157)
      ·
        refine ⟨28451262327713834757113467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151740065747807118704605157 28451262327713834757113467)
        ·
          refine ⟨42676893491570752135670201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28451262327713834757113467 42676893491570752135670201)
          ·
            refine ⟨32007670118678064101752651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42676893491570752135670201 32007670118678064101752651)
            ·
              refine ⟨48011505178017096152628977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32007670118678064101752651 48011505178017096152628977)
              ·
                refine ⟨36008628883512822114471733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48011505178017096152628977 36008628883512822114471733)
                ·
                  refine ⟨3375808957829327073231725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36008628883512822114471733 3375808957829327073231725)
                  ·
                    refine ⟨1265928359185997652461897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3375808957829327073231725 1265928359185997652461897)
                    ·
                      rfl

theorem cell22_3698080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5, 3].length) (baseStart_3698080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698080 prefixEnd_3698080 := by exact prefixLift 3698080
  have htrace : WordTrace (prefixWord ++ tailWord_3698080) baseStart_3698080 baseEnd_3698080 := by
    simpa [prefixWord, tailWord_3698080, baseEnd_3698080] using wordTrace_append hprefix tailTrace_3698080
  have hstable : (prefixWord ++ tailWord_3698080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698080).length < 2 ^ (prefixWord ++ tailWord_3698080).sum := by decide
  have hdescent : baseEnd_3698080 < baseStart_3698080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698097 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 3, 3]
def baseStart_3698097 : Nat := 118140960795 + 3698097 * 2 ^ 59
def prefixEnd_3698097 : Nat := 4983230072969 + 3 ^ 40 * 3698097 * 2
def baseEnd_3698097 : Nat := 1265934178633415274786845

theorem tailTrace_3698097 : CollatzResearch.WordTrace tailWord_3698097 prefixEnd_3698097 1265934178633415274786845 := by
  unfold tailWord_3698097
  simp only [CollatzResearch.WordTrace]
  refine ⟨134880678483433628529684545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89920452322289085686456363 134880678483433628529684545)
  ·
    refine ⟨101160508862575221397263409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134880678483433628529684545 101160508862575221397263409)
    ·
      refine ⟨75870381646931416047947557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101160508862575221397263409 75870381646931416047947557)
      ·
        refine ⟨14225696558799640508990167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75870381646931416047947557 14225696558799640508990167)
        ·
          refine ⟨21338544838199460763485251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14225696558799640508990167 21338544838199460763485251)
          ·
            refine ⟨32007817257299191145227877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21338544838199460763485251 32007817257299191145227877)
            ·
              refine ⟨6001465735743598339730227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32007817257299191145227877 6001465735743598339730227)
              ·
                refine ⟨9002198603615397509595341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6001465735743598339730227 9002198603615397509595341)
                ·
                  refine ⟨3375824476355774066098253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9002198603615397509595341 3375824476355774066098253)
                  ·
                    refine ⟨1265934178633415274786845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3375824476355774066098253 1265934178633415274786845)
                    ·
                      rfl

theorem cell22_3698097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_3698097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698097 prefixEnd_3698097 := by exact prefixLift 3698097
  have htrace : WordTrace (prefixWord ++ tailWord_3698097) baseStart_3698097 baseEnd_3698097 := by
    simpa [prefixWord, tailWord_3698097, baseEnd_3698097] using wordTrace_append hprefix tailTrace_3698097
  have hstable : (prefixWord ++ tailWord_3698097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698097).length < 2 ^ (prefixWord ++ tailWord_3698097).sum := by decide
  have hdescent : baseEnd_3698097 < baseStart_3698097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698170 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_3698170 : Nat := 118140960795 + 3698170 * 2 ^ 59
def prefixEnd_3698170 : Nat := 4983230072969 + 3 ^ 40 * 3698170 * 2
def baseEnd_3698170 : Nat := 1265959168025267417711621

theorem tailTrace_3698170 : CollatzResearch.WordTrace tailWord_3698170 prefixEnd_3698170 1265959168025267417711621 := by
  unfold tailWord_3698170
  simp only [CollatzResearch.WordTrace]
  refine ⟨33720835253042290499272991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89922227341446107998061309 33720835253042290499272991)
  ·
    refine ⟨50581252879563435748909487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33720835253042290499272991 50581252879563435748909487)
    ·
      refine ⟨75871879319345153623364231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50581252879563435748909487 75871879319345153623364231)
      ·
        refine ⟨113807818979017730435046347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75871879319345153623364231 113807818979017730435046347)
        ·
          refine ⟨170711728468526595652569521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113807818979017730435046347 170711728468526595652569521)
          ·
            refine ⟨128033796351394946739427141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170711728468526595652569521 128033796351394946739427141)
            ·
              refine ⟨24006336815886552513642589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128033796351394946739427141 24006336815886552513642589)
              ·
                refine ⟨9002376305957457192615971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24006336815886552513642589 9002376305957457192615971)
                ·
                  refine ⟨13503564458936185788923957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9002376305957457192615971 13503564458936185788923957)
                  ·
                    refine ⟨1265959168025267417711621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13503564458936185788923957 1265959168025267417711621)
                    ·
                      rfl

theorem cell22_3698170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_3698170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698170 prefixEnd_3698170 := by exact prefixLift 3698170
  have htrace : WordTrace (prefixWord ++ tailWord_3698170) baseStart_3698170 baseEnd_3698170 := by
    simpa [prefixWord, tailWord_3698170, baseEnd_3698170] using wordTrace_append hprefix tailTrace_3698170
  have hstable : (prefixWord ++ tailWord_3698170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698170).length < 2 ^ (prefixWord ++ tailWord_3698170).sum := by decide
  have hdescent : baseEnd_3698170 < baseStart_3698170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698187 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 1, 5]
def baseStart_3698187 : Nat := 118140960795 + 3698187 * 2 ^ 59
def prefixEnd_3698187 : Nat := 4983230072969 + 3 ^ 40 * 3698187 * 2
def baseEnd_3698187 : Nat := 1265964987472685040036569

theorem tailTrace_3698187 : CollatzResearch.WordTrace tailWord_3698187 prefixEnd_3698187 1265964987472685040036569 := by
  unfold tailWord_3698187
  simp only [CollatzResearch.WordTrace]
  refine ⟨134883961053107573900460815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89922640702071715933640543 134883961053107573900460815)
  ·
    refine ⟨202325941579661360850691223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134883961053107573900460815 202325941579661360850691223)
    ·
      refine ⟨303488912369492041276036835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202325941579661360850691223 303488912369492041276036835)
      ·
        refine ⟨455233368554238061914055253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303488912369492041276036835 455233368554238061914055253)
        ·
          refine ⟨5334766037744977288055335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 455233368554238061914055253 5334766037744977288055335)
          ·
            refine ⟨8002149056617465932083003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5334766037744977288055335 8002149056617465932083003)
            ·
              refine ⟨12003223584926198898124505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8002149056617465932083003 12003223584926198898124505)
              ·
                refine ⟨9002417688694649173593379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12003223584926198898124505 9002417688694649173593379)
                ·
                  refine ⟨13503626533041973760390069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9002417688694649173593379 13503626533041973760390069)
                  ·
                    refine ⟨1265964987472685040036569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13503626533041973760390069 1265964987472685040036569)
                    ·
                      rfl

theorem cell22_3698187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 5].length) (baseStart_3698187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698187 prefixEnd_3698187 := by exact prefixLift 3698187
  have htrace : WordTrace (prefixWord ++ tailWord_3698187) baseStart_3698187 baseEnd_3698187 := by
    simpa [prefixWord, tailWord_3698187, baseEnd_3698187] using wordTrace_append hprefix tailTrace_3698187
  have hstable : (prefixWord ++ tailWord_3698187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698187).length < 2 ^ (prefixWord ++ tailWord_3698187).sum := by decide
  have hdescent : baseEnd_3698187 < baseStart_3698187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698200 : List Nat := [2, 1, 2, 3, 4, 10]
def baseStart_3698200 : Nat := 118140960795 + 3698200 * 2 ^ 59
def prefixEnd_3698200 : Nat := 4983230072969 + 3 ^ 40 * 3698200 * 2
def baseEnd_3698200 : Nat := 15629252316522930116809

theorem tailTrace_3698200 : CollatzResearch.WordTrace tailWord_3698200 prefixEnd_3698200 15629252316522930116809 := by
  unfold tailWord_3698200
  simp only [CollatzResearch.WordTrace]
  refine ⟨67442217601030238560342027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89922956801373651413789369 67442217601030238560342027)
  ·
    refine ⟨101163326401545357840513041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67442217601030238560342027 101163326401545357840513041)
    ·
      refine ⟨75872494801159018380384781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101163326401545357840513041 75872494801159018380384781)
      ·
        refine ⟨28452185550434631892644293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75872494801159018380384781 28452185550434631892644293)
        ·
          refine ⟨5334784790706493479870805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28452185550434631892644293 5334784790706493479870805)
          ·
            refine ⟨15629252316522930116809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5334784790706493479870805 15629252316522930116809)
            ·
              rfl

theorem cell22_3698200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 10].length) (baseStart_3698200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698200 prefixEnd_3698200 := by exact prefixLift 3698200
  have htrace : WordTrace (prefixWord ++ tailWord_3698200) baseStart_3698200 baseEnd_3698200 := by
    simpa [prefixWord, tailWord_3698200, baseEnd_3698200] using wordTrace_append hprefix tailTrace_3698200
  have hstable : (prefixWord ++ tailWord_3698200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698200).length < 2 ^ (prefixWord ++ tailWord_3698200).sum := by decide
  have hdescent : baseEnd_3698200 < baseStart_3698200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698204 : List Nat := [2, 2, 3, 1, 2, 1, 4, 2, 2, 3]
def baseStart_3698204 : Nat := 118140960795 + 3698204 * 2 ^ 59
def prefixEnd_3698204 : Nat := 4983230072969 + 3 ^ 40 * 3698204 * 2
def baseEnd_3698204 : Nat := 1265970806920102662361517

theorem tailTrace_3698204 : CollatzResearch.WordTrace tailWord_3698204 prefixEnd_3698204 1265970806920102662361517 := by
  unfold tailWord_3698204
  simp only [CollatzResearch.WordTrace]
  refine ⟨67442290547022992901914833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89923054062697323869219777 67442290547022992901914833)
  ·
    refine ⟨50581717910267244676436125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67442290547022992901914833 50581717910267244676436125)
    ·
      refine ⟨18968144216350216753663547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50581717910267244676436125 18968144216350216753663547)
      ·
        refine ⟨28452216324525325130495321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18968144216350216753663547 28452216324525325130495321)
        ·
          refine ⟨21339162243393993847871491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28452216324525325130495321 21339162243393993847871491)
          ·
            refine ⟨32008743365090990771807237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21339162243393993847871491 32008743365090990771807237)
            ·
              refine ⟨6001639380954560769713857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32008743365090990771807237 6001639380954560769713857)
              ·
                refine ⟨4501229535715920577285393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6001639380954560769713857 4501229535715920577285393)
                ·
                  refine ⟨3375922151786940432964045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4501229535715920577285393 3375922151786940432964045)
                  ·
                    refine ⟨1265970806920102662361517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3375922151786940432964045 1265970806920102662361517)
                    ·
                      rfl

theorem cell22_3698204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_3698204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698204 prefixEnd_3698204 := by exact prefixLift 3698204
  have htrace : WordTrace (prefixWord ++ tailWord_3698204) baseStart_3698204 baseEnd_3698204 := by
    simpa [prefixWord, tailWord_3698204, baseEnd_3698204] using wordTrace_append hprefix tailTrace_3698204
  have hstable : (prefixWord ++ tailWord_3698204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698204).length < 2 ^ (prefixWord ++ tailWord_3698204).sum := by decide
  have hdescent : baseEnd_3698204 < baseStart_3698204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698232 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 5, 3]
def baseStart_3698232 : Nat := 118140960795 + 3698232 * 2 ^ 59
def prefixEnd_3698232 : Nat := 4983230072969 + 3 ^ 40 * 3698232 * 2
def baseEnd_3698232 : Nat := 1265980391892319922661431

theorem tailTrace_3698232 : CollatzResearch.WordTrace tailWord_3698232 prefixEnd_3698232 1265980391892319922661431 := by
  unfold tailWord_3698232
  simp only [CollatzResearch.WordTrace]
  refine ⟨67442801168972273292924475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89923734891963031057232633 67442801168972273292924475)
  ·
    refine ⟨101164201753458409939386713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67442801168972273292924475 101164201753458409939386713)
    ·
      refine ⟨75873151315093807454540035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101164201753458409939386713 75873151315093807454540035)
      ·
        refine ⟨113809726972640711181810053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75873151315093807454540035 113809726972640711181810053)
        ·
          refine ⟨21339323807370133346589385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113809726972640711181810053 21339323807370133346589385)
          ·
            refine ⟨16004492855527600009942039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21339323807370133346589385 16004492855527600009942039)
            ·
              refine ⟨24006739283291400014913059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16004492855527600009942039 24006739283291400014913059)
              ·
                refine ⟨36010108924937100022369589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24006739283291400014913059 36010108924937100022369589)
                ·
                  refine ⟨3375947711712853127097149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36010108924937100022369589 3375947711712853127097149)
                  ·
                    refine ⟨1265980391892319922661431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3375947711712853127097149 1265980391892319922661431)
                    ·
                      rfl

theorem cell22_3698232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_3698232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698232 prefixEnd_3698232 := by exact prefixLift 3698232
  have htrace : WordTrace (prefixWord ++ tailWord_3698232) baseStart_3698232 baseEnd_3698232 := by
    simpa [prefixWord, tailWord_3698232, baseEnd_3698232] using wordTrace_append hprefix tailTrace_3698232
  have hstable : (prefixWord ++ tailWord_3698232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698232).length < 2 ^ (prefixWord ++ tailWord_3698232).sum := by decide
  have hdescent : baseEnd_3698232 < baseStart_3698232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698236 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 2, 4]
def baseStart_3698236 : Nat := 118140960795 + 3698236 * 2 ^ 59
def prefixEnd_3698236 : Nat := 4983230072969 + 3 ^ 40 * 3698236 * 2
def baseEnd_3698236 : Nat := 1265981761174065245561419

theorem tailTrace_3698236 : CollatzResearch.WordTrace tailWord_3698236 prefixEnd_3698236 1265981761174065245561419 := by
  unfold tailWord_3698236
  simp only [CollatzResearch.WordTrace]
  refine ⟨67442874114965027634497281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89923832153286703512663041 67442874114965027634497281)
  ·
    refine ⟨50582155586223770725872961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67442874114965027634497281 50582155586223770725872961)
    ·
      refine ⟨37936616689667828044404721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50582155586223770725872961 37936616689667828044404721)
      ·
        refine ⟨28452462517250871033303541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37936616689667828044404721 28452462517250871033303541)
        ·
          refine ⟨2667418360992269159372207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28452462517250871033303541 2667418360992269159372207)
          ·
            refine ⟨4001127541488403739058311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667418360992269159372207 4001127541488403739058311)
            ·
              refine ⟨6001691312232605608587467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4001127541488403739058311 6001691312232605608587467)
              ·
                refine ⟨9002536968348908412881201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6001691312232605608587467 9002536968348908412881201)
                ·
                  refine ⟨6751902726261681309660901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9002536968348908412881201 6751902726261681309660901)
                  ·
                    refine ⟨1265981761174065245561419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6751902726261681309660901 1265981761174065245561419)
                    ·
                      rfl

theorem cell22_3698236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_3698236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698236 prefixEnd_3698236 := by exact prefixLift 3698236
  have htrace : WordTrace (prefixWord ++ tailWord_3698236) baseStart_3698236 baseEnd_3698236 := by
    simpa [prefixWord, tailWord_3698236, baseEnd_3698236] using wordTrace_append hprefix tailTrace_3698236
  have hstable : (prefixWord ++ tailWord_3698236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698236).length < 2 ^ (prefixWord ++ tailWord_3698236).sum := by decide
  have hdescent : baseEnd_3698236 < baseStart_3698236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698245 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 7]
def baseStart_3698245 : Nat := 118140960795 + 3698245 * 2 ^ 59
def prefixEnd_3698245 : Nat := 4983230072969 + 3 ^ 40 * 3698245 * 2
def baseEnd_3698245 : Nat := 421994947352664074028797

theorem tailTrace_3698245 : CollatzResearch.WordTrace tailWord_3698245 prefixEnd_3698245 421994947352664074028797 := by
  unfold tailWord_3698245
  simp only [CollatzResearch.WordTrace]
  refine ⟨134886076486897449806072189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89924050991264966537381459 134886076486897449806072189)
  ·
    refine ⟨50582278682586543677277071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134886076486897449806072189 50582278682586543677277071)
    ·
      refine ⟨75873418023879815515915607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50582278682586543677277071 75873418023879815515915607)
      ·
        refine ⟨113810127035819723273873411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75873418023879815515915607 113810127035819723273873411)
        ·
          refine ⟨170715190553729584910810117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113810127035819723273873411 170715190553729584910810117)
          ·
            refine ⟨32009098228824297170776897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170715190553729584910810117 32009098228824297170776897)
            ·
              refine ⟨24006823671618222878082673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32009098228824297170776897 24006823671618222878082673)
              ·
                refine ⟨18005117753713667158562005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24006823671618222878082673 18005117753713667158562005)
                ·
                  refine ⟨421994947352664074028797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18005117753713667158562005 421994947352664074028797)
                  ·
                    rfl

theorem cell22_3698245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_3698245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698245 prefixEnd_3698245 := by exact prefixLift 3698245
  have htrace : WordTrace (prefixWord ++ tailWord_3698245) baseStart_3698245 baseEnd_3698245 := by
    simpa [prefixWord, tailWord_3698245, baseEnd_3698245] using wordTrace_append hprefix tailTrace_3698245
  have hstable : (prefixWord ++ tailWord_3698245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698245).length < 2 ^ (prefixWord ++ tailWord_3698245).sum := by decide
  have hdescent : baseEnd_3698245 < baseStart_3698245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698277 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_3698277 : Nat := 118140960795 + 3698277 * 2 ^ 59
def prefixEnd_3698277 : Nat := 4983230072969 + 3 ^ 40 * 3698277 * 2
def baseEnd_3698277 : Nat := 1265995796311954805286293

theorem tailTrace_3698277 : CollatzResearch.WordTrace tailWord_3698277 prefixEnd_3698277 1265995796311954805286293 := by
  unfold tailWord_3698277
  simp only [CollatzResearch.WordTrace]
  refine ⟨134887243622781519271237085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89924829081854346180824723 134887243622781519271237085)
  ·
    refine ⟨50582716358543069726713907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134887243622781519271237085 50582716358543069726713907)
    ·
      refine ⟨75874074537814604590070861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50582716358543069726713907 75874074537814604590070861)
      ·
        refine ⟨28452777951680476721276573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75874074537814604590070861 28452777951680476721276573)
        ·
          refine ⟨10669791731880178770478715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28452777951680476721276573 10669791731880178770478715)
          ·
            refine ⟨16004687597820268155718073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10669791731880178770478715 16004687597820268155718073)
            ·
              refine ⟨12003515698365201116788555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16004687597820268155718073 12003515698365201116788555)
              ·
                refine ⟨18005273547547801675182833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12003515698365201116788555 18005273547547801675182833)
                ·
                  refine ⟨13503955160660851256387125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18005273547547801675182833 13503955160660851256387125)
                  ·
                    refine ⟨1265995796311954805286293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13503955160660851256387125 1265995796311954805286293)
                    ·
                      rfl

theorem cell22_3698277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_3698277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698277 prefixEnd_3698277 := by exact prefixLift 3698277
  have htrace : WordTrace (prefixWord ++ tailWord_3698277) baseStart_3698277 baseEnd_3698277 := by
    simpa [prefixWord, tailWord_3698277, baseEnd_3698277] using wordTrace_append hprefix tailTrace_3698277
  have hstable : (prefixWord ++ tailWord_3698277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698277).length < 2 ^ (prefixWord ++ tailWord_3698277).sum := by decide
  have hdescent : baseEnd_3698277 < baseStart_3698277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698339 : List Nat := [1, 1, 1, 4, 1, 1, 5, 3, 2, 3]
def baseStart_3698339 : Nat := 118140960795 + 3698339 * 2 ^ 59
def prefixEnd_3698339 : Nat := 4983230072969 + 3 ^ 40 * 3698339 * 2
def baseEnd_3698339 : Nat := 1266017020179007310236103

theorem tailTrace_3698339 : CollatzResearch.WordTrace tailWord_3698339 prefixEnd_3698339 1266017020179007310236103 := by
  unfold tailWord_3698339
  simp only [CollatzResearch.WordTrace]
  refine ⟨134889504948556903859994071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89926336632371269239996047 134889504948556903859994071)
  ·
    refine ⟨202334257422835355789991107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134889504948556903859994071 202334257422835355789991107)
    ·
      refine ⟨303501386134253033684986661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202334257422835355789991107 303501386134253033684986661)
      ·
        refine ⟨56906509900172443815934999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 303501386134253033684986661 56906509900172443815934999)
        ·
          refine ⟨85359764850258665723902499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56906509900172443815934999 85359764850258665723902499)
          ·
            refine ⟨128039647275387998585853749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85359764850258665723902499 128039647275387998585853749)
            ·
              refine ⟨12003716932067624867423789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128039647275387998585853749 12003716932067624867423789)
              ·
                refine ⟨4501393849525359325283921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12003716932067624867423789 4501393849525359325283921)
                ·
                  refine ⟨3376045387144019493962941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4501393849525359325283921 3376045387144019493962941)
                  ·
                    refine ⟨1266017020179007310236103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3376045387144019493962941 1266017020179007310236103)
                    ·
                      rfl

theorem cell22_3698339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 3].length) (baseStart_3698339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698339 prefixEnd_3698339 := by exact prefixLift 3698339
  have htrace : WordTrace (prefixWord ++ tailWord_3698339) baseStart_3698339 baseEnd_3698339 := by
    simpa [prefixWord, tailWord_3698339, baseEnd_3698339] using wordTrace_append hprefix tailTrace_3698339
  have hstable : (prefixWord ++ tailWord_3698339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698339).length < 2 ^ (prefixWord ++ tailWord_3698339).sum := by decide
  have hdescent : baseEnd_3698339 < baseStart_3698339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698382 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_3698382 : Nat := 118140960795 + 3698382 * 2 ^ 59
def prefixEnd_3698382 : Nat := 4983230072969 + 3 ^ 40 * 3698382 * 2
def baseEnd_3698382 : Nat := 1266031739957769531410971

theorem tailTrace_3698382 : CollatzResearch.WordTrace tailWord_3698382 prefixEnd_3698382 1266031739957769531410971 := by
  unfold tailWord_3698382
  simp only [CollatzResearch.WordTrace]
  refine ⟨16861384160925140275476175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89927382191600748135872933 16861384160925140275476175)
  ·
    refine ⟨25292076241387710413214263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16861384160925140275476175 25292076241387710413214263)
    ·
      refine ⟨37938114362081565619821395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25292076241387710413214263 37938114362081565619821395)
      ·
        refine ⟨56907171543122348429732093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37938114362081565619821395 56907171543122348429732093)
        ·
          refine ⟨21340189328670880661149535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56907171543122348429732093 21340189328670880661149535)
          ·
            refine ⟨32010283993006320991724303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21340189328670880661149535 32010283993006320991724303)
            ·
              refine ⟨48015425989509481487586455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32010283993006320991724303 48015425989509481487586455)
              ·
                refine ⟨72023138984264222231379683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48015425989509481487586455 72023138984264222231379683)
                ·
                  refine ⟨108034708476396333347069525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72023138984264222231379683 108034708476396333347069525)
                  ·
                    refine ⟨1266031739957769531410971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108034708476396333347069525 1266031739957769531410971)
                    ·
                      rfl

theorem cell22_3698382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_3698382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698382 prefixEnd_3698382 := by exact prefixLift 3698382
  have htrace : WordTrace (prefixWord ++ tailWord_3698382) baseStart_3698382 baseEnd_3698382 := by
    simpa [prefixWord, tailWord_3698382, baseEnd_3698382] using wordTrace_append hprefix tailTrace_3698382
  have hstable : (prefixWord ++ tailWord_3698382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698382).length < 2 ^ (prefixWord ++ tailWord_3698382).sum := by decide
  have hdescent : baseEnd_3698382 < baseStart_3698382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698401 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 3, 3]
def baseStart_3698401 : Nat := 118140960795 + 3698401 * 2 ^ 59
def prefixEnd_3698401 : Nat := 4983230072969 + 3 ^ 40 * 3698401 * 2
def baseEnd_3698401 : Nat := 1266038244046059815185913

theorem tailTrace_3698401 : CollatzResearch.WordTrace tailWord_3698401 prefixEnd_3698401 1266038244046059815185913 := by
  unfold tailWord_3698401
  simp only [CollatzResearch.WordTrace]
  refine ⟨134891766274332288448751057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89927844182888192299167371 134891766274332288448751057)
  ·
    refine ⟨101168824705749216336563293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134891766274332288448751057 101168824705749216336563293)
    ·
      refine ⟨37938309264655956126211235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101168824705749216336563293 37938309264655956126211235)
      ·
        refine ⟨56907463896983934189316853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37938309264655956126211235 56907463896983934189316853)
        ·
          refine ⟨5335074740342243830248455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56907463896983934189316853 5335074740342243830248455)
          ·
            refine ⟨8002612110513365745372683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5335074740342243830248455 8002612110513365745372683)
            ·
              refine ⟨12003918165770048618059025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8002612110513365745372683 12003918165770048618059025)
              ·
                refine ⟨9002938624327536463544269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12003918165770048618059025 9002938624327536463544269)
                ·
                  refine ⟨3376101984122826173829101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9002938624327536463544269 3376101984122826173829101)
                  ·
                    refine ⟨1266038244046059815185913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3376101984122826173829101 1266038244046059815185913)
                    ·
                      rfl

theorem cell22_3698401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_3698401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698401 prefixEnd_3698401 := by exact prefixLift 3698401
  have htrace : WordTrace (prefixWord ++ tailWord_3698401) baseStart_3698401 baseEnd_3698401 := by
    simpa [prefixWord, tailWord_3698401, baseEnd_3698401] using wordTrace_append hprefix tailTrace_3698401
  have hstable : (prefixWord ++ tailWord_3698401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698401).length < 2 ^ (prefixWord ++ tailWord_3698401).sum := by decide
  have hdescent : baseEnd_3698401 < baseStart_3698401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698418 : List Nat := [3, 2, 1, 3, 1, 1, 4, 3, 1, 3]
def baseStart_3698418 : Nat := 118140960795 + 3698418 * 2 ^ 59
def prefixEnd_3698418 : Nat := 4983230072969 + 3 ^ 40 * 3698418 * 2
def baseEnd_3698418 : Nat := 1266044063493477437510861

theorem tailTrace_3698418 : CollatzResearch.WordTrace tailWord_3698418 prefixEnd_3698418 1266044063493477437510861 := by
  unfold tailWord_3698418
  simp only [CollatzResearch.WordTrace]
  refine ⟨33723096578817675088029977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89928257543513800234746605 33723096578817675088029977)
  ·
    refine ⟨25292322434113256316022483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33723096578817675088029977 25292322434113256316022483)
    ·
      refine ⟨37938483651169884474033725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25292322434113256316022483 37938483651169884474033725)
      ·
        refine ⟨14226931369188706677762647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37938483651169884474033725 14226931369188706677762647)
        ·
          refine ⟨21340397053783060016643971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14226931369188706677762647 21340397053783060016643971)
          ·
            refine ⟨32010595580674590024965957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21340397053783060016643971 32010595580674590024965957)
            ·
              refine ⟨6001986671376485629681117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32010595580674590024965957 6001986671376485629681117)
              ·
                refine ⟨2250745001766182111130419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6001986671376485629681117 2250745001766182111130419)
                ·
                  refine ⟨3376117502649273166695629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250745001766182111130419 3376117502649273166695629)
                  ·
                    refine ⟨1266044063493477437510861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3376117502649273166695629 1266044063493477437510861)
                    ·
                      rfl

theorem cell22_3698418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_3698418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698418 prefixEnd_3698418 := by exact prefixLift 3698418
  have htrace : WordTrace (prefixWord ++ tailWord_3698418) baseStart_3698418 baseEnd_3698418 := by
    simpa [prefixWord, tailWord_3698418, baseEnd_3698418] using wordTrace_append hprefix tailTrace_3698418
  have hstable : (prefixWord ++ tailWord_3698418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698418).length < 2 ^ (prefixWord ++ tailWord_3698418).sum := by decide
  have hdescent : baseEnd_3698418 < baseStart_3698418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698427 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 5, 4]
def baseStart_3698427 : Nat := 118140960795 + 3698427 * 2 ^ 59
def prefixEnd_3698427 : Nat := 4983230072969 + 3 ^ 40 * 3698427 * 2
def baseEnd_3698427 : Nat := 1266047144377404414035833

theorem tailTrace_3698427 : CollatzResearch.WordTrace tailWord_3698427 prefixEnd_3698427 1266047144377404414035833 := by
  unfold tailWord_3698427
  simp only [CollatzResearch.WordTrace]
  refine ⟨134892714572238094889197535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89928476381492063259465023 134892714572238094889197535)
  ·
    refine ⟨202339071858357142333796303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134892714572238094889197535 202339071858357142333796303)
    ·
      refine ⟨303508607787535713500694455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202339071858357142333796303 303508607787535713500694455)
      ·
        refine ⟨455262911681303570251041683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303508607787535713500694455 455262911681303570251041683)
        ·
          refine ⟨682894367521955355376562525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455262911681303570251041683 682894367521955355376562525)
          ·
            refine ⟨256085387820733258266210947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 682894367521955355376562525 256085387820733258266210947)
            ·
              refine ⟨384128081731099887399316421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256085387820733258266210947 384128081731099887399316421)
              ·
                refine ⟨72024015324581228887371829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384128081731099887399316421 72024015324581228887371829)
                ·
                  refine ⟨6752251436679490208191109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72024015324581228887371829 6752251436679490208191109)
                  ·
                    refine ⟨1266047144377404414035833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6752251436679490208191109 1266047144377404414035833)
                    ·
                      rfl

theorem cell22_3698427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 4].length) (baseStart_3698427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698427 prefixEnd_3698427 := by exact prefixLift 3698427
  have htrace : WordTrace (prefixWord ++ tailWord_3698427) baseStart_3698427 baseEnd_3698427 := by
    simpa [prefixWord, tailWord_3698427, baseEnd_3698427] using wordTrace_append hprefix tailTrace_3698427
  have hstable : (prefixWord ++ tailWord_3698427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698427).length < 2 ^ (prefixWord ++ tailWord_3698427).sum := by decide
  have hdescent : baseEnd_3698427 < baseStart_3698427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698476 : List Nat := [2, 2, 1, 1, 1, 5, 3, 3, 4]
def baseStart_3698476 : Nat := 118140960795 + 3698476 * 2 ^ 59
def prefixEnd_3698476 : Nat := 4983230072969 + 3 ^ 40 * 3698476 * 2
def baseEnd_3698476 : Nat := 422021306026261539853561

theorem tailTrace_3698476 : CollatzResearch.WordTrace tailWord_3698476 prefixEnd_3698476 422021306026261539853561 := by
  unfold tailWord_3698476
  simp only [CollatzResearch.WordTrace]
  refine ⟨67447250874530288128865641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89929667832707050838487521 67447250874530288128865641)
  ·
    refine ⟨50585438155897716096649231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67447250874530288128865641 50585438155897716096649231)
    ·
      refine ⟨75878157233846574144973847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50585438155897716096649231 75878157233846574144973847)
      ·
        refine ⟨113817235850769861217460771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75878157233846574144973847 113817235850769861217460771)
        ·
          refine ⟨170725853776154791826191157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113817235850769861217460771 170725853776154791826191157)
          ·
            refine ⟨16005548791514511733705421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170725853776154791826191157 16005548791514511733705421)
            ·
              refine ⟨6002080796817941900139533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16005548791514511733705421 6002080796817941900139533)
              ·
                refine ⟨2250780298806728212552325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6002080796817941900139533 2250780298806728212552325)
                ·
                  refine ⟨422021306026261539853561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2250780298806728212552325 422021306026261539853561)
                  ·
                    rfl

theorem cell22_3698476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_3698476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698476 prefixEnd_3698476 := by exact prefixLift 3698476
  have htrace : WordTrace (prefixWord ++ tailWord_3698476) baseStart_3698476 baseEnd_3698476 := by
    simpa [prefixWord, tailWord_3698476, baseEnd_3698476] using wordTrace_append hprefix tailTrace_3698476
  have hstable : (prefixWord ++ tailWord_3698476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698476).length < 2 ^ (prefixWord ++ tailWord_3698476).sum := by decide
  have hdescent : baseEnd_3698476 < baseStart_3698476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698504 : List Nat := [2, 1, 3, 1, 1, 5, 2, 7]
def baseStart_3698504 : Nat := 118140960795 + 3698504 * 2 ^ 59
def prefixEnd_3698504 : Nat := 4983230072969 + 3 ^ 40 * 3698504 * 2
def baseEnd_3698504 : Nat := 140674833672333542206733

theorem tailTrace_3698504 : CollatzResearch.WordTrace tailWord_3698504 prefixEnd_3698504 140674833672333542206733 := by
  unfold tailWord_3698504
  simp only [CollatzResearch.WordTrace]
  refine ⟨67447761496479568519875283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89930348661972758026500377 67447761496479568519875283)
  ·
    refine ⟨101171642244719352779812925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67447761496479568519875283 101171642244719352779812925)
    ·
      refine ⟨37939365841769757292429847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101171642244719352779812925 37939365841769757292429847)
      ·
        refine ⟨56909048762654635938644771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37939365841769757292429847 56909048762654635938644771)
        ·
          refine ⟨85363573143981953907967157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56909048762654635938644771 85363573143981953907967157)
          ·
            refine ⟨8002834982248308178871921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85363573143981953907967157 8002834982248308178871921)
            ·
              refine ⟨6002126236686231134153941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8002834982248308178871921 6002126236686231134153941)
              ·
                refine ⟨140674833672333542206733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6002126236686231134153941 140674833672333542206733)
                ·
                  rfl

theorem cell22_3698504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 7].length) (baseStart_3698504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698504 prefixEnd_3698504 := by exact prefixLift 3698504
  have htrace : WordTrace (prefixWord ++ tailWord_3698504) baseStart_3698504 baseEnd_3698504 := by
    simpa [prefixWord, tailWord_3698504, baseEnd_3698504] using wordTrace_append hprefix tailTrace_3698504
  have hstable : (prefixWord ++ tailWord_3698504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698504).length < 2 ^ (prefixWord ++ tailWord_3698504).sum := by decide
  have hdescent : baseEnd_3698504 < baseStart_3698504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698508 : List Nat := [2, 2, 1, 3, 4, 1, 1, 3, 2, 3]
def baseStart_3698508 : Nat := 118140960795 + 3698508 * 2 ^ 59
def prefixEnd_3698508 : Nat := 4983230072969 + 3 ^ 40 * 3698508 * 2
def baseEnd_3698508 : Nat := 1266074872332747202760585

theorem tailTrace_3698508 : CollatzResearch.WordTrace tailWord_3698508 prefixEnd_3698508 1266074872332747202760585 := by
  unfold tailWord_3698508
  simp only [CollatzResearch.WordTrace]
  refine ⟨67447834442472322861448089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89930445923296430481930785 67447834442472322861448089)
  ·
    refine ⟨50585875831854242146086067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67447834442472322861448089 50585875831854242146086067)
    ·
      refine ⟨75878813747781363219129101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50585875831854242146086067 75878813747781363219129101)
      ·
        refine ⟨28454555155418011207173413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75878813747781363219129101 28454555155418011207173413)
        ·
          refine ⟨5335229091640877101345015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28454555155418011207173413 5335229091640877101345015)
          ·
            refine ⟨8002843637461315652017523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5335229091640877101345015 8002843637461315652017523)
            ·
              refine ⟨12004265456191973478026285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8002843637461315652017523 12004265456191973478026285)
              ·
                refine ⟨4501599546071990054259857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12004265456191973478026285 4501599546071990054259857)
                ·
                  refine ⟨3376199659553992540694893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4501599546071990054259857 3376199659553992540694893)
                  ·
                    refine ⟨1266074872332747202760585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3376199659553992540694893 1266074872332747202760585)
                    ·
                      rfl

theorem cell22_3698508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_3698508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698508 prefixEnd_3698508 := by exact prefixLift 3698508
  have htrace : WordTrace (prefixWord ++ tailWord_3698508) baseStart_3698508 baseEnd_3698508 := by
    simpa [prefixWord, tailWord_3698508, baseEnd_3698508] using wordTrace_append hprefix tailTrace_3698508
  have hstable : (prefixWord ++ tailWord_3698508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698508).length < 2 ^ (prefixWord ++ tailWord_3698508).sum := by decide
  have hdescent : baseEnd_3698508 < baseStart_3698508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698553 : List Nat := [1, 2, 1, 3, 2, 2, 3, 4, 1, 3]
def baseStart_3698553 : Nat := 118140960795 + 3698553 * 2 ^ 59
def prefixEnd_3698553 : Nat := 4983230072969 + 3 ^ 40 * 3698553 * 2
def baseEnd_3698553 : Nat := 1266090276752382085385447

theorem tailTrace_3698553 : CollatzResearch.WordTrace tailWord_3698553 prefixEnd_3698553 1266090276752382085385447 := by
  unfold tailWord_3698553
  simp only [CollatzResearch.WordTrace]
  refine ⟨134897310169781618408284313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89931540113187745605522875 134897310169781618408284313)
  ·
    refine ⟨101172982627336213806213235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134897310169781618408284313 101172982627336213806213235)
    ·
      refine ⟨151759473941004320709319853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101172982627336213806213235 151759473941004320709319853)
      ·
        refine ⟨56909802727876620265994945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151759473941004320709319853 56909802727876620265994945)
        ·
          refine ⟨42682352045907465199496209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56909802727876620265994945 42682352045907465199496209)
          ·
            refine ⟨32011764034430598899622157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42682352045907465199496209 32011764034430598899622157)
            ·
              refine ⟨12004411512911474587358309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32011764034430598899622157 12004411512911474587358309)
              ·
                refine ⟨2250827158670901485129683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12004411512911474587358309 2250827158670901485129683)
                ·
                  refine ⟨3376240738006352227694525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250827158670901485129683 3376240738006352227694525)
                  ·
                    refine ⟨1266090276752382085385447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3376240738006352227694525 1266090276752382085385447)
                    ·
                      rfl

theorem cell22_3698553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 1, 3].length) (baseStart_3698553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698553 prefixEnd_3698553 := by exact prefixLift 3698553
  have htrace : WordTrace (prefixWord ++ tailWord_3698553) baseStart_3698553 baseEnd_3698553 := by
    simpa [prefixWord, tailWord_3698553, baseEnd_3698553] using wordTrace_append hprefix tailTrace_3698553
  have hstable : (prefixWord ++ tailWord_3698553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698553).length < 2 ^ (prefixWord ++ tailWord_3698553).sum := by decide
  have hdescent : baseEnd_3698553 < baseStart_3698553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698564 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_3698564 : Nat := 118140960795 + 3698564 * 2 ^ 59
def prefixEnd_3698564 : Nat := 4983230072969 + 3 ^ 40 * 3698564 * 2
def baseEnd_3698564 : Nat := 1266094042277181723360413

theorem tailTrace_3698564 : CollatzResearch.WordTrace tailWord_3698564 prefixEnd_3698564 1266094042277181723360413 := by
  unfold tailWord_3698564
  simp only [CollatzResearch.WordTrace]
  refine ⟨67448855686370883643467373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89931807581827844857956497 67448855686370883643467373)
  ·
    refine ⟨25293320882389081366300265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67448855686370883643467373 25293320882389081366300265)
    ·
      refine ⟨18969990661791811024725199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25293320882389081366300265 18969990661791811024725199)
      ·
        refine ⟨28454985992687716537087799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18969990661791811024725199 28454985992687716537087799)
        ·
          refine ⟨42682478989031574805631699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28454985992687716537087799 42682478989031574805631699)
          ·
            refine ⟨64023718483547362208447549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42682478989031574805631699 64023718483547362208447549)
            ·
              refine ⟨24008894431330260828167831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64023718483547362208447549 24008894431330260828167831)
              ·
                refine ⟨36013341646995391242251747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24008894431330260828167831 36013341646995391242251747)
                ·
                  refine ⟨54020012470493086863377621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36013341646995391242251747 54020012470493086863377621)
                  ·
                    refine ⟨1266094042277181723360413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54020012470493086863377621 1266094042277181723360413)
                    ·
                      rfl

theorem cell22_3698564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_3698564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698564 prefixEnd_3698564 := by exact prefixLift 3698564
  have htrace : WordTrace (prefixWord ++ tailWord_3698564) baseStart_3698564 baseEnd_3698564 := by
    simpa [prefixWord, tailWord_3698564, baseEnd_3698564] using wordTrace_append hprefix tailTrace_3698564
  have hstable : (prefixWord ++ tailWord_3698564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698564).length < 2 ^ (prefixWord ++ tailWord_3698564).sum := by decide
  have hdescent : baseEnd_3698564 < baseStart_3698564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698611 : List Nat := [1, 1, 1, 2, 3, 1, 3, 6, 4]
def baseStart_3698611 : Nat := 118140960795 + 3698611 * 2 ^ 59
def prefixEnd_3698611 : Nat := 4983230072969 + 3 ^ 40 * 3698611 * 2
def baseEnd_3698611 : Nat := 422036710445896422478423

theorem tailTrace_3698611 : CollatzResearch.WordTrace tailWord_3698611 prefixEnd_3698611 422036710445896422478423 := by
  unfold tailWord_3698611
  simp only [CollatzResearch.WordTrace]
  refine ⟨134899425603571494313895687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89932950402380996209263791 134899425603571494313895687)
  ·
    refine ⟨202349138405357241470843531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134899425603571494313895687 202349138405357241470843531)
    ·
      refine ⟨303523707608035862206265297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202349138405357241470843531 303523707608035862206265297)
      ·
        refine ⟨227642780706026896654698973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303523707608035862206265297 227642780706026896654698973)
        ·
          refine ⟨85366042764760086245512115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227642780706026896654698973 85366042764760086245512115)
          ·
            refine ⟨128049064147140129368268173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85366042764760086245512115 128049064147140129368268173)
            ·
              refine ⟨48018399055177548513100565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128049064147140129368268173 48018399055177548513100565)
              ·
                refine ⟨2250862455711447586551589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48018399055177548513100565 2250862455711447586551589)
                ·
                  refine ⟨422036710445896422478423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2250862455711447586551589 422036710445896422478423)
                  ·
                    rfl

theorem cell22_3698611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 4].length) (baseStart_3698611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698611 prefixEnd_3698611 := by exact prefixLift 3698611
  have htrace : WordTrace (prefixWord ++ tailWord_3698611) baseStart_3698611 baseEnd_3698611 := by
    simpa [prefixWord, tailWord_3698611, baseEnd_3698611] using wordTrace_append hprefix tailTrace_3698611
  have hstable : (prefixWord ++ tailWord_3698611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698611).length < 2 ^ (prefixWord ++ tailWord_3698611).sum := by decide
  have hdescent : baseEnd_3698611 < baseStart_3698611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698624 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 3, 6]
def baseStart_3698624 : Nat := 118140960795 + 3698624 * 2 ^ 59
def prefixEnd_3698624 : Nat := 4983230072969 + 3 ^ 40 * 3698624 * 2
def baseEnd_3698624 : Nat := 1266114581503361566860229

theorem tailTrace_3698624 : CollatzResearch.WordTrace tailWord_3698624 prefixEnd_3698624 1266114581503361566860229 := by
  unfold tailWord_3698624
  simp only [CollatzResearch.WordTrace]
  refine ⟨67449949876262198767059463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89933266501682931689412617 67449949876262198767059463)
  ·
    refine ⟨101174924814393298150589195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67449949876262198767059463 101174924814393298150589195)
    ·
      refine ⟨151762387221589947225883793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101174924814393298150589195 151762387221589947225883793)
      ·
        refine ⟨113821790416192460419412845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151762387221589947225883793 113821790416192460419412845)
        ·
          refine ⟨42683171406072172657279817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113821790416192460419412845 42683171406072172657279817)
          ·
            refine ⟨32012378554554129492959863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42683171406072172657279817 32012378554554129492959863)
            ·
              refine ⟨48018567831831194239439795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32012378554554129492959863 48018567831831194239439795)
              ·
                refine ⟨72027851747746791359159693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48018567831831194239439795 72027851747746791359159693)
                ·
                  refine ⟨27010444405405046759684885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72027851747746791359159693 27010444405405046759684885)
                  ·
                    refine ⟨1266114581503361566860229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27010444405405046759684885 1266114581503361566860229)
                    ·
                      rfl

theorem cell22_3698624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_3698624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698624 prefixEnd_3698624 := by exact prefixLift 3698624
  have htrace : WordTrace (prefixWord ++ tailWord_3698624) baseStart_3698624 baseEnd_3698624 := by
    simpa [prefixWord, tailWord_3698624, baseEnd_3698624] using wordTrace_append hprefix tailTrace_3698624
  have hstable : (prefixWord ++ tailWord_3698624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698624).length < 2 ^ (prefixWord ++ tailWord_3698624).sum := by decide
  have hdescent : baseEnd_3698624 < baseStart_3698624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698639 : List Nat := [1, 1, 2, 1, 1, 5, 3, 8]
def baseStart_3698639 : Nat := 118140960795 + 3698639 * 2 ^ 59
def prefixEnd_3698639 : Nat := 4983230072969 + 3 ^ 40 * 3698639 * 2
def baseEnd_3698639 : Nat := 140679968478878503081687

theorem tailTrace_3698639 : CollatzResearch.WordTrace tailWord_3698639 prefixEnd_3698639 140679968478878503081687 := by
  unfold tailWord_3698639
  simp only [CollatzResearch.WordTrace]
  refine ⟨134900446847470055095914971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89933631231646703397276647 134900446847470055095914971)
  ·
    refine ⟨202350670271205082643872457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134900446847470055095914971 202350670271205082643872457)
    ·
      refine ⟨151763002703403811982904343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202350670271205082643872457 151763002703403811982904343)
      ·
        refine ⟨227644504055105717974356515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151763002703403811982904343 227644504055105717974356515)
        ·
          refine ⟨341466756082658576961534773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227644504055105717974356515 341466756082658576961534773)
          ·
            refine ⟨32012508382749241590143885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 341466756082658576961534773 32012508382749241590143885)
            ·
              refine ⟨12004690643530965596303957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32012508382749241590143885 12004690643530965596303957)
              ·
                refine ⟨140679968478878503081687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12004690643530965596303957 140679968478878503081687)
                ·
                  rfl

theorem cell22_3698639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 8].length) (baseStart_3698639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698639 prefixEnd_3698639 := by exact prefixLift 3698639
  have htrace : WordTrace (prefixWord ++ tailWord_3698639) baseStart_3698639 baseEnd_3698639 := by
    simpa [prefixWord, tailWord_3698639, baseEnd_3698639] using wordTrace_append hprefix tailTrace_3698639
  have hstable : (prefixWord ++ tailWord_3698639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698639).length < 2 ^ (prefixWord ++ tailWord_3698639).sum := by decide
  have hdescent : baseEnd_3698639 < baseStart_3698639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698645 : List Nat := [1, 3, 2, 3, 2, 3, 1, 3, 4]
def baseStart_3698645 : Nat := 118140960795 + 3698645 * 2 ^ 59
def prefixEnd_3698645 : Nat := 4983230072969 + 3 ^ 40 * 3698645 * 2
def baseEnd_3698645 : Nat := 422040590077508170695055

theorem tailTrace_3698645 : CollatzResearch.WordTrace tailWord_3698645 prefixEnd_3698645 422040590077508170695055 := by
  unfold tailWord_3698645
  simp only [CollatzResearch.WordTrace]
  refine ⟨134900665685448318120633389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89933777123632212080422259 134900665685448318120633389)
  ·
    refine ⟨50587749632043119295237521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134900665685448318120633389 50587749632043119295237521)
    ·
      refine ⟨37940812224032339471428141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50587749632043119295237521 37940812224032339471428141)
      ·
        refine ⟨14227804584012127301785553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37940812224032339471428141 14227804584012127301785553)
        ·
          refine ⟨10670853438009095476339165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14227804584012127301785553 10670853438009095476339165)
          ·
            refine ⟨4001570039253410803627187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10670853438009095476339165 4001570039253410803627187)
            ·
              refine ⟨6002355058880116205440781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4001570039253410803627187 6002355058880116205440781)
              ·
                refine ⟨2250883147080043577040293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6002355058880116205440781 2250883147080043577040293)
                ·
                  refine ⟨422040590077508170695055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2250883147080043577040293 422040590077508170695055)
                  ·
                    rfl

theorem cell22_3698645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_3698645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698645 prefixEnd_3698645 := by exact prefixLift 3698645
  have htrace : WordTrace (prefixWord ++ tailWord_3698645) baseStart_3698645 baseEnd_3698645 := by
    simpa [prefixWord, tailWord_3698645, baseEnd_3698645] using wordTrace_append hprefix tailTrace_3698645
  have hstable : (prefixWord ++ tailWord_3698645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698645).length < 2 ^ (prefixWord ++ tailWord_3698645).sum := by decide
  have hdescent : baseEnd_3698645 < baseStart_3698645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698694 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3698694 : Nat := 118140960795 + 3698694 * 2 ^ 59
def prefixEnd_3698694 : Nat := 4983230072969 + 3 ^ 40 * 3698694 * 2
def baseEnd_3698694 : Nat := 1266138543933904717610015

theorem tailTrace_3698694 : CollatzResearch.WordTrace tailWord_3698694 prefixEnd_3698694 1266138543933904717610015 := by
  unfold tailWord_3698694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4215701651945962484036473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89934968574847199659444757 4215701651945962484036473)
  ·
    refine ⟨3161776238959471863027355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4215701651945962484036473 3161776238959471863027355)
    ·
      refine ⟨4742664358439207794541033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3161776238959471863027355 4742664358439207794541033)
      ·
        refine ⟨3556998268829405845905775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4742664358439207794541033 3556998268829405845905775)
        ·
          refine ⟨5335497403244108768858663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3556998268829405845905775 5335497403244108768858663)
          ·
            refine ⟨8003246104866163153287995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5335497403244108768858663 8003246104866163153287995)
            ·
              refine ⟨12004869157299244729931993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8003246104866163153287995 12004869157299244729931993)
              ·
                refine ⟨9003651867974433547448995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12004869157299244729931993 9003651867974433547448995)
                ·
                  refine ⟨13505477801961650321173493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9003651867974433547448995 13505477801961650321173493)
                  ·
                    refine ⟨1266138543933904717610015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13505477801961650321173493 1266138543933904717610015)
                    ·
                      rfl

theorem cell22_3698694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3698694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698694 prefixEnd_3698694 := by exact prefixLift 3698694
  have htrace : WordTrace (prefixWord ++ tailWord_3698694) baseStart_3698694 baseEnd_3698694 := by
    simpa [prefixWord, tailWord_3698694, baseEnd_3698694] using wordTrace_append hprefix tailTrace_3698694
  have hstable : (prefixWord ++ tailWord_3698694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698694).length < 2 ^ (prefixWord ++ tailWord_3698694).sum := by decide
  have hdescent : baseEnd_3698694 < baseStart_3698694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698748 : List Nat := [2, 2, 2, 2, 2, 1, 2, 4, 1, 4]
def baseStart_3698748 : Nat := 118140960795 + 3698748 * 2 ^ 59
def prefixEnd_3698748 : Nat := 4983230072969 + 3 ^ 40 * 3698748 * 2
def baseEnd_3698748 : Nat := 1266157029237466576759849

theorem tailTrace_3698748 : CollatzResearch.WordTrace tailWord_3698748 prefixEnd_3698748 1266157029237466576759849 := by
  unfold tailWord_3698748
  simp only [CollatzResearch.WordTrace]
  refine ⟨67452211202037583355816449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89936281602716777807755265 67452211202037583355816449)
  ·
    refine ⟨50589158401528187516862337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67452211202037583355816449 50589158401528187516862337)
    ·
      refine ⟨37941868801146140637646753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50589158401528187516862337 37941868801146140637646753)
      ·
        refine ⟨28456401600859605478235065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37941868801146140637646753 28456401600859605478235065)
        ·
          refine ⟨21342301200644704108676299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28456401600859605478235065 21342301200644704108676299)
          ·
            refine ⟨32013451800967056163014449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21342301200644704108676299 32013451800967056163014449)
            ·
              refine ⟨24010088850725292122260837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32013451800967056163014449 24010088850725292122260837)
              ·
                refine ⟨4501891659510992272923907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24010088850725292122260837 4501891659510992272923907)
                ·
                  refine ⟨6752837489266488409385861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4501891659510992272923907 6752837489266488409385861)
                  ·
                    refine ⟨1266157029237466576759849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6752837489266488409385861 1266157029237466576759849)
                    ·
                      rfl

theorem cell22_3698748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_3698748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698748 prefixEnd_3698748 := by exact prefixLift 3698748
  have htrace : WordTrace (prefixWord ++ tailWord_3698748) baseStart_3698748 baseEnd_3698748 := by
    simpa [prefixWord, tailWord_3698748, baseEnd_3698748] using wordTrace_append hprefix tailTrace_3698748
  have hstable : (prefixWord ++ tailWord_3698748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698748).length < 2 ^ (prefixWord ++ tailWord_3698748).sum := by decide
  have hdescent : baseEnd_3698748 < baseStart_3698748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698761 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 1, 5]
def baseStart_3698761 : Nat := 118140960795 + 3698761 * 2 ^ 59
def prefixEnd_3698761 : Nat := 4983230072969 + 3 ^ 40 * 3698761 * 2
def baseEnd_3698761 : Nat := 1266161479403138876184809

theorem tailTrace_3698761 : CollatzResearch.WordTrace tailWord_3698761 prefixEnd_3698761 1266161479403138876184809 := by
  unfold tailWord_3698761
  simp only [CollatzResearch.WordTrace]
  refine ⟨134904896553028069931856137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89936597702018713287904091 134904896553028069931856137)
  ·
    refine ⟨101178672414771052448892103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134904896553028069931856137 101178672414771052448892103)
    ·
      refine ⟨151768008622156578673338155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101178672414771052448892103 151768008622156578673338155)
      ·
        refine ⟨227652012933234868010007233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151768008622156578673338155 227652012933234868010007233)
        ·
          refine ⟨170739009699926151007505425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227652012933234868010007233 170739009699926151007505425)
          ·
            refine ⟨128054257274944613255629069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170739009699926151007505425 128054257274944613255629069)
            ·
              refine ⟨48020346478104229970860901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128054257274944613255629069 48020346478104229970860901)
              ·
                refine ⟨9003814964644543119536419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48020346478104229970860901 9003814964644543119536419)
                ·
                  refine ⟨13505722446966814679304629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9003814964644543119536419 13505722446966814679304629)
                  ·
                    refine ⟨1266161479403138876184809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13505722446966814679304629 1266161479403138876184809)
                    ·
                      rfl

theorem cell22_3698761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_3698761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698761 prefixEnd_3698761 := by exact prefixLift 3698761
  have htrace : WordTrace (prefixWord ++ tailWord_3698761) baseStart_3698761 baseEnd_3698761 := by
    simpa [prefixWord, tailWord_3698761, baseEnd_3698761] using wordTrace_append hprefix tailTrace_3698761
  have hstable : (prefixWord ++ tailWord_3698761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698761).length < 2 ^ (prefixWord ++ tailWord_3698761).sum := by decide
  have hdescent : baseEnd_3698761 < baseStart_3698761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698765 : List Nat := [1, 6, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_3698765 : Nat := 118140960795 + 3698765 * 2 ^ 59
def prefixEnd_3698765 : Nat := 4983230072969 + 3 ^ 40 * 3698765 * 2
def baseEnd_3698765 : Nat := 1266162848684884199084797

theorem tailTrace_3698765 : CollatzResearch.WordTrace tailWord_3698765 prefixEnd_3698765 1266162848684884199084797 := by
  unfold tailWord_3698765
  simp only [CollatzResearch.WordTrace]
  refine ⟨134905042445013578615001749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89936694963342385743334499 134905042445013578615001749)
  ·
    refine ⟨6323673864610011497578207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134905042445013578615001749 6323673864610011497578207)
    ·
      refine ⟨9485510796915017246367311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6323673864610011497578207 9485510796915017246367311)
      ·
        refine ⟨14228266195372525869550967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9485510796915017246367311 14228266195372525869550967)
        ·
          refine ⟨21342399293058788804326451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14228266195372525869550967 21342399293058788804326451)
          ·
            refine ⟨32013598939588183206489677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21342399293058788804326451 32013598939588183206489677)
            ·
              refine ⟨12005099602345568702433629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32013598939588183206489677 12005099602345568702433629)
              ·
                refine ⟨4501912350879588263412611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12005099602345568702433629 4501912350879588263412611)
                ·
                  refine ⟨6752868526319382395118917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4501912350879588263412611 6752868526319382395118917)
                  ·
                    refine ⟨1266162848684884199084797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6752868526319382395118917 1266162848684884199084797)
                    ·
                      rfl

theorem cell22_3698765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_3698765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698765 prefixEnd_3698765 := by exact prefixLift 3698765
  have htrace : WordTrace (prefixWord ++ tailWord_3698765) baseStart_3698765 baseEnd_3698765 := by
    simpa [prefixWord, tailWord_3698765, baseEnd_3698765] using wordTrace_append hprefix tailTrace_3698765
  have hstable : (prefixWord ++ tailWord_3698765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698765).length < 2 ^ (prefixWord ++ tailWord_3698765).sum := by decide
  have hdescent : baseEnd_3698765 < baseStart_3698765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698778 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 4, 3]
def baseStart_3698778 : Nat := 118140960795 + 3698778 * 2 ^ 59
def prefixEnd_3698778 : Nat := 4983230072969 + 3 ^ 40 * 3698778 * 2
def baseEnd_3698778 : Nat := 1266167298850556498509757

theorem tailTrace_3698778 : CollatzResearch.WordTrace tailWord_3698778 prefixEnd_3698778 1266167298850556498509757 := by
  unfold tailWord_3698778
  simp only [CollatzResearch.WordTrace]
  refine ⟨33726379148491620458806247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89937011062644321223483325 33726379148491620458806247)
  ·
    refine ⟨50589568722737430688209371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33726379148491620458806247 50589568722737430688209371)
    ·
      refine ⟨75884353084106146032314057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50589568722737430688209371 75884353084106146032314057)
      ·
        refine ⟨56913264813079609524235543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75884353084106146032314057 56913264813079609524235543)
        ·
          refine ⟨85369897219619414286353315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56913264813079609524235543 85369897219619414286353315)
          ·
            refine ⟨128054845829429121429529973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85369897219619414286353315 128054845829429121429529973)
            ·
              refine ⟨12005141796508980134018435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128054845829429121429529973 12005141796508980134018435)
              ·
                refine ⟨18007712694763470201027653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12005141796508980134018435 18007712694763470201027653)
                ·
                  refine ⟨3376446130268150662692685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18007712694763470201027653 3376446130268150662692685)
                  ·
                    refine ⟨1266167298850556498509757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3376446130268150662692685 1266167298850556498509757)
                    ·
                      rfl

theorem cell22_3698778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_3698778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698778 prefixEnd_3698778 := by exact prefixLift 3698778
  have htrace : WordTrace (prefixWord ++ tailWord_3698778) baseStart_3698778 baseEnd_3698778 := by
    simpa [prefixWord, tailWord_3698778, baseEnd_3698778] using wordTrace_append hprefix tailTrace_3698778
  have hstable : (prefixWord ++ tailWord_3698778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698778).length < 2 ^ (prefixWord ++ tailWord_3698778).sum := by decide
  have hdescent : baseEnd_3698778 < baseStart_3698778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698780 : List Nat := [2, 2, 4, 1, 1, 2, 2, 4, 4]
def baseStart_3698780 : Nat := 118140960795 + 3698780 * 2 ^ 59
def prefixEnd_3698780 : Nat := 4983230072969 + 3 ^ 40 * 3698780 * 2
def baseEnd_3698780 : Nat := 422055994497143053319917

theorem tailTrace_3698780 : CollatzResearch.WordTrace tailWord_3698780 prefixEnd_3698780 422055994497143053319917 := by
  unfold tailWord_3698780
  simp only [CollatzResearch.WordTrace]
  refine ⟨67452794769979618088398897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89937059693306157451198529 67452794769979618088398897)
  ·
    refine ⟨50589596077484713566299173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67452794769979618088398897 50589596077484713566299173)
    ·
      refine ⟨9485549264528383793681095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50589596077484713566299173 9485549264528383793681095)
      ·
        refine ⟨14228323896792575690521643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9485549264528383793681095 14228323896792575690521643)
        ·
          refine ⟨21342485845188863535782465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14228323896792575690521643 21342485845188863535782465)
          ·
            refine ⟨16006864383891647651836849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21342485845188863535782465 16006864383891647651836849)
            ·
              refine ⟨12005148287918735738877637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16006864383891647651836849 12005148287918735738877637)
              ·
                refine ⟨2250965303984762951039557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12005148287918735738877637 2250965303984762951039557)
                ·
                  refine ⟨422055994497143053319917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2250965303984762951039557 422055994497143053319917)
                  ·
                    rfl

theorem cell22_3698780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_3698780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698780 prefixEnd_3698780 := by exact prefixLift 3698780
  have htrace : WordTrace (prefixWord ++ tailWord_3698780) baseStart_3698780 baseEnd_3698780 := by
    simpa [prefixWord, tailWord_3698780, baseEnd_3698780] using wordTrace_append hprefix tailTrace_3698780
  have hstable : (prefixWord ++ tailWord_3698780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698780).length < 2 ^ (prefixWord ++ tailWord_3698780).sum := by decide
  have hdescent : baseEnd_3698780 < baseStart_3698780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698791 : List Nat := [1, 1, 5, 1, 1, 2, 2, 9]
def baseStart_3698791 : Nat := 118140960795 + 3698791 * 2 ^ 59
def prefixEnd_3698791 : Nat := 4983230072969 + 3 ^ 40 * 3698791 * 2
def baseEnd_3698791 : Nat := 140685749890692088659413

theorem tailTrace_3698791 : CollatzResearch.WordTrace tailWord_3698791 prefixEnd_3698791 140685749890692088659413 := by
  unfold tailWord_3698791
  simp only [CollatzResearch.WordTrace]
  refine ⟨134905990742919385055448227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89937327161946256703632151 134905990742919385055448227)
  ·
    refine ⟨202358986114379077583172341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134905990742919385055448227 202358986114379077583172341)
    ·
      refine ⟨18971154948223038523422407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 202358986114379077583172341 18971154948223038523422407)
      ·
        refine ⟨28456732422334557785133611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18971154948223038523422407 28456732422334557785133611)
        ·
          refine ⟨42685098633501836677700417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28456732422334557785133611 42685098633501836677700417)
          ·
            refine ⟨32013823975126377508275313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42685098633501836677700417 32013823975126377508275313)
            ·
              refine ⟨24010367981344783131206485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32013823975126377508275313 24010367981344783131206485)
              ·
                refine ⟨140685749890692088659413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24010367981344783131206485 140685749890692088659413)
                ·
                  rfl

theorem cell22_3698791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 9].length) (baseStart_3698791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698791 prefixEnd_3698791 := by exact prefixLift 3698791
  have htrace : WordTrace (prefixWord ++ tailWord_3698791) baseStart_3698791 baseEnd_3698791 := by
    simpa [prefixWord, tailWord_3698791, baseEnd_3698791] using wordTrace_append hprefix tailTrace_3698791
  have hstable : (prefixWord ++ tailWord_3698791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698791).length < 2 ^ (prefixWord ++ tailWord_3698791).sum := by decide
  have hdescent : baseEnd_3698791 < baseStart_3698791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698823 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 5, 3]
def baseStart_3698823 : Nat := 118140960795 + 3698823 * 2 ^ 59
def prefixEnd_3698823 : Nat := 4983230072969 + 3 ^ 40 * 3698823 * 2
def baseEnd_3698823 : Nat := 1266182703270191381134619

theorem tailTrace_3698823 : CollatzResearch.WordTrace tailWord_3698823 prefixEnd_3698823 1266182703270191381134619 := by
  unfold tailWord_3698823
  simp only [CollatzResearch.WordTrace]
  refine ⟨134907157878803454520613123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89938105252535636347075415 134907157878803454520613123)
  ·
    refine ⟨202360736818205181780919685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134907157878803454520613123 202360736818205181780919685)
    ·
      refine ⟨37942638153413471583922441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202360736818205181780919685 37942638153413471583922441)
      ·
        refine ⟨28456978615060103687941831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37942638153413471583922441 28456978615060103687941831)
        ·
          refine ⟨42685467922590155531912747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28456978615060103687941831 42685467922590155531912747)
          ·
            refine ⟨64028201883885233297869121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42685467922590155531912747 64028201883885233297869121)
            ·
              refine ⟨48021151412913924973401841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64028201883885233297869121 48021151412913924973401841)
              ·
                refine ⟨36015863559685443730051381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48021151412913924973401841 36015863559685443730051381)
                ·
                  refine ⟨3376487208720510349692317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36015863559685443730051381 3376487208720510349692317)
                  ·
                    refine ⟨1266182703270191381134619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3376487208720510349692317 1266182703270191381134619)
                    ·
                      rfl

theorem cell22_3698823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_3698823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698823 prefixEnd_3698823 := by exact prefixLift 3698823
  have htrace : WordTrace (prefixWord ++ tailWord_3698823) baseStart_3698823 baseEnd_3698823 := by
    simpa [prefixWord, tailWord_3698823, baseEnd_3698823] using wordTrace_append hprefix tailTrace_3698823
  have hstable : (prefixWord ++ tailWord_3698823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698823).length < 2 ^ (prefixWord ++ tailWord_3698823).sum := by decide
  have hdescent : baseEnd_3698823 < baseStart_3698823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698846 : List Nat := [4, 3, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_3698846 : Nat := 118140960795 + 3698846 * 2 ^ 59
def prefixEnd_3698846 : Nat := 4983230072969 + 3 ^ 40 * 3698846 * 2
def baseEnd_3698846 : Nat := 1266190576640226987809549

theorem tailTrace_3698846 : CollatzResearch.WordTrace tailWord_3698846 prefixEnd_3698846 1266190576640226987809549 := by
  unfold tailWord_3698846
  simp only [CollatzResearch.WordTrace]
  refine ⟨16863499594715016181087549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89938664505146752965800261 16863499594715016181087549)
  ·
    refine ⟨6323812348018131067907831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16863499594715016181087549 6323812348018131067907831)
    ·
      refine ⟨9485718522027196601861747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6323812348018131067907831 9485718522027196601861747)
      ·
        refine ⟨14228577783040794902792621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9485718522027196601861747 14228577783040794902792621)
        ·
          refine ⟨5335716668640298088547233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14228577783040794902792621 5335716668640298088547233)
          ·
            refine ⟨4001787501480223566410425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5335716668640298088547233 4001787501480223566410425)
            ·
              refine ⟨3001340626110167674807819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4001787501480223566410425 3001340626110167674807819)
              ·
                refine ⟨4502010939165251512211729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3001340626110167674807819 4502010939165251512211729)
                ·
                  refine ⟨3376508204373938634158797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4502010939165251512211729 3376508204373938634158797)
                  ·
                    refine ⟨1266190576640226987809549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3376508204373938634158797 1266190576640226987809549)
                    ·
                      rfl

theorem cell22_3698846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_3698846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698846 prefixEnd_3698846 := by exact prefixLift 3698846
  have htrace : WordTrace (prefixWord ++ tailWord_3698846) baseStart_3698846 baseEnd_3698846 := by
    simpa [prefixWord, tailWord_3698846, baseEnd_3698846] using wordTrace_append hprefix tailTrace_3698846
  have hstable : (prefixWord ++ tailWord_3698846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698846).length < 2 ^ (prefixWord ++ tailWord_3698846).sum := by decide
  have hdescent : baseEnd_3698846 < baseStart_3698846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698853 : List Nat := [1, 3, 1, 2, 1, 3, 3, 3, 5]
def baseStart_3698853 : Nat := 118140960795 + 3698853 * 2 ^ 59
def prefixEnd_3698853 : Nat := 4983230072969 + 3 ^ 40 * 3698853 * 2
def baseEnd_3698853 : Nat := 422064324294427100961509

theorem tailTrace_3698853 : CollatzResearch.WordTrace tailWord_3698853 prefixEnd_3698853 422064324294427100961509 := by
  unfold tailWord_3698853
  simp only [CollatzResearch.WordTrace]
  refine ⟨134908252068694769644205213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89938834712463179762803475 134908252068694769644205213)
  ·
    refine ⟨50590594525760538616576955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134908252068694769644205213 50590594525760538616576955)
    ·
      refine ⟨75885891788640807924865433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50590594525760538616576955 75885891788640807924865433)
      ·
        refine ⟨56914418841480605943649075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75885891788640807924865433 56914418841480605943649075)
        ·
          refine ⟨85371628262220908915473613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56914418841480605943649075 85371628262220908915473613)
          ·
            refine ⟨32014360598332840843302605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85371628262220908915473613 32014360598332840843302605)
            ·
              refine ⟨12005385224374815316238477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32014360598332840843302605 12005385224374815316238477)
              ·
                refine ⟨4502019459140555743589429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12005385224374815316238477 4502019459140555743589429)
                ·
                  refine ⟨422064324294427100961509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4502019459140555743589429 422064324294427100961509)
                  ·
                    rfl

theorem cell22_3698853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_3698853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698853 prefixEnd_3698853 := by exact prefixLift 3698853
  have htrace : WordTrace (prefixWord ++ tailWord_3698853) baseStart_3698853 baseEnd_3698853 := by
    simpa [prefixWord, tailWord_3698853, baseEnd_3698853] using wordTrace_append hprefix tailTrace_3698853
  have hstable : (prefixWord ++ tailWord_3698853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698853).length < 2 ^ (prefixWord ++ tailWord_3698853).sum := by decide
  have hdescent : baseEnd_3698853 < baseStart_3698853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698902 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3698902 : Nat := 118140960795 + 3698902 * 2 ^ 59
def prefixEnd_3698902 : Nat := 4983230072969 + 3 ^ 40 * 3698902 * 2
def baseEnd_3698902 : Nat := 1266209746584661508409377

theorem tailTrace_3698902 : CollatzResearch.WordTrace tailWord_3698902 prefixEnd_3698902 1266209746584661508409377 := by
  unfold tailWord_3698902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8431877452844828188296185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89940026163678167341825973 8431877452844828188296185)
  ·
    refine ⟨6323908089633621141222139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8431877452844828188296185 6323908089633621141222139)
    ·
      refine ⟨9485862134450431711833209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6323908089633621141222139 9485862134450431711833209)
      ·
        refine ⟨7114396600837823783874907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9485862134450431711833209 7114396600837823783874907)
        ·
          refine ⟨10671594901256735675812361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7114396600837823783874907 10671594901256735675812361)
          ·
            refine ⟨8003696175942551756859271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10671594901256735675812361 8003696175942551756859271)
            ·
              refine ⟨12005544263913827635288907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8003696175942551756859271 12005544263913827635288907)
              ·
                refine ⟨18008316395870741452933361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12005544263913827635288907 18008316395870741452933361)
                ·
                  refine ⟨13506237296903056089700021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18008316395870741452933361 13506237296903056089700021)
                  ·
                    refine ⟨1266209746584661508409377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13506237296903056089700021 1266209746584661508409377)
                    ·
                      rfl

theorem cell22_3698902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3698902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698902 prefixEnd_3698902 := by exact prefixLift 3698902
  have htrace : WordTrace (prefixWord ++ tailWord_3698902) baseStart_3698902 baseEnd_3698902 := by
    simpa [prefixWord, tailWord_3698902, baseEnd_3698902] using wordTrace_append hprefix tailTrace_3698902
  have hstable : (prefixWord ++ tailWord_3698902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698902).length < 2 ^ (prefixWord ++ tailWord_3698902).sum := by decide
  have hdescent : baseEnd_3698902 < baseStart_3698902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698930 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_3698930 : Nat := 118140960795 + 3698930 * 2 ^ 59
def prefixEnd_3698930 : Nat := 4983230072969 + 3 ^ 40 * 3698930 * 2
def baseEnd_3698930 : Nat := 1266219331556878768709291

theorem tailTrace_3698930 : CollatzResearch.WordTrace tailWord_3698930 prefixEnd_3698930 1266219331556878768709291 := by
  unfold tailWord_3698930
  simp only [CollatzResearch.WordTrace]
  refine ⟨33727765122353952948689561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89940706992943874529838829 33727765122353952948689561)
  ·
    refine ⟨25295823841765464711517171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33727765122353952948689561 25295823841765464711517171)
    ·
      refine ⟨37943735762648197067275757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25295823841765464711517171 37943735762648197067275757)
      ·
        refine ⟨14228900910993073900228409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37943735762648197067275757 14228900910993073900228409)
        ·
          refine ⟨10671675683244805425171307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14228900910993073900228409 10671675683244805425171307)
          ·
            refine ⟨16007513524867208137756961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10671675683244805425171307 16007513524867208137756961)
            ·
              refine ⟨12005635143650406103317721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16007513524867208137756961 12005635143650406103317721)
              ·
                refine ⟨9004226357737804577488291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12005635143650406103317721 9004226357737804577488291)
                ·
                  refine ⟨13506339536606706866232437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9004226357737804577488291 13506339536606706866232437)
                  ·
                    refine ⟨1266219331556878768709291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13506339536606706866232437 1266219331556878768709291)
                    ·
                      rfl

theorem cell22_3698930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_3698930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698930 prefixEnd_3698930 := by exact prefixLift 3698930
  have htrace : WordTrace (prefixWord ++ tailWord_3698930) baseStart_3698930 baseEnd_3698930 := by
    simpa [prefixWord, tailWord_3698930, baseEnd_3698930] using wordTrace_append hprefix tailTrace_3698930
  have hstable : (prefixWord ++ tailWord_3698930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698930).length < 2 ^ (prefixWord ++ tailWord_3698930).sum := by decide
  have hdescent : baseEnd_3698930 < baseStart_3698930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698983 : List Nat := [1, 1, 8, 1, 1, 2, 1, 3, 4]
def baseStart_3698983 : Nat := 118140960795 + 3698983 * 2 ^ 59
def prefixEnd_3698983 : Nat := 4983230072969 + 3 ^ 40 * 3698983 * 2
def baseEnd_3698983 : Nat := 422079158180001432378043

theorem tailTrace_3698983 : CollatzResearch.WordTrace tailWord_3698983 prefixEnd_3698983 422079158180001432378043 := by
  unfold tailWord_3698983
  simp only [CollatzResearch.WordTrace]
  refine ⟨134912993558223801846437603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89941995705482534564291735 134912993558223801846437603)
  ·
    refine ⟨202369490337335702769656405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134912993558223801846437603 202369490337335702769656405)
    ·
      refine ⟨2371517464890652766831911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 202369490337335702769656405 2371517464890652766831911)
      ·
        refine ⟨3557276197335979150247867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2371517464890652766831911 3557276197335979150247867)
        ·
          refine ⟨5335914296003968725371801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3557276197335979150247867 5335914296003968725371801)
          ·
            refine ⟨4001935722002976544028851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5335914296003968725371801 4001935722002976544028851)
            ·
              refine ⟨6002903583004464816043277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4001935722002976544028851 6002903583004464816043277)
              ·
                refine ⟨2251088843626674306016229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6002903583004464816043277 2251088843626674306016229)
                ·
                  refine ⟨422079158180001432378043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2251088843626674306016229 422079158180001432378043)
                  ·
                    rfl

theorem cell22_3698983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 4].length) (baseStart_3698983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698983 prefixEnd_3698983 := by exact prefixLift 3698983
  have htrace : WordTrace (prefixWord ++ tailWord_3698983) baseStart_3698983 baseEnd_3698983 := by
    simpa [prefixWord, tailWord_3698983, baseEnd_3698983] using wordTrace_append hprefix tailTrace_3698983
  have hstable : (prefixWord ++ tailWord_3698983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698983).length < 2 ^ (prefixWord ++ tailWord_3698983).sum := by decide
  have hdescent : baseEnd_3698983 < baseStart_3698983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698988 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 7]
def baseStart_3698988 : Nat := 118140960795 + 3698988 * 2 ^ 59
def prefixEnd_3698988 : Nat := 4983230072969 + 3 ^ 40 * 3698988 * 2
def baseEnd_3698988 : Nat := 422079728714061983586371

theorem tailTrace_3698988 : CollatzResearch.WordTrace tailWord_3698988 prefixEnd_3698988 422079728714061983586371 := by
  unfold tailWord_3698988
  simp only [CollatzResearch.WordTrace]
  refine ⟨67456587961602843850184809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89942117282137125133579745 67456587961602843850184809)
  ·
    refine ⟨50592440971202132887638607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67456587961602843850184809 50592440971202132887638607)
    ·
      refine ⟨75888661456803199331457911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50592440971202132887638607 75888661456803199331457911)
      ·
        refine ⟨113832992185204798997186867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75888661456803199331457911 113832992185204798997186867)
        ·
          refine ⟨170749488277807198495780301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113832992185204798997186867 170749488277807198495780301)
          ·
            refine ⟨64031058104177699435917613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170749488277807198495780301 64031058104177699435917613)
            ·
              refine ⟨24011646789066637288469105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64031058104177699435917613 24011646789066637288469105)
              ·
                refine ⟨18008735091799977966351829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24011646789066637288469105 18008735091799977966351829)
                ·
                  refine ⟨422079728714061983586371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18008735091799977966351829 422079728714061983586371)
                  ·
                    rfl

theorem cell22_3698988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_3698988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698988 prefixEnd_3698988 := by exact prefixLift 3698988
  have htrace : WordTrace (prefixWord ++ tailWord_3698988) baseStart_3698988 baseEnd_3698988 := by
    simpa [prefixWord, tailWord_3698988, baseEnd_3698988] using wordTrace_append hprefix tailTrace_3698988
  have hstable : (prefixWord ++ tailWord_3698988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698988).length < 2 ^ (prefixWord ++ tailWord_3698988).sum := by decide
  have hdescent : baseEnd_3698988 < baseStart_3698988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3698992 : List Nat := [2, 1, 1, 1, 2, 2, 2, 7, 1, 3]
def baseStart_3698992 : Nat := 118140960795 + 3698992 * 2 ^ 59
def prefixEnd_3698992 : Nat := 4983230072969 + 3 ^ 40 * 3698992 * 2
def baseEnd_3698992 : Nat := 1266240555423931273659101

theorem tailTrace_3698992 : CollatzResearch.WordTrace tailWord_3698992 prefixEnd_3698992 1266240555423931273659101 := by
  unfold tailWord_3698992
  simp only [CollatzResearch.WordTrace]
  refine ⟨67456660907595598191757615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89942214543460797589010153 67456660907595598191757615)
  ·
    refine ⟨101184991361393397287636423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67456660907595598191757615 101184991361393397287636423)
    ·
      refine ⟨151777487042090095931454635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101184991361393397287636423 151777487042090095931454635)
      ·
        refine ⟨227666230563135143897181953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151777487042090095931454635 227666230563135143897181953)
        ·
          refine ⟨170749672922351357922886465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227666230563135143897181953 170749672922351357922886465)
          ·
            refine ⟨128062254691763518442164849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170749672922351357922886465 128062254691763518442164849)
            ·
              refine ⟨96046691018822638831623637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128062254691763518442164849 96046691018822638831623637)
              ·
                refine ⟨2251094320753655597616179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 96046691018822638831623637 2251094320753655597616179)
                ·
                  refine ⟨3376641481130483396424269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251094320753655597616179 3376641481130483396424269)
                  ·
                    refine ⟨1266240555423931273659101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3376641481130483396424269 1266240555423931273659101)
                    ·
                      rfl

theorem cell22_3698992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7, 1, 3].length) (baseStart_3698992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3698992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3698992 prefixEnd_3698992 := by exact prefixLift 3698992
  have htrace : WordTrace (prefixWord ++ tailWord_3698992) baseStart_3698992 baseEnd_3698992 := by
    simpa [prefixWord, tailWord_3698992, baseEnd_3698992] using wordTrace_append hprefix tailTrace_3698992
  have hstable : (prefixWord ++ tailWord_3698992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3698992).length < 2 ^ (prefixWord ++ tailWord_3698992).sum := by decide
  have hdescent : baseEnd_3698992 < baseStart_3698992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3698992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699018 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_3699018 : Nat := 118140960795 + 3699018 * 2 ^ 59
def prefixEnd_3699018 : Nat := 4983230072969 + 3 ^ 40 * 3699018 * 2
def baseEnd_3699018 : Nat := 1266249455755275872509021

theorem tailTrace_3699018 : CollatzResearch.WordTrace tailWord_3699018 prefixEnd_3699018 1266249455755275872509021 := by
  unfold tailWord_3699018
  simp only [CollatzResearch.WordTrace]
  refine ⟨33728567528274250705990427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89942846742064668549307805 33728567528274250705990427)
  ·
    refine ⟨50592851292411376058985641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33728567528274250705990427 50592851292411376058985641)
    ·
      refine ⟨37944638469308532044239231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50592851292411376058985641 37944638469308532044239231)
      ·
        refine ⟨56916957703962798066358847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37944638469308532044239231 56916957703962798066358847)
        ·
          refine ⟨85375436555944197099538271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56916957703962798066358847 85375436555944197099538271)
          ·
            refine ⟨128063154833916295649307407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85375436555944197099538271 128063154833916295649307407)
            ·
              refine ⟨192094732250874443473961111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128063154833916295649307407 192094732250874443473961111)
              ·
                refine ⟨288142098376311665210941667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192094732250874443473961111 288142098376311665210941667)
                ·
                  refine ⟨432213147564467497816412501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 288142098376311665210941667 432213147564467497816412501)
                  ·
                    refine ⟨1266249455755275872509021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 432213147564467497816412501 1266249455755275872509021)
                    ·
                      rfl

theorem cell22_3699018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_3699018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699018 prefixEnd_3699018 := by exact prefixLift 3699018
  have htrace : WordTrace (prefixWord ++ tailWord_3699018) baseStart_3699018 baseEnd_3699018 := by
    simpa [prefixWord, tailWord_3699018, baseEnd_3699018] using wordTrace_append hprefix tailTrace_3699018
  have hstable : (prefixWord ++ tailWord_3699018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699018).length < 2 ^ (prefixWord ++ tailWord_3699018).sum := by decide
  have hdescent : baseEnd_3699018 < baseStart_3699018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699033 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 8]
def baseStart_3699033 : Nat := 118140960795 + 3699033 * 2 ^ 59
def prefixEnd_3699033 : Nat := 4983230072969 + 3 ^ 40 * 3699033 * 2
def baseEnd_3699033 : Nat := 422084863520606944461325

theorem tailTrace_3699033 : CollatzResearch.WordTrace tailWord_3699033 prefixEnd_3699033 422084863520606944461325 := by
  unfold tailWord_3699033
  simp only [CollatzResearch.WordTrace]
  refine ⟨134914817208042660385757753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89943211472028440257171835 134914817208042660385757753)
  ·
    refine ⟨101186112906031995289318315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134914817208042660385757753 101186112906031995289318315)
    ·
      refine ⟨151779169359047992933977473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101186112906031995289318315 151779169359047992933977473)
      ·
        refine ⟨113834377019285994700483105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151779169359047992933977473 113834377019285994700483105)
        ·
          refine ⟨85375782764464496025362329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113834377019285994700483105 85375782764464496025362329)
          ·
            refine ⟨64031837073348372019021747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85375782764464496025362329 64031837073348372019021747)
            ·
              refine ⟨96047755610022558028532621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64031837073348372019021747 96047755610022558028532621)
              ·
                refine ⟨36017908353758459260699733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96047755610022558028532621 36017908353758459260699733)
                ·
                  refine ⟨422084863520606944461325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36017908353758459260699733 422084863520606944461325)
                  ·
                    rfl

theorem cell22_3699033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 8].length) (baseStart_3699033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699033 prefixEnd_3699033 := by exact prefixLift 3699033
  have htrace : WordTrace (prefixWord ++ tailWord_3699033) baseStart_3699033 baseEnd_3699033 := by
    simpa [prefixWord, tailWord_3699033, baseEnd_3699033] using wordTrace_append hprefix tailTrace_3699033
  have hstable : (prefixWord ++ tailWord_3699033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699033).length < 2 ^ (prefixWord ++ tailWord_3699033).sum := by decide
  have hdescent : baseEnd_3699033 < baseStart_3699033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699067 : List Nat := [1, 1, 1, 1, 1, 8, 1, 4, 4]
def baseStart_3699067 : Nat := 118140960795 + 3699067 * 2 ^ 59
def prefixEnd_3699067 : Nat := 4983230072969 + 3 ^ 40 * 3699067 * 2
def baseEnd_3699067 : Nat := 422088743152218692677957

theorem tailTrace_3699067 : CollatzResearch.WordTrace tailWord_3699067 prefixEnd_3699067 422088743152218692677957 := by
  unfold tailWord_3699067
  simp only [CollatzResearch.WordTrace]
  refine ⟨134916057289919484192495455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89944038193279656128330303 134916057289919484192495455)
  ·
    refine ⟨202374085934879226288743183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134916057289919484192495455 202374085934879226288743183)
    ·
      refine ⟨303561128902318839433114775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202374085934879226288743183 303561128902318839433114775)
      ·
        refine ⟨455341693353478259149672163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303561128902318839433114775 455341693353478259149672163)
        ·
          refine ⟨683012540030217388724508245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455341693353478259149672163 683012540030217388724508245)
          ·
            refine ⟨8004053203479110024115331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 683012540030217388724508245 8004053203479110024115331)
            ·
              refine ⟨12006079805218665036172997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8004053203479110024115331 12006079805218665036172997)
              ·
                refine ⟨2251139963478499694282437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12006079805218665036172997 2251139963478499694282437)
                ·
                  refine ⟨422088743152218692677957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2251139963478499694282437 422088743152218692677957)
                  ·
                    rfl

theorem cell22_3699067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 4].length) (baseStart_3699067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699067 prefixEnd_3699067 := by exact prefixLift 3699067
  have htrace : WordTrace (prefixWord ++ tailWord_3699067) baseStart_3699067 baseEnd_3699067 := by
    simpa [prefixWord, tailWord_3699067, baseEnd_3699067] using wordTrace_append hprefix tailTrace_3699067
  have hstable : (prefixWord ++ tailWord_3699067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699067).length < 2 ^ (prefixWord ++ tailWord_3699067).sum := by decide
  have hdescent : baseEnd_3699067 < baseStart_3699067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699080 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 1, 6]
def baseStart_3699080 : Nat := 118140960795 + 3699080 * 2 ^ 59
def prefixEnd_3699080 : Nat := 4983230072969 + 3 ^ 40 * 3699080 * 2
def baseEnd_3699080 : Nat := 1266270679622328377458831

theorem tailTrace_3699080 : CollatzResearch.WordTrace tailWord_3699080 prefixEnd_3699080 1266270679622328377458831 := by
  unfold tailWord_3699080
  simp only [CollatzResearch.WordTrace]
  refine ⟨67458265719436193706359347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89944354292581591608479129 67458265719436193706359347)
  ·
    refine ⟨101187398579154290559539021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67458265719436193706359347 101187398579154290559539021)
    ·
      refine ⟨37945274467182858959827133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101187398579154290559539021 37945274467182858959827133)
      ·
        refine ⟨14229477925193572109935175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37945274467182858959827133 14229477925193572109935175)
        ·
          refine ⟨21344216887790358164902763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14229477925193572109935175 21344216887790358164902763)
          ·
            refine ⟨32016325331685537247354145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21344216887790358164902763 32016325331685537247354145)
            ·
              refine ⟨24012243998764152935515609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32016325331685537247354145 24012243998764152935515609)
              ·
                refine ⟨18009182999073114701636707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24012243998764152935515609 18009182999073114701636707)
                ·
                  refine ⟨27013774498609672052455061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18009182999073114701636707 27013774498609672052455061)
                  ·
                    refine ⟨1266270679622328377458831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27013774498609672052455061 1266270679622328377458831)
                    ·
                      rfl

theorem cell22_3699080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_3699080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699080 prefixEnd_3699080 := by exact prefixLift 3699080
  have htrace : WordTrace (prefixWord ++ tailWord_3699080) baseStart_3699080 baseEnd_3699080 := by
    simpa [prefixWord, tailWord_3699080, baseEnd_3699080] using wordTrace_append hprefix tailTrace_3699080
  have hstable : (prefixWord ++ tailWord_3699080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699080).length < 2 ^ (prefixWord ++ tailWord_3699080).sum := by decide
  have hdescent : baseEnd_3699080 < baseStart_3699080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699112 : List Nat := [2, 1, 6, 1, 1, 2, 9]
def baseStart_3699112 : Nat := 118140960795 + 3699112 * 2 ^ 59
def prefixEnd_3699112 : Nat := 4983230072969 + 3 ^ 40 * 3699112 * 2
def baseEnd_3699112 : Nat := 46899319773195961505879

theorem tailTrace_3699112 : CollatzResearch.WordTrace tailWord_3699112 prefixEnd_3699112 46899319773195961505879 := by
  unfold tailWord_3699112
  simp only [CollatzResearch.WordTrace]
  refine ⟨67458849287378228438941795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89945132383170971251922393 67458849287378228438941795)
  ·
    refine ⟨101188273931067342658412693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67458849287378228438941795 101188273931067342658412693)
    ·
      refine ⟨4743200340518781687113095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101188273931067342658412693 4743200340518781687113095)
      ·
        refine ⟨7114800510778172530669643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4743200340518781687113095 7114800510778172530669643)
        ·
          refine ⟨10672200766167258796004465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7114800510778172530669643 10672200766167258796004465)
          ·
            refine ⟨8004150574625444097003349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10672200766167258796004465 8004150574625444097003349)
            ·
              refine ⟨46899319773195961505879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8004150574625444097003349 46899319773195961505879)
              ·
                rfl

theorem cell22_3699112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 9].length) (baseStart_3699112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699112 prefixEnd_3699112 := by exact prefixLift 3699112
  have htrace : WordTrace (prefixWord ++ tailWord_3699112) baseStart_3699112 baseEnd_3699112 := by
    simpa [prefixWord, tailWord_3699112, baseEnd_3699112] using wordTrace_append hprefix tailTrace_3699112
  have hstable : (prefixWord ++ tailWord_3699112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699112).length < 2 ^ (prefixWord ++ tailWord_3699112).sum := by decide
  have hdescent : baseEnd_3699112 < baseStart_3699112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699127 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 3, 3]
def baseStart_3699127 : Nat := 118140960795 + 3699127 * 2 ^ 59
def prefixEnd_3699127 : Nat := 4983230072969 + 3 ^ 40 * 3699127 * 2
def baseEnd_3699127 : Nat := 1266286768682835921533687

theorem tailTrace_3699127 : CollatzResearch.WordTrace tailWord_3699127 prefixEnd_3699127 1266286768682835921533687 := by
  unfold tailWord_3699127
  simp only [CollatzResearch.WordTrace]
  refine ⟨134918245669702114439679635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89945497113134742959786423 134918245669702114439679635)
  ·
    refine ⟨202377368504553171659519453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134918245669702114439679635 202377368504553171659519453)
    ·
      refine ⟨75891513189207439372319795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 202377368504553171659519453 75891513189207439372319795)
      ·
        refine ⟨113837269783811159058479693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75891513189207439372319795 113837269783811159058479693)
        ·
          refine ⟨42688976168929184646929885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113837269783811159058479693 42688976168929184646929885)
          ·
            refine ⟨16008366063348444242598707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42688976168929184646929885 16008366063348444242598707)
            ·
              refine ⟨24012549095022666363898061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16008366063348444242598707 24012549095022666363898061)
              ·
                refine ⟨9004705910633499886461773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24012549095022666363898061 9004705910633499886461773)
                ·
                  refine ⟨3376764716487562457423165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9004705910633499886461773 3376764716487562457423165)
                  ·
                    refine ⟨1266286768682835921533687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3376764716487562457423165 1266286768682835921533687)
                    ·
                      rfl

theorem cell22_3699127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_3699127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699127 prefixEnd_3699127 := by exact prefixLift 3699127
  have htrace : WordTrace (prefixWord ++ tailWord_3699127) baseStart_3699127 baseEnd_3699127 := by
    simpa [prefixWord, tailWord_3699127, baseEnd_3699127] using wordTrace_append hprefix tailTrace_3699127
  have hstable : (prefixWord ++ tailWord_3699127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699127).length < 2 ^ (prefixWord ++ tailWord_3699127).sum := by decide
  have hdescent : baseEnd_3699127 < baseStart_3699127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699178 : List Nat := [3, 1, 3, 1, 3, 2, 3, 2, 1, 3]
def baseStart_3699178 : Nat := 118140960795 + 3699178 * 2 ^ 59
def prefixEnd_3699178 : Nat := 4983230072969 + 3 ^ 40 * 3699178 * 2
def baseEnd_3699178 : Nat := 1266304227025088788508531

theorem tailTrace_3699178 : CollatzResearch.WordTrace tailWord_3699178 prefixEnd_3699178 1266304227025088788508531 := by
  unfold tailWord_3699178
  simp only [CollatzResearch.WordTrace]
  refine ⟨33730026448129337537446547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89946737195011566766524125 33730026448129337537446547)
  ·
    refine ⟨50595039672194006306169821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33730026448129337537446547 50595039672194006306169821)
    ·
      refine ⟨18973139877072752364813683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50595039672194006306169821 18973139877072752364813683)
      ·
        refine ⟨28459709815609128547220525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18973139877072752364813683 28459709815609128547220525)
        ·
          refine ⟨10672391180853423205207697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28459709815609128547220525 10672391180853423205207697)
          ·
            refine ⟨8004293385640067403905773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10672391180853423205207697 8004293385640067403905773)
            ·
              refine ⟨3001610019615025276464665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8004293385640067403905773 3001610019615025276464665)
              ·
                refine ⟨2251207514711268957348499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001610019615025276464665 2251207514711268957348499)
                ·
                  refine ⟨3376811272066903436022749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251207514711268957348499 3376811272066903436022749)
                  ·
                    refine ⟨1266304227025088788508531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3376811272066903436022749 1266304227025088788508531)
                    ·
                      rfl

theorem cell22_3699178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_3699178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699178 prefixEnd_3699178 := by exact prefixLift 3699178
  have htrace : WordTrace (prefixWord ++ tailWord_3699178) baseStart_3699178 baseEnd_3699178 := by
    simpa [prefixWord, tailWord_3699178, baseEnd_3699178] using wordTrace_append hprefix tailTrace_3699178
  have hstable : (prefixWord ++ tailWord_3699178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699178).length < 2 ^ (prefixWord ++ tailWord_3699178).sum := by decide
  have hdescent : baseEnd_3699178 < baseStart_3699178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699200 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 7, 5]
def baseStart_3699200 : Nat := 118140960795 + 3699200 * 2 ^ 59
def prefixEnd_3699200 : Nat := 4983230072969 + 3 ^ 40 * 3699200 * 2
def baseEnd_3699200 : Nat := 1266311758074688064458463

theorem tailTrace_3699200 : CollatzResearch.WordTrace tailWord_3699200 prefixEnd_3699200 1266311758074688064458463 := by
  unfold tailWord_3699200
  simp only [CollatzResearch.WordTrace]
  refine ⟨67460454099218823953543527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89947272132291765271391369 67460454099218823953543527)
  ·
    refine ⟨101190681148828235930315291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67460454099218823953543527 101190681148828235930315291)
    ·
      refine ⟨151786021723242353895472937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101190681148828235930315291 151786021723242353895472937)
      ·
        refine ⟨113839516292431765421604703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151786021723242353895472937 113839516292431765421604703)
        ·
          refine ⟨170759274438647648132407055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113839516292431765421604703 170759274438647648132407055)
          ·
            refine ⟨256138911657971472198610583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170759274438647648132407055 256138911657971472198610583)
            ·
              refine ⟨384208367486957208297915875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256138911657971472198610583 384208367486957208297915875)
              ·
                refine ⟨576312551230435812446873813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384208367486957208297915875 576312551230435812446873813)
                ·
                  refine ⟨13507325419463339354223605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 576312551230435812446873813 13507325419463339354223605)
                  ·
                    refine ⟨1266311758074688064458463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13507325419463339354223605 1266311758074688064458463)
                    ·
                      rfl

theorem cell22_3699200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_3699200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699200 prefixEnd_3699200 := by exact prefixLift 3699200
  have htrace : WordTrace (prefixWord ++ tailWord_3699200) baseStart_3699200 baseEnd_3699200 := by
    simpa [prefixWord, tailWord_3699200, baseEnd_3699200] using wordTrace_append hprefix tailTrace_3699200
  have hstable : (prefixWord ++ tailWord_3699200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699200).length < 2 ^ (prefixWord ++ tailWord_3699200).sum := by decide
  have hdescent : baseEnd_3699200 < baseStart_3699200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699204 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_3699204 : Nat := 118140960795 + 3699204 * 2 ^ 59
def prefixEnd_3699204 : Nat := 4983230072969 + 3 ^ 40 * 3699204 * 2
def baseEnd_3699204 : Nat := 1266313127356433387358451

theorem tailTrace_3699204 : CollatzResearch.WordTrace tailWord_3699204 prefixEnd_3699204 1266313127356433387358451 := by
  unfold tailWord_3699204
  simp only [CollatzResearch.WordTrace]
  refine ⟨67460527045211578295116333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89947369393615437726821777 67460527045211578295116333)
  ·
    refine ⟨25297697641954341860668625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67460527045211578295116333 25297697641954341860668625)
    ·
      refine ⟨18973273231465756395501469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25297697641954341860668625 18973273231465756395501469)
      ·
        refine ⟨7114977461799658648313051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18973273231465756395501469 7114977461799658648313051)
        ·
          refine ⟨10672466192699487972469577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7114977461799658648313051 10672466192699487972469577)
          ·
            refine ⟨8004349644524615979352183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10672466192699487972469577 8004349644524615979352183)
            ·
              refine ⟨12006524466786923969028275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8004349644524615979352183 12006524466786923969028275)
              ·
                refine ⟨18009786700180385953542413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12006524466786923969028275 18009786700180385953542413)
                ·
                  refine ⟨6753670012567644732578405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18009786700180385953542413 6753670012567644732578405)
                  ·
                    refine ⟨1266313127356433387358451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6753670012567644732578405 1266313127356433387358451)
                    ·
                      rfl

theorem cell22_3699204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_3699204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699204 prefixEnd_3699204 := by exact prefixLift 3699204
  have htrace : WordTrace (prefixWord ++ tailWord_3699204) baseStart_3699204 baseEnd_3699204 := by
    simpa [prefixWord, tailWord_3699204, baseEnd_3699204] using wordTrace_append hprefix tailTrace_3699204
  have hstable : (prefixWord ++ tailWord_3699204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699204).length < 2 ^ (prefixWord ++ tailWord_3699204).sum := by decide
  have hdescent : baseEnd_3699204 < baseStart_3699204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699217 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 4, 3]
def baseStart_3699217 : Nat := 118140960795 + 3699217 * 2 ^ 59
def prefixEnd_3699217 : Nat := 4983230072969 + 3 ^ 40 * 3699217 * 2
def baseEnd_3699217 : Nat := 1266317577522105686783411

theorem tailTrace_3699217 : CollatzResearch.WordTrace tailWord_3699217 prefixEnd_3699217 1266317577522105686783411 := by
  unfold tailWord_3699217
  simp only [CollatzResearch.WordTrace]
  refine ⟨134921528239376059810455905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89947685492917373206970603 134921528239376059810455905)
  ·
    refine ⟨101191146179532044857841929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134921528239376059810455905 101191146179532044857841929)
    ·
      refine ⟨75893359634649033643381447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101191146179532044857841929 75893359634649033643381447)
      ·
        refine ⟨113840039451973550465072171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75893359634649033643381447 113840039451973550465072171)
        ·
          refine ⟨170760059177960325697608257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113840039451973550465072171 170760059177960325697608257)
          ·
            refine ⟨128070044383470244273206193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170760059177960325697608257 128070044383470244273206193)
            ·
              refine ⟨96052533287602683204904645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128070044383470244273206193 96052533287602683204904645)
              ·
                refine ⟨18009849991425503100919621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96052533287602683204904645 18009849991425503100919621)
                ·
                  refine ⟨3376846873392281831422429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18009849991425503100919621 3376846873392281831422429)
                  ·
                    refine ⟨1266317577522105686783411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3376846873392281831422429 1266317577522105686783411)
                    ·
                      rfl

theorem cell22_3699217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_3699217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699217 prefixEnd_3699217 := by exact prefixLift 3699217
  have htrace : WordTrace (prefixWord ++ tailWord_3699217) baseStart_3699217 baseEnd_3699217 := by
    simpa [prefixWord, tailWord_3699217, baseEnd_3699217] using wordTrace_append hprefix tailTrace_3699217
  have hstable : (prefixWord ++ tailWord_3699217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699217).length < 2 ^ (prefixWord ++ tailWord_3699217).sum := by decide
  have hdescent : baseEnd_3699217 < baseStart_3699217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699296 : List Nat := [2, 1, 1, 3, 2, 1, 4, 4, 1, 3]
def baseStart_3699296 : Nat := 118140960795 + 3699296 * 2 ^ 59
def prefixEnd_3699296 : Nat := 4983230072969 + 3 ^ 40 * 3699296 * 2
def baseEnd_3699296 : Nat := 1266344620836575814058169

theorem tailTrace_3699296 : CollatzResearch.WordTrace tailWord_3699296 prefixEnd_3699296 1266344620836575814058169 := by
  unfold tailWord_3699296
  simp only [CollatzResearch.WordTrace]
  refine ⟨67462204803044928151290871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89949606404059904201721161 67462204803044928151290871)
  ·
    refine ⟨101193307204567392226936307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67462204803044928151290871 101193307204567392226936307)
    ·
      refine ⟨151789960806851088340404461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101193307204567392226936307 151789960806851088340404461)
      ·
        refine ⟨56921235302569158127651673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151789960806851088340404461 56921235302569158127651673)
        ·
          refine ⟨42690926476926868595738755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56921235302569158127651673 42690926476926868595738755)
          ·
            refine ⟨64036389715390302893608133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42690926476926868595738755 64036389715390302893608133)
            ·
              refine ⟨12006823071635681792551525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64036389715390302893608133 12006823071635681792551525)
              ·
                refine ⟨2251279325931690336103411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12006823071635681792551525 2251279325931690336103411)
                ·
                  refine ⟨3376918988897535504155117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251279325931690336103411 3376918988897535504155117)
                  ·
                    refine ⟨1266344620836575814058169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3376918988897535504155117 1266344620836575814058169)
                    ·
                      rfl

theorem cell22_3699296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 1, 3].length) (baseStart_3699296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699296 prefixEnd_3699296 := by exact prefixLift 3699296
  have htrace : WordTrace (prefixWord ++ tailWord_3699296) baseStart_3699296 baseEnd_3699296 := by
    simpa [prefixWord, tailWord_3699296, baseEnd_3699296] using wordTrace_append hprefix tailTrace_3699296
  have hstable : (prefixWord ++ tailWord_3699296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699296).length < 2 ^ (prefixWord ++ tailWord_3699296).sum := by decide
  have hdescent : baseEnd_3699296 < baseStart_3699296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699322 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_3699322 : Nat := 118140960795 + 3699322 * 2 ^ 59
def prefixEnd_3699322 : Nat := 4983230072969 + 3 ^ 40 * 3699322 * 2
def baseEnd_3699322 : Nat := 1266353521167920412908089

theorem tailTrace_3699322 : CollatzResearch.WordTrace tailWord_3699322 prefixEnd_3699322 1266353521167920412908089 := by
  unfold tailWord_3699322
  simp only [CollatzResearch.WordTrace]
  refine ⟨33731339475998915685757055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89950238602663775162018813 33731339475998915685757055)
  ·
    refine ⟨50597009213998373528635583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33731339475998915685757055 50597009213998373528635583)
    ·
      refine ⟨75895513820997560292953375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50597009213998373528635583 75895513820997560292953375)
      ·
        refine ⟨113843270731496340439430063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75895513820997560292953375 113843270731496340439430063)
        ·
          refine ⟨170764906097244510659145095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113843270731496340439430063 170764906097244510659145095)
          ·
            refine ⟨256147359145866765988717643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170764906097244510659145095 256147359145866765988717643)
            ·
              refine ⟨384221038718800148983076465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256147359145866765988717643 384221038718800148983076465)
              ·
                refine ⟨288165779039100111737307349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384221038718800148983076465 288165779039100111737307349)
                ·
                  refine ⟨6753885446228908868843141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 288165779039100111737307349 6753885446228908868843141)
                  ·
                    refine ⟨1266353521167920412908089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6753885446228908868843141 1266353521167920412908089)
                    ·
                      rfl

theorem cell22_3699322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_3699322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699322 prefixEnd_3699322 := by exact prefixLift 3699322
  have htrace : WordTrace (prefixWord ++ tailWord_3699322) baseStart_3699322 baseEnd_3699322 := by
    simpa [prefixWord, tailWord_3699322, baseEnd_3699322] using wordTrace_append hprefix tailTrace_3699322
  have hstable : (prefixWord ++ tailWord_3699322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699322).length < 2 ^ (prefixWord ++ tailWord_3699322).sum := by decide
  have hdescent : baseEnd_3699322 < baseStart_3699322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699373 : List Nat := [1, 5, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_3699373 : Nat := 118140960795 + 3699373 * 2 ^ 59
def prefixEnd_3699373 : Nat := 4983230072969 + 3 ^ 40 * 3699373 * 2
def baseEnd_3699373 : Nat := 1266370979510173279882933

theorem tailTrace_3699373 : CollatzResearch.WordTrace tailWord_3699373 prefixEnd_3699373 1266370979510173279882933 := by
  unfold tailWord_3699373
  simp only [CollatzResearch.WordTrace]
  refine ⟨134927218026810898453134773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89951478684540598968756515 134927218026810898453134773)
  ·
    refine ⟨12649426690013521729981385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134927218026810898453134773 12649426690013521729981385)
    ·
      refine ⟨9487070017510141297486039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12649426690013521729981385 9487070017510141297486039)
      ·
        refine ⟨14230605026265211946229059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9487070017510141297486039 14230605026265211946229059)
        ·
          refine ⟨21345907539397817919343589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14230605026265211946229059 21345907539397817919343589)
          ·
            refine ⟨4002357663637090859876923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21345907539397817919343589 4002357663637090859876923)
            ·
              refine ⟨6003536495455636289815385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4002357663637090859876923 6003536495455636289815385)
              ·
                refine ⟨4502652371591727217361539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6003536495455636289815385 4502652371591727217361539)
                ·
                  refine ⟨6753978557387590826042309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4502652371591727217361539 6753978557387590826042309)
                  ·
                    refine ⟨1266370979510173279882933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6753978557387590826042309 1266370979510173279882933)
                    ·
                      rfl

theorem cell22_3699373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_3699373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699373 prefixEnd_3699373 := by exact prefixLift 3699373
  have htrace : WordTrace (prefixWord ++ tailWord_3699373) baseStart_3699373 baseEnd_3699373 := by
    simpa [prefixWord, tailWord_3699373, baseEnd_3699373] using wordTrace_append hprefix tailTrace_3699373
  have hstable : (prefixWord ++ tailWord_3699373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699373).length < 2 ^ (prefixWord ++ tailWord_3699373).sum := by decide
  have hdescent : baseEnd_3699373 < baseStart_3699373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699405 : List Nat := [1, 6, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3699405 : Nat := 118140960795 + 3699405 * 2 ^ 59
def prefixEnd_3699405 : Nat := 4983230072969 + 3 ^ 40 * 3699405 * 2
def baseEnd_3699405 : Nat := 422127311254711954360945

theorem tailTrace_3699405 : CollatzResearch.WordTrace tailWord_3699405 prefixEnd_3699405 422127311254711954360945 := by
  unfold tailWord_3699405
  simp only [CollatzResearch.WordTrace]
  refine ⟨134928385162694967918299669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89952256775129978612199779 134928385162694967918299669)
  ·
    refine ⟨6324768054501326621170297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134928385162694967918299669 6324768054501326621170297)
    ·
      refine ⟨4743576040875994965877723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6324768054501326621170297 4743576040875994965877723)
      ·
        refine ⟨7115364061313992448816585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4743576040875994965877723 7115364061313992448816585)
        ·
          refine ⟨5336523045985494336612439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7115364061313992448816585 5336523045985494336612439)
          ·
            refine ⟨8004784568978241504918659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5336523045985494336612439 8004784568978241504918659)
            ·
              refine ⟨12007176853467362257377989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8004784568978241504918659 12007176853467362257377989)
              ·
                refine ⟨2251345660025130423258373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12007176853467362257377989 2251345660025130423258373)
                ·
                  refine ⟨422127311254711954360945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2251345660025130423258373 422127311254711954360945)
                  ·
                    rfl

theorem cell22_3699405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3699405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699405 prefixEnd_3699405 := by exact prefixLift 3699405
  have htrace : WordTrace (prefixWord ++ tailWord_3699405) baseStart_3699405 baseEnd_3699405 := by
    simpa [prefixWord, tailWord_3699405, baseEnd_3699405] using wordTrace_append hprefix tailTrace_3699405
  have hstable : (prefixWord ++ tailWord_3699405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699405).length < 2 ^ (prefixWord ++ tailWord_3699405).sum := by decide
  have hdescent : baseEnd_3699405 < baseStart_3699405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699448 : List Nat := [2, 1, 2, 1, 1, 2, 6, 3, 1, 3]
def baseStart_3699448 : Nat := 118140960795 + 3699448 * 2 ^ 59
def prefixEnd_3699448 : Nat := 4983230072969 + 3 ^ 40 * 3699448 * 2
def baseEnd_3699448 : Nat := 1266396653542898084257703

theorem tailTrace_3699448 : CollatzResearch.WordTrace tailWord_3699448 prefixEnd_3699448 1266396653542898084257703 := by
  unfold tailWord_3699448
  simp only [CollatzResearch.WordTrace]
  refine ⟨67464976750769593131057499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89953302334359457508076665 67464976750769593131057499)
  ·
    refine ⟨101197465126154389696586249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67464976750769593131057499 101197465126154389696586249)
    ·
      refine ⟨75898098844615792272439687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101197465126154389696586249 75898098844615792272439687)
      ·
        refine ⟨113847148266923688408659531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75898098844615792272439687 113847148266923688408659531)
        ·
          refine ⟨170770722400385532612989297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113847148266923688408659531 170770722400385532612989297)
          ·
            refine ⟨128078041800289149459741973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170770722400385532612989297 128078041800289149459741973)
            ·
              refine ⟨6003658209388553880925405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128078041800289149459741973 6003658209388553880925405)
              ·
                refine ⟨2251371828520707705347027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6003658209388553880925405 2251371828520707705347027)
                ·
                  refine ⟨3377057742781061558020541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251371828520707705347027 3377057742781061558020541)
                  ·
                    refine ⟨1266396653542898084257703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3377057742781061558020541 1266396653542898084257703)
                    ·
                      rfl

theorem cell22_3699448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_3699448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699448 prefixEnd_3699448 := by exact prefixLift 3699448
  have htrace : WordTrace (prefixWord ++ tailWord_3699448) baseStart_3699448 baseEnd_3699448 := by
    simpa [prefixWord, tailWord_3699448, baseEnd_3699448] using wordTrace_append hprefix tailTrace_3699448
  have hstable : (prefixWord ++ tailWord_3699448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699448).length < 2 ^ (prefixWord ++ tailWord_3699448).sum := by decide
  have hdescent : baseEnd_3699448 < baseStart_3699448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699489 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 6]
def baseStart_3699489 : Nat := 118140960795 + 3699489 * 2 ^ 59
def prefixEnd_3699489 : Nat := 4983230072969 + 3 ^ 40 * 3699489 * 2
def baseEnd_3699489 : Nat := 422136896226929214660859

theorem tailTrace_3699489 : CollatzResearch.WordTrace tailWord_3699489 prefixEnd_3699489 422136896226929214660859 := by
  unfold tailWord_3699489
  simp only [CollatzResearch.WordTrace]
  refine ⟨134931448894390650264357521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89954299262927100176238347 134931448894390650264357521)
  ·
    refine ⟨101198586670792987698268141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134931448894390650264357521 101198586670792987698268141)
    ·
      refine ⟨37949470001547370386850553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101198586670792987698268141 37949470001547370386850553)
      ·
        refine ⟨28462102501160527790137915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37949470001547370386850553 28462102501160527790137915)
        ·
          refine ⟨42693153751740791685206873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28462102501160527790137915 42693153751740791685206873)
          ·
            refine ⟨32019865313805593763905155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42693153751740791685206873 32019865313805593763905155)
            ·
              refine ⟨48029797970708390645857733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32019865313805593763905155 48029797970708390645857733)
              ·
                refine ⟨9005587119507823246098325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48029797970708390645857733 9005587119507823246098325)
                ·
                  refine ⟨422136896226929214660859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9005587119507823246098325 422136896226929214660859)
                  ·
                    rfl

theorem cell22_3699489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 6].length) (baseStart_3699489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699489 prefixEnd_3699489 := by exact prefixLift 3699489
  have htrace : WordTrace (prefixWord ++ tailWord_3699489) baseStart_3699489 baseEnd_3699489 := by
    simpa [prefixWord, tailWord_3699489, baseEnd_3699489] using wordTrace_append hprefix tailTrace_3699489
  have hstable : (prefixWord ++ tailWord_3699489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699489).length < 2 ^ (prefixWord ++ tailWord_3699489).sum := by decide
  have hdescent : baseEnd_3699489 < baseStart_3699489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699504 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 1, 5]
def baseStart_3699504 : Nat := 118140960795 + 3699504 * 2 ^ 59
def prefixEnd_3699504 : Nat := 4983230072969 + 3 ^ 40 * 3699504 * 2
def baseEnd_3699504 : Nat := 1266415823487332604857531

theorem tailTrace_3699504 : CollatzResearch.WordTrace tailWord_3699504 prefixEnd_3699504 1266415823487332604857531 := by
  unfold tailWord_3699504
  simp only [CollatzResearch.WordTrace]
  refine ⟨67465997994668153913076783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89954663992890871884102377 67465997994668153913076783)
  ·
    refine ⟨101198996992002230869615175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67465997994668153913076783 101198996992002230869615175)
    ·
      refine ⟨151798495488003346304422763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101198996992002230869615175 151798495488003346304422763)
      ·
        refine ⟨227697743232005019456634145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151798495488003346304422763 227697743232005019456634145)
        ·
          refine ⟨170773307424003764592475609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227697743232005019456634145 170773307424003764592475609)
          ·
            refine ⟨128079980568002823444356707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170773307424003764592475609 128079980568002823444356707)
            ·
              refine ⟨192119970852004235166535061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128079980568002823444356707 192119970852004235166535061)
              ·
                refine ⟨9005623633687698523431331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 192119970852004235166535061 9005623633687698523431331)
                ·
                  refine ⟨13508435450531547785146997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9005623633687698523431331 13508435450531547785146997)
                  ·
                    refine ⟨1266415823487332604857531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13508435450531547785146997 1266415823487332604857531)
                    ·
                      rfl

theorem cell22_3699504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_3699504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699504 prefixEnd_3699504 := by exact prefixLift 3699504
  have htrace : WordTrace (prefixWord ++ tailWord_3699504) baseStart_3699504 baseEnd_3699504 := by
    simpa [prefixWord, tailWord_3699504, baseEnd_3699504] using wordTrace_append hprefix tailTrace_3699504
  have hstable : (prefixWord ++ tailWord_3699504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699504).length < 2 ^ (prefixWord ++ tailWord_3699504).sum := by decide
  have hdescent : baseEnd_3699504 < baseStart_3699504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699523 : List Nat := [1, 1, 1, 3, 1, 4, 5, 2, 4]
def baseStart_3699523 : Nat := 118140960795 + 3699523 * 2 ^ 59
def prefixEnd_3699523 : Nat := 4983230072969 + 3 ^ 40 * 3699523 * 2
def baseEnd_3699523 : Nat := 422140775858540962877491

theorem tailTrace_3699523 : CollatzResearch.WordTrace tailWord_3699523 prefixEnd_3699523 422140775858540962877491 := by
  unfold tailWord_3699523
  simp only [CollatzResearch.WordTrace]
  refine ⟨134932688976267474071095223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89955125984178316047396815 134932688976267474071095223)
  ·
    refine ⟨202399033464401211106642835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134932688976267474071095223 202399033464401211106642835)
    ·
      refine ⟨303598550196601816659964253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202399033464401211106642835 303598550196601816659964253)
      ·
        refine ⟨113849456323725681247486595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303598550196601816659964253 113849456323725681247486595)
        ·
          refine ⟨170774184485588521871229893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113849456323725681247486595 170774184485588521871229893)
          ·
            refine ⟨32020159591047847850855605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170774184485588521871229893 32020159591047847850855605)
            ·
              refine ⟨3001889961660735736017713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32020159591047847850855605 3001889961660735736017713)
              ·
                refine ⟨2251417471245551802013285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3001889961660735736017713 2251417471245551802013285)
                ·
                  refine ⟨422140775858540962877491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2251417471245551802013285 422140775858540962877491)
                  ·
                    rfl

theorem cell22_3699523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 4].length) (baseStart_3699523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699523 prefixEnd_3699523 := by exact prefixLift 3699523
  have htrace : WordTrace (prefixWord ++ tailWord_3699523) baseStart_3699523 baseEnd_3699523 := by
    simpa [prefixWord, tailWord_3699523, baseEnd_3699523] using wordTrace_append hprefix tailTrace_3699523
  have hstable : (prefixWord ++ tailWord_3699523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699523).length < 2 ^ (prefixWord ++ tailWord_3699523).sum := by decide
  have hdescent : baseEnd_3699523 < baseStart_3699523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699538 : List Nat := [3, 2, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_3699538 : Nat := 118140960795 + 3699538 * 2 ^ 59
def prefixEnd_3699538 : Nat := 4983230072969 + 3 ^ 40 * 3699538 * 2
def baseEnd_3699538 : Nat := 1266427462382167849507427

theorem tailTrace_3699538 : CollatzResearch.WordTrace tailWord_3699538 prefixEnd_3699538 1266427462382167849507427 := by
  unfold tailWord_3699538
  simp only [CollatzResearch.WordTrace]
  refine ⟨33733309017803282908222817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89955490714142087755260845 33733309017803282908222817)
  ·
    refine ⟨25299981763352462181167113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33733309017803282908222817 25299981763352462181167113)
    ·
      refine ⟨18974986322514346635875335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25299981763352462181167113 18974986322514346635875335)
      ·
        refine ⟨28462479483771519953813003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18974986322514346635875335 28462479483771519953813003)
        ·
          refine ⟨42693719225657279930719505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28462479483771519953813003 42693719225657279930719505)
          ·
            refine ⟨32020289419242959948039629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42693719225657279930719505 32020289419242959948039629)
            ·
              refine ⟨12007608532216109980514861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32020289419242959948039629 12007608532216109980514861)
              ·
                refine ⟨4502853199581041242693073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12007608532216109980514861 4502853199581041242693073)
                ·
                  refine ⟨3377139899685780932019805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4502853199581041242693073 3377139899685780932019805)
                  ·
                    refine ⟨1266427462382167849507427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3377139899685780932019805 1266427462382167849507427)
                    ·
                      rfl

theorem cell22_3699538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_3699538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699538 prefixEnd_3699538 := by exact prefixLift 3699538
  have htrace : WordTrace (prefixWord ++ tailWord_3699538) baseStart_3699538 baseEnd_3699538 := by
    simpa [prefixWord, tailWord_3699538, baseEnd_3699538] using wordTrace_append hprefix tailTrace_3699538
  have hstable : (prefixWord ++ tailWord_3699538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699538).length < 2 ^ (prefixWord ++ tailWord_3699538).sum := by decide
  have hdescent : baseEnd_3699538 < baseStart_3699538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699579 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 7]
def baseStart_3699579 : Nat := 118140960795 + 3699579 * 2 ^ 59
def prefixEnd_3699579 : Nat := 4983230072969 + 3 ^ 40 * 3699579 * 2
def baseEnd_3699579 : Nat := 422147165840019136410767

theorem tailTrace_3699579 : CollatzResearch.WordTrace tailWord_3699579 prefixEnd_3699579 422147165840019136410767 := by
  unfold tailWord_3699579
  simp only [CollatzResearch.WordTrace]
  refine ⟨134934731464064595635133791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89956487642709730423422527 134934731464064595635133791)
  ·
    refine ⟨202402097196096893452700687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134934731464064595635133791 202402097196096893452700687)
    ·
      refine ⟨303603145794145340179051031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202402097196096893452700687 303603145794145340179051031)
      ·
        refine ⟨455404718691218010268576547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303603145794145340179051031 455404718691218010268576547)
        ·
          refine ⟨683107078036827015402864821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455404718691218010268576547 683107078036827015402864821)
          ·
            refine ⟨64041288565952532694018577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 683107078036827015402864821 64041288565952532694018577)
            ·
              refine ⟨48030966424464399520513933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64041288565952532694018577 48030966424464399520513933)
              ·
                refine ⟨18011612409174149820192725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48030966424464399520513933 18011612409174149820192725)
                ·
                  refine ⟨422147165840019136410767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18011612409174149820192725 422147165840019136410767)
                  ·
                    rfl

theorem cell22_3699579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 7].length) (baseStart_3699579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699579 prefixEnd_3699579 := by exact prefixLift 3699579
  have htrace : WordTrace (prefixWord ++ tailWord_3699579) baseStart_3699579 baseEnd_3699579 := by
    simpa [prefixWord, tailWord_3699579, baseEnd_3699579] using wordTrace_append hprefix tailTrace_3699579
  have hstable : (prefixWord ++ tailWord_3699579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699579).length < 2 ^ (prefixWord ++ tailWord_3699579).sum := by decide
  have hdescent : baseEnd_3699579 < baseStart_3699579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699596 : List Nat := [2, 2, 1, 2, 1, 2, 4, 3, 5]
def baseStart_3699596 : Nat := 118140960795 + 3699596 * 2 ^ 59
def prefixEnd_3699596 : Nat := 4983230072969 + 3 ^ 40 * 3699596 * 2
def baseEnd_3699596 : Nat := 422149105655825010519083

theorem tailTrace_3699596 : CollatzResearch.WordTrace tailWord_3699596 prefixEnd_3699596 422149105655825010519083 := by
  unfold tailWord_3699596
  simp only [CollatzResearch.WordTrace]
  refine ⟨67467675752501503769251321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89956901003335338359001761 67467675752501503769251321)
  ·
    refine ⟨50600756814376127826938491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67467675752501503769251321 50600756814376127826938491)
    ·
      refine ⟨75901135221564191740407737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50600756814376127826938491 75901135221564191740407737)
      ·
        refine ⟨56925851416173143805305803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75901135221564191740407737 56925851416173143805305803)
        ·
          refine ⟨85388777124259715707958705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56925851416173143805305803 85388777124259715707958705)
          ·
            refine ⟨64041582843194786780969029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85388777124259715707958705 64041582843194786780969029)
            ·
              refine ⟨12007796783099022521431693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64041582843194786780969029 12007796783099022521431693)
              ·
                refine ⟨4502923793662133445536885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12007796783099022521431693 4502923793662133445536885)
                ·
                  refine ⟨422149105655825010519083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4502923793662133445536885 422149105655825010519083)
                  ·
                    rfl

theorem cell22_3699596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_3699596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699596 prefixEnd_3699596 := by exact prefixLift 3699596
  have htrace : WordTrace (prefixWord ++ tailWord_3699596) baseStart_3699596 baseEnd_3699596 := by
    simpa [prefixWord, tailWord_3699596, baseEnd_3699596] using wordTrace_append hprefix tailTrace_3699596
  have hstable : (prefixWord ++ tailWord_3699596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699596).length < 2 ^ (prefixWord ++ tailWord_3699596).sum := by decide
  have hdescent : baseEnd_3699596 < baseStart_3699596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699617 : List Nat := [1, 2, 3, 4, 1, 2, 2, 3, 1, 3]
def baseStart_3699617 : Nat := 118140960795 + 3699617 * 2 ^ 59
def prefixEnd_3699617 : Nat := 4983230072969 + 3 ^ 40 * 3699617 * 2
def baseEnd_3699617 : Nat := 1266454505696637976782185

theorem tailTrace_3699617 : CollatzResearch.WordTrace tailWord_3699617 prefixEnd_3699617 1266454505696637976782185 := by
  unfold tailWord_3699617
  simp only [CollatzResearch.WordTrace]
  refine ⟨134936117437926928125017105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89957411625284618750011403 134936117437926928125017105)
  ·
    refine ⟨101202088078445196093762829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134936117437926928125017105 101202088078445196093762829)
    ·
      refine ⟨37950783029416948535161061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101202088078445196093762829 37950783029416948535161061)
      ·
        refine ⟨7115771818015677850342699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37950783029416948535161061 7115771818015677850342699)
        ·
          refine ⟨10673657727023516775514049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7115771818015677850342699 10673657727023516775514049)
          ·
            refine ⟨8005243295267637581635537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10673657727023516775514049 8005243295267637581635537)
            ·
              refine ⟨6003932471450728186226653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8005243295267637581635537 6003932471450728186226653)
              ·
                refine ⟨2251474676794023069834995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6003932471450728186226653 2251474676794023069834995)
                ·
                  refine ⟨3377212015191034604752493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251474676794023069834995 3377212015191034604752493)
                  ·
                    refine ⟨1266454505696637976782185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3377212015191034604752493 1266454505696637976782185)
                    ·
                      rfl

theorem cell22_3699617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_3699617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699617 prefixEnd_3699617 := by exact prefixLift 3699617
  have htrace : WordTrace (prefixWord ++ tailWord_3699617) baseStart_3699617 baseEnd_3699617 := by
    simpa [prefixWord, tailWord_3699617, baseEnd_3699617] using wordTrace_append hprefix tailTrace_3699617
  have hstable : (prefixWord ++ tailWord_3699617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699617).length < 2 ^ (prefixWord ++ tailWord_3699617).sum := by decide
  have hdescent : baseEnd_3699617 < baseStart_3699617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699641 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 6]
def baseStart_3699641 : Nat := 118140960795 + 3699641 * 2 ^ 59
def prefixEnd_3699641 : Nat := 4983230072969 + 3 ^ 40 * 3699641 * 2
def baseEnd_3699641 : Nat := 422154240462369971394037

theorem tailTrace_3699641 : CollatzResearch.WordTrace tailWord_3699641 prefixEnd_3699641 422154240462369971394037 := by
  unfold tailWord_3699641
  simp only [CollatzResearch.WordTrace]
  refine ⟨134936992789839980223890777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89957995193226653482593851 134936992789839980223890777)
  ·
    refine ⟨101202744592379985167918083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134936992789839980223890777 101202744592379985167918083)
    ·
      refine ⟨151804116888569977751877125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101202744592379985167918083 151804116888569977751877125)
      ·
        refine ⟨28463271916606870828476961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151804116888569977751877125 28463271916606870828476961)
        ·
          refine ⟨21347453937455153121357721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28463271916606870828476961 21347453937455153121357721)
          ·
            refine ⟨16010590453091364841018291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21347453937455153121357721 16010590453091364841018291)
            ·
              refine ⟨24015885679637047261527437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16010590453091364841018291 24015885679637047261527437)
              ·
                refine ⟨9005957129863892723072789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24015885679637047261527437 9005957129863892723072789)
                ·
                  refine ⟨422154240462369971394037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9005957129863892723072789 422154240462369971394037)
                  ·
                    rfl

theorem cell22_3699641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 6].length) (baseStart_3699641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699641 prefixEnd_3699641 := by exact prefixLift 3699641
  have htrace : WordTrace (prefixWord ++ tailWord_3699641) baseStart_3699641 baseEnd_3699641 := by
    simpa [prefixWord, tailWord_3699641, baseEnd_3699641] using wordTrace_append hprefix tailTrace_3699641
  have hstable : (prefixWord ++ tailWord_3699641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699641).length < 2 ^ (prefixWord ++ tailWord_3699641).sum := by decide
  have hdescent : baseEnd_3699641 < baseStart_3699641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699673 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 4, 3]
def baseStart_3699673 : Nat := 118140960795 + 3699673 * 2 ^ 59
def prefixEnd_3699673 : Nat := 4983230072969 + 3 ^ 40 * 3699673 * 2
def baseEnd_3699673 : Nat := 1266473675641072497382013

theorem tailTrace_3699673 : CollatzResearch.WordTrace tailWord_3699673 prefixEnd_3699673 1266473675641072497382013 := by
  unfold tailWord_3699673
  simp only [CollatzResearch.WordTrace]
  refine ⟨134938159925724049689055673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89958773283816033126037115 134938159925724049689055673)
  ·
    refine ⟨101203619944293037266791755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134938159925724049689055673 101203619944293037266791755)
    ·
      refine ⟨151805429916439555900187633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101203619944293037266791755 151805429916439555900187633)
      ·
        refine ⟨113854072437329666925140725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151805429916439555900187633 113854072437329666925140725)
        ·
          refine ⟨10673819290999656274231943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113854072437329666925140725 10673819290999656274231943)
          ·
            refine ⟨16010728936499484411347915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10673819290999656274231943 16010728936499484411347915)
            ·
              refine ⟨24016093404749226617021873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16010728936499484411347915 24016093404749226617021873)
              ·
                refine ⟨18012070053561919962766405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24016093404749226617021873 18012070053561919962766405)
                ·
                  refine ⟨3377263135042859993018701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18012070053561919962766405 3377263135042859993018701)
                  ·
                    refine ⟨1266473675641072497382013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3377263135042859993018701 1266473675641072497382013)
                    ·
                      rfl

theorem cell22_3699673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 3].length) (baseStart_3699673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699673 prefixEnd_3699673 := by exact prefixLift 3699673
  have htrace : WordTrace (prefixWord ++ tailWord_3699673) baseStart_3699673 baseEnd_3699673 := by
    simpa [prefixWord, tailWord_3699673, baseEnd_3699673] using wordTrace_append hprefix tailTrace_3699673
  have hstable : (prefixWord ++ tailWord_3699673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699673).length < 2 ^ (prefixWord ++ tailWord_3699673).sum := by decide
  have hdescent : baseEnd_3699673 < baseStart_3699673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699810 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 6]
def baseStart_3699810 : Nat := 118140960795 + 3699810 * 2 ^ 59
def prefixEnd_3699810 : Nat := 4983230072969 + 3 ^ 40 * 3699810 * 2
def baseEnd_3699810 : Nat := 422173524513616602235531

theorem tailTrace_3699810 : CollatzResearch.WordTrace tailWord_3699810 prefixEnd_3699810 422173524513616602235531 := by
  unfold tailWord_3699810
  simp only [CollatzResearch.WordTrace]
  refine ⟨33735789181556930521698221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89962104484151814724528589 33735789181556930521698221)
  ·
    refine ⟨12650920943083848945636833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33735789181556930521698221 12650920943083848945636833)
    ·
      refine ⟨9488190707312886709227625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12650920943083848945636833 9488190707312886709227625)
      ·
        refine ⟨7116143030484665031920719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9488190707312886709227625 7116143030484665031920719)
        ·
          refine ⟨10674214545726997547881079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7116143030484665031920719 10674214545726997547881079)
          ·
            refine ⟨16011321818590496321821619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10674214545726997547881079 16011321818590496321821619)
            ·
              refine ⟨24016982727885744482732429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16011321818590496321821619 24016982727885744482732429)
              ·
                refine ⟨9006368522957154181024661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24016982727885744482732429 9006368522957154181024661)
                ·
                  refine ⟨422173524513616602235531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9006368522957154181024661 422173524513616602235531)
                  ·
                    rfl

theorem cell22_3699810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_3699810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699810 prefixEnd_3699810 := by exact prefixLift 3699810
  have htrace : WordTrace (prefixWord ++ tailWord_3699810) baseStart_3699810 baseEnd_3699810 := by
    simpa [prefixWord, tailWord_3699810, baseEnd_3699810] using wordTrace_append hprefix tailTrace_3699810
  have hstable : (prefixWord ++ tailWord_3699810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699810).length < 2 ^ (prefixWord ++ tailWord_3699810).sum := by decide
  have hdescent : baseEnd_3699810 < baseStart_3699810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699829 : List Nat := [1, 3, 4, 3, 1, 1, 2, 2, 1, 4]
def baseStart_3699829 : Nat := 118140960795 + 3699829 * 2 ^ 59
def prefixEnd_3699829 : Nat := 4983230072969 + 3 ^ 40 * 3699829 * 2
def baseEnd_3699829 : Nat := 1266527077629140090481535

theorem tailTrace_3699829 : CollatzResearch.WordTrace tailWord_3699829 prefixEnd_3699829 1266527077629140090481535 := by
  unfold tailWord_3699829
  simp only [CollatzResearch.WordTrace]
  refine ⟨134943849713158888331734541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89962566475439258887823027 134943849713158888331734541)
  ·
    refine ⟨50603943642434583124400453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134943849713158888331734541 50603943642434583124400453)
    ·
      refine ⟨9488239432956484335825085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50603943642434583124400453 9488239432956484335825085)
      ·
        refine ⟨3558089787358681625934407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9488239432956484335825085 3558089787358681625934407)
        ·
          refine ⟨5337134681038022438901611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3558089787358681625934407 5337134681038022438901611)
          ·
            refine ⟨8005702021557033658352417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5337134681038022438901611 8005702021557033658352417)
            ·
              refine ⟨6004276516167775243764313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8005702021557033658352417 6004276516167775243764313)
              ·
                refine ⟨4503207387125831432823235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6004276516167775243764313 4503207387125831432823235)
                ·
                  refine ⟨6754811080688747149234853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4503207387125831432823235 6754811080688747149234853)
                  ·
                    refine ⟨1266527077629140090481535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6754811080688747149234853 1266527077629140090481535)
                    ·
                      rfl

theorem cell22_3699829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_3699829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699829 prefixEnd_3699829 := by exact prefixLift 3699829
  have htrace : WordTrace (prefixWord ++ tailWord_3699829) baseStart_3699829 baseEnd_3699829 := by
    simpa [prefixWord, tailWord_3699829, baseEnd_3699829] using wordTrace_append hprefix tailTrace_3699829
  have hstable : (prefixWord ++ tailWord_3699829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699829).length < 2 ^ (prefixWord ++ tailWord_3699829).sum := by decide
  have hdescent : baseEnd_3699829 < baseStart_3699829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699898 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_3699898 : Nat := 118140960795 + 3699898 * 2 ^ 59
def prefixEnd_3699898 : Nat := 4983230072969 + 3 ^ 40 * 3699898 * 2
def baseEnd_3699898 : Nat := 1266550697739246910506323

theorem tailTrace_3699898 : CollatzResearch.WordTrace tailWord_3699898 prefixEnd_3699898 1266550697739246910506323 := by
  unfold tailWord_3699898
  simp only [CollatzResearch.WordTrace]
  refine ⟨33736591587477228278999087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89964244233272608743997565 33736591587477228278999087)
  ·
    refine ⟨50604887381215842418498631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33736591587477228278999087 50604887381215842418498631)
    ·
      refine ⟨75907331071823763627747947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50604887381215842418498631 75907331071823763627747947)
      ·
        refine ⟨113860996607735645441621921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75907331071823763627747947 113860996607735645441621921)
        ·
          refine ⟨85395747455801734081216441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113860996607735645441621921 85395747455801734081216441)
          ·
            refine ⟨64046810591851300560912331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85395747455801734081216441 64046810591851300560912331)
            ·
              refine ⟨96070215887776950841368497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64046810591851300560912331 96070215887776950841368497)
              ·
                refine ⟨72052661915832713131026373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96070215887776950841368497 72052661915832713131026373)
                ·
                  refine ⟨13509874109218633712067445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72052661915832713131026373 13509874109218633712067445)
                  ·
                    refine ⟨1266550697739246910506323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13509874109218633712067445 1266550697739246910506323)
                    ·
                      rfl

theorem cell22_3699898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_3699898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699898 prefixEnd_3699898 := by exact prefixLift 3699898
  have htrace : WordTrace (prefixWord ++ tailWord_3699898) baseStart_3699898 baseEnd_3699898 := by
    simpa [prefixWord, tailWord_3699898, baseEnd_3699898] using wordTrace_append hprefix tailTrace_3699898
  have hstable : (prefixWord ++ tailWord_3699898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699898).length < 2 ^ (prefixWord ++ tailWord_3699898).sum := by decide
  have hdescent : baseEnd_3699898 < baseStart_3699898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699962 : List Nat := [3, 1, 1, 1, 1, 4, 4, 3, 4]
def baseStart_3699962 : Nat := 118140960795 + 3699962 * 2 ^ 59
def prefixEnd_3699962 : Nat := 4983230072969 + 3 ^ 40 * 3699962 * 2
def baseEnd_3699962 : Nat := 422190868749057358968709

theorem tailTrace_3699962 : CollatzResearch.WordTrace tailWord_3699962 prefixEnd_3699962 422190868749057358968709 := by
  unfold tailWord_3699962
  simp only [CollatzResearch.WordTrace]
  refine ⟨33737175155419263011581535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89965800414451368030884093 33737175155419263011581535)
  ·
    refine ⟨50605762733128894517372303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33737175155419263011581535 50605762733128894517372303)
    ·
      refine ⟨75908644099693341776058455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50605762733128894517372303 75908644099693341776058455)
      ·
        refine ⟨113862966149540012664087683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75908644099693341776058455 113862966149540012664087683)
        ·
          refine ⟨170794449224310018996131525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113862966149540012664087683 170794449224310018996131525)
          ·
            refine ⟨32023959229558128561774661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170794449224310018996131525 32023959229558128561774661)
            ·
              refine ⟨6004492355542149105332749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32023959229558128561774661 6004492355542149105332749)
              ·
                refine ⟨2251684633328305914499781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6004492355542149105332749 2251684633328305914499781)
                ·
                  refine ⟨422190868749057358968709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2251684633328305914499781 422190868749057358968709)
                  ·
                    rfl

theorem cell22_3699962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_3699962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699962 prefixEnd_3699962 := by exact prefixLift 3699962
  have htrace : WordTrace (prefixWord ++ tailWord_3699962) baseStart_3699962 baseEnd_3699962 := by
    simpa [prefixWord, tailWord_3699962, baseEnd_3699962] using wordTrace_append hprefix tailTrace_3699962
  have hstable : (prefixWord ++ tailWord_3699962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699962).length < 2 ^ (prefixWord ++ tailWord_3699962).sum := by decide
  have hdescent : baseEnd_3699962 < baseStart_3699962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3699973 : List Nat := [1, 3, 1, 1, 2, 1, 13]
def baseStart_3699973 : Nat := 118140960795 + 3699973 * 2 ^ 59
def prefixEnd_3699973 : Nat := 4983230072969 + 3 ^ 40 * 3699973 * 2
def baseEnd_3699973 : Nat := 46910235991554507958559

theorem tailTrace_3699973 : CollatzResearch.WordTrace tailWord_3699973 prefixEnd_3699973 46910235991554507958559 := by
  unfold tailWord_3699973
  simp only [CollatzResearch.WordTrace]
  refine ⟨134949101824637200924976573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89966067883091467283317715 134949101824637200924976573)
  ·
    refine ⟨50605913184238950346866215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134949101824637200924976573 50605913184238950346866215)
    ·
      refine ⟨75908869776358425520299323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50605913184238950346866215 75908869776358425520299323)
      ·
        refine ⟨113863304664537638280448985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75908869776358425520299323 113863304664537638280448985)
        ·
          refine ⟨85397478498403228710336739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113863304664537638280448985 85397478498403228710336739)
          ·
            refine ⟨128096217747604843065505109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85397478498403228710336739 128096217747604843065505109)
            ·
              refine ⟨46910235991554507958559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 128096217747604843065505109 46910235991554507958559)
              ·
                rfl

theorem cell22_3699973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 13].length) (baseStart_3699973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3699973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3699973 prefixEnd_3699973 := by exact prefixLift 3699973
  have htrace : WordTrace (prefixWord ++ tailWord_3699973) baseStart_3699973 baseEnd_3699973 := by
    simpa [prefixWord, tailWord_3699973, baseEnd_3699973] using wordTrace_append hprefix tailTrace_3699973
  have hstable : (prefixWord ++ tailWord_3699973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3699973).length < 2 ^ (prefixWord ++ tailWord_3699973).sum := by decide
  have hdescent : baseEnd_3699973 < baseStart_3699973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3699973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700035 : List Nat := [1, 1, 1, 3, 1, 3, 1, 6, 5]
def baseStart_3700035 : Nat := 118140960795 + 3700035 * 2 ^ 59
def prefixEnd_3700035 : Nat := 4983230072969 + 3 ^ 40 * 3700035 * 2
def baseEnd_3700035 : Nat := 422199198546341406610301

theorem tailTrace_3700035 : CollatzResearch.WordTrace tailWord_3700035 prefixEnd_3700035 422199198546341406610301 := by
  unfold tailWord_3700035
  simp only [CollatzResearch.WordTrace]
  refine ⟨134951363150412585513733559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89967575433608390342489039 134951363150412585513733559)
  ·
    refine ⟨202427044725618878270600339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134951363150412585513733559 202427044725618878270600339)
    ·
      refine ⟨303640567088428317405900509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202427044725618878270600339 303640567088428317405900509)
      ·
        refine ⟨113865212658160619027212691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 303640567088428317405900509 113865212658160619027212691)
        ·
          refine ⟨170797818987240928540819037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113865212658160619027212691 170797818987240928540819037)
          ·
            refine ⟨64049182120215348202807139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170797818987240928540819037 64049182120215348202807139)
            ·
              refine ⟨96073773180323022304210709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64049182120215348202807139 96073773180323022304210709)
              ·
                refine ⟨4503458117827641670509877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96073773180323022304210709 4503458117827641670509877)
                ·
                  refine ⟨422199198546341406610301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4503458117827641670509877 422199198546341406610301)
                  ·
                    rfl

theorem cell22_3700035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 5].length) (baseStart_3700035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700035 prefixEnd_3700035 := by exact prefixLift 3700035
  have htrace : WordTrace (prefixWord ++ tailWord_3700035) baseStart_3700035 baseEnd_3700035 := by
    simpa [prefixWord, tailWord_3700035, baseEnd_3700035] using wordTrace_append hprefix tailTrace_3700035
  have hstable : (prefixWord ++ tailWord_3700035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700035).length < 2 ^ (prefixWord ++ tailWord_3700035).sum := by decide
  have hdescent : baseEnd_3700035 < baseStart_3700035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700039 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 3, 3]
def baseStart_3700039 : Nat := 118140960795 + 3700039 * 2 ^ 59
def prefixEnd_3700039 : Nat := 4983230072969 + 3 ^ 40 * 3700039 * 2
def baseEnd_3700039 : Nat := 1266598964920769542730891

theorem tailTrace_3700039 : CollatzResearch.WordTrace tailWord_3700039 prefixEnd_3700039 1266598964920769542730891 := by
  unfold tailWord_3700039
  simp only [CollatzResearch.WordTrace]
  refine ⟨134951509042398094196879171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89967672694932062797919447 134951509042398094196879171)
  ·
    refine ⟨202427263563597141295318757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134951509042398094196879171 202427263563597141295318757)
    ·
      refine ⟨37955111918174463992872267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 202427263563597141295318757 37955111918174463992872267)
      ·
        refine ⟨56932667877261695989308401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37955111918174463992872267 56932667877261695989308401)
        ·
          refine ⟨42699500907946271991981301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56932667877261695989308401 42699500907946271991981301)
          ·
            refine ⟨4003078210119962999248247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42699500907946271991981301 4003078210119962999248247)
            ·
              refine ⟨6004617315179944498872371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4003078210119962999248247 6004617315179944498872371)
              ·
                refine ⟨9006925972769916748308557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6004617315179944498872371 9006925972769916748308557)
                ·
                  refine ⟨3377597239788718780615709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9006925972769916748308557 3377597239788718780615709)
                  ·
                    refine ⟨1266598964920769542730891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3377597239788718780615709 1266598964920769542730891)
                    ·
                      rfl

theorem cell22_3700039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_3700039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700039 prefixEnd_3700039 := by exact prefixLift 3700039
  have htrace : WordTrace (prefixWord ++ tailWord_3700039) baseStart_3700039 baseEnd_3700039 := by
    simpa [prefixWord, tailWord_3700039, baseEnd_3700039] using wordTrace_append hprefix tailTrace_3700039
  have hstable : (prefixWord ++ tailWord_3700039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700039).length < 2 ^ (prefixWord ++ tailWord_3700039).sum := by decide
  have hdescent : baseEnd_3700039 < baseStart_3700039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700045 : List Nat := [1, 6, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_3700045 : Nat := 118140960795 + 3700045 * 2 ^ 59
def prefixEnd_3700045 : Nat := 4983230072969 + 3 ^ 40 * 3700045 * 2
def baseEnd_3700045 : Nat := 1266601018843387527080873

theorem tailTrace_3700045 : CollatzResearch.WordTrace tailWord_3700045 prefixEnd_3700045 1266601018843387527080873 := by
  unfold tailWord_3700045
  simp only [CollatzResearch.WordTrace]
  refine ⟨134951727880376357221597589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89967818586917571481065059 134951727880376357221597589)
  ·
    refine ⟨6325862244392641744762387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134951727880376357221597589 6325862244392641744762387)
    ·
      refine ⟨9488793366588962617143581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6325862244392641744762387 9488793366588962617143581)
      ·
        refine ⟨3558297512470860981428843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9488793366588962617143581 3558297512470860981428843)
        ·
          refine ⟨5337446268706291472143265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3558297512470860981428843 5337446268706291472143265)
          ·
            refine ⟨4003084701529718604107449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5337446268706291472143265 4003084701529718604107449)
            ·
              refine ⟨3002313526147288953080587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4003084701529718604107449 3002313526147288953080587)
              ·
                refine ⟨4503470289220933429620881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3002313526147288953080587 4503470289220933429620881)
                ·
                  refine ⟨3377602716915700072215661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4503470289220933429620881 3377602716915700072215661)
                  ·
                    refine ⟨1266601018843387527080873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3377602716915700072215661 1266601018843387527080873)
                    ·
                      rfl

theorem cell22_3700045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_3700045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700045 prefixEnd_3700045 := by exact prefixLift 3700045
  have htrace : WordTrace (prefixWord ++ tailWord_3700045) baseStart_3700045 baseEnd_3700045 := by
    simpa [prefixWord, tailWord_3700045, baseEnd_3700045] using wordTrace_append hprefix tailTrace_3700045
  have hstable : (prefixWord ++ tailWord_3700045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700045).length < 2 ^ (prefixWord ++ tailWord_3700045).sum := by decide
  have hdescent : baseEnd_3700045 < baseStart_3700045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700050 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_3700050 : Nat := 118140960795 + 3700050 * 2 ^ 59
def prefixEnd_3700050 : Nat := 4983230072969 + 3 ^ 40 * 3700050 * 2
def baseEnd_3700050 : Nat := 1266602730445569180705857

theorem tailTrace_3700050 : CollatzResearch.WordTrace tailWord_3700050 prefixEnd_3700050 1266602730445569180705857 := by
  unfold tailWord_3700050
  simp only [CollatzResearch.WordTrace]
  refine ⟨33737977561339560768882401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89967940163572162050353069 33737977561339560768882401)
  ·
    refine ⟨25303483171004670576661801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33737977561339560768882401 25303483171004670576661801)
    ·
      refine ⟨18977612378253502932496351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25303483171004670576661801 18977612378253502932496351)
      ·
        refine ⟨28466418567380254398744527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18977612378253502932496351 28466418567380254398744527)
        ·
          refine ⟨42699627851070381598116791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28466418567380254398744527 42699627851070381598116791)
          ·
            refine ⟨64049441776605572397175187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42699627851070381598116791 64049441776605572397175187)
            ·
              refine ⟨96074162664908358595762781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64049441776605572397175187 96074162664908358595762781)
              ·
                refine ⟨36027810999340634473411043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96074162664908358595762781 36027810999340634473411043)
                ·
                  refine ⟨54041716499010951710116565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36027810999340634473411043 54041716499010951710116565)
                  ·
                    refine ⟨1266602730445569180705857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54041716499010951710116565 1266602730445569180705857)
                    ·
                      rfl

theorem cell22_3700050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_3700050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700050 prefixEnd_3700050 := by exact prefixLift 3700050
  have htrace : WordTrace (prefixWord ++ tailWord_3700050) baseStart_3700050 baseEnd_3700050 := by
    simpa [prefixWord, tailWord_3700050, baseEnd_3700050] using wordTrace_append hprefix tailTrace_3700050
  have hstable : (prefixWord ++ tailWord_3700050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700050).length < 2 ^ (prefixWord ++ tailWord_3700050).sum := by decide
  have hdescent : baseEnd_3700050 < baseStart_3700050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700052 : List Nat := [2, 4, 1, 1, 2, 1, 3, 3, 5]
def baseStart_3700052 : Nat := 118140960795 + 3700052 * 2 ^ 59
def prefixEnd_3700052 : Nat := 4983230072969 + 3 ^ 40 * 3700052 * 2
def baseEnd_3700052 : Nat := 422201138362147280718617

theorem tailTrace_3700052 : CollatzResearch.WordTrace tailWord_3700052 prefixEnd_3700052 422201138362147280718617 := by
  unfold tailWord_3700052
  simp only [CollatzResearch.WordTrace]
  refine ⟨67475991595675498708551205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89967988794233998278068273 67475991595675498708551205)
  ·
    refine ⟨12651748424189156007853351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67475991595675498708551205 12651748424189156007853351)
    ·
      refine ⟨18977622636283734011780027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12651748424189156007853351 18977622636283734011780027)
      ·
        refine ⟨28466433954425601017670041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18977622636283734011780027 28466433954425601017670041)
        ·
          refine ⟨21349825465819200763252531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28466433954425601017670041 21349825465819200763252531)
          ·
            refine ⟨32024738198728801144878797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21349825465819200763252531 32024738198728801144878797)
            ·
              refine ⟨12009276824523300429329549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32024738198728801144878797 12009276824523300429329549)
              ·
                refine ⟨4503478809196237660998581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12009276824523300429329549 4503478809196237660998581)
                ·
                  refine ⟨422201138362147280718617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4503478809196237660998581 422201138362147280718617)
                  ·
                    rfl

theorem cell22_3700052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_3700052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700052 prefixEnd_3700052 := by exact prefixLift 3700052
  have htrace : WordTrace (prefixWord ++ tailWord_3700052) baseStart_3700052 baseEnd_3700052 := by
    simpa [prefixWord, tailWord_3700052, baseEnd_3700052] using wordTrace_append hprefix tailTrace_3700052
  have hstable : (prefixWord ++ tailWord_3700052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700052).length < 2 ^ (prefixWord ++ tailWord_3700052).sum := by decide
  have hdescent : baseEnd_3700052 < baseStart_3700052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700127 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 1, 6]
def baseStart_3700127 : Nat := 118140960795 + 3700127 * 2 ^ 59
def prefixEnd_3700127 : Nat := 4983230072969 + 3 ^ 40 * 3700127 * 2
def baseEnd_3700127 : Nat := 1266629089119166646530621

theorem tailTrace_3700127 : CollatzResearch.WordTrace tailWord_3700127 prefixEnd_3700127 1266629089119166646530621 := by
  unfold tailWord_3700127
  simp only [CollatzResearch.WordTrace]
  refine ⟨134954718666079285226082635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89969812444052856817388423 134954718666079285226082635)
  ·
    refine ⟨202432077999118927839123953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134954718666079285226082635 202432077999118927839123953)
    ·
      refine ⟨151824058499339195879342965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202432077999118927839123953 151824058499339195879342965)
      ·
        refine ⟨14233505484313049613688403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151824058499339195879342965 14233505484313049613688403)
        ·
          refine ⟨21350258226469574420532605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14233505484313049613688403 21350258226469574420532605)
          ·
            refine ⟨8006346834926090407699727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21350258226469574420532605 8006346834926090407699727)
            ·
              refine ⟨12009520252389135611549591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8006346834926090407699727 12009520252389135611549591)
              ·
                refine ⟨18014280378583703417324387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12009520252389135611549591 18014280378583703417324387)
                ·
                  refine ⟨27021420567875555125986581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18014280378583703417324387 27021420567875555125986581)
                  ·
                    refine ⟨1266629089119166646530621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27021420567875555125986581 1266629089119166646530621)
                    ·
                      rfl

theorem cell22_3700127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_3700127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700127 prefixEnd_3700127 := by exact prefixLift 3700127
  have htrace : WordTrace (prefixWord ++ tailWord_3700127) baseStart_3700127 baseEnd_3700127 := by
    simpa [prefixWord, tailWord_3700127, baseEnd_3700127] using wordTrace_append hprefix tailTrace_3700127
  have hstable : (prefixWord ++ tailWord_3700127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700127).length < 2 ^ (prefixWord ++ tailWord_3700127).sum := by decide
  have hdescent : baseEnd_3700127 < baseStart_3700127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700174 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_3700174 : Nat := 118140960795 + 3700174 * 2 ^ 59
def prefixEnd_3700174 : Nat := 4983230072969 + 3 ^ 40 * 3700174 * 2
def baseEnd_3700174 : Nat := 1266645178179674190605477

theorem tailTrace_3700174 : CollatzResearch.WordTrace tailWord_3700174 prefixEnd_3700174 1266645178179674190605477 := by
  unfold tailWord_3700174
  simp only [CollatzResearch.WordTrace]
  refine ⟨16869554112113626531630447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89970955264606008168695717 16869554112113626531630447)
  ·
    refine ⟨25304331168170439797445671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16869554112113626531630447 25304331168170439797445671)
    ·
      refine ⟨37956496752255659696168507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25304331168170439797445671 37956496752255659696168507)
      ·
        refine ⟨56934745128383489544252761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37956496752255659696168507 56934745128383489544252761)
        ·
          refine ⟨42701058846287617158189571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56934745128383489544252761 42701058846287617158189571)
          ·
            refine ⟨64051588269431425737284357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42701058846287617158189571 64051588269431425737284357)
            ·
              refine ⟨12009672800518392325740817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64051588269431425737284357 12009672800518392325740817)
              ·
                refine ⟨9007254600388794244305613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12009672800518392325740817 9007254600388794244305613)
                ·
                  refine ⟨3377720475145797841614605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9007254600388794244305613 3377720475145797841614605)
                  ·
                    refine ⟨1266645178179674190605477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3377720475145797841614605 1266645178179674190605477)
                    ·
                      rfl

theorem cell22_3700174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_3700174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700174 prefixEnd_3700174 := by exact prefixLift 3700174
  have htrace : WordTrace (prefixWord ++ tailWord_3700174) baseStart_3700174 baseEnd_3700174 := by
    simpa [prefixWord, tailWord_3700174, baseEnd_3700174] using wordTrace_append hprefix tailTrace_3700174
  have hstable : (prefixWord ++ tailWord_3700174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700174).length < 2 ^ (prefixWord ++ tailWord_3700174).sum := by decide
  have hdescent : baseEnd_3700174 < baseStart_3700174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700208 : List Nat := [2, 1, 1, 1, 3, 5, 3, 2, 1, 3]
def baseStart_3700208 : Nat := 118140960795 + 3700208 * 2 ^ 59
def prefixEnd_3700208 : Nat := 4983230072969 + 3 ^ 40 * 3700208 * 2
def baseEnd_3700208 : Nat := 1266656817074509435255373

theorem tailTrace_3700208 : CollatzResearch.WordTrace tailWord_3700208 prefixEnd_3700208 1266656817074509435255373 := by
  unfold tailWord_3700208
  simp only [CollatzResearch.WordTrace]
  refine ⟨67478836489392918029890639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89971781985857224039854185 67478836489392918029890639)
  ·
    refine ⟨101218254734089377044835959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67478836489392918029890639 101218254734089377044835959)
    ·
      refine ⟨151827382101134065567253939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101218254734089377044835959 151827382101134065567253939)
      ·
        refine ⟨227741073151701098350880909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151827382101134065567253939 227741073151701098350880909)
        ·
          refine ⟨85402902431887911881580341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227741073151701098350880909 85402902431887911881580341)
          ·
            refine ⟨8006522102989491738898157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85402902431887911881580341 8006522102989491738898157)
            ·
              refine ⟨3002445788621059402086809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8006522102989491738898157 3002445788621059402086809)
              ·
                refine ⟨2251834341465794551565107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3002445788621059402086809 2251834341465794551565107)
                ·
                  refine ⟨3377751512198691827347661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251834341465794551565107 3377751512198691827347661)
                  ·
                    refine ⟨1266656817074509435255373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3377751512198691827347661 1266656817074509435255373)
                    ·
                      rfl

theorem cell22_3700208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 1, 3].length) (baseStart_3700208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700208 prefixEnd_3700208 := by exact prefixLift 3700208
  have htrace : WordTrace (prefixWord ++ tailWord_3700208) baseStart_3700208 baseEnd_3700208 := by
    simpa [prefixWord, tailWord_3700208, baseEnd_3700208] using wordTrace_append hprefix tailTrace_3700208
  have hstable : (prefixWord ++ tailWord_3700208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700208).length < 2 ^ (prefixWord ++ tailWord_3700208).sum := by decide
  have hdescent : baseEnd_3700208 < baseStart_3700208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700217 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 3, 4]
def baseStart_3700217 : Nat := 118140960795 + 3700217 * 2 ^ 59
def prefixEnd_3700217 : Nat := 4983230072969 + 3 ^ 40 * 3700217 * 2
def baseEnd_3700217 : Nat := 1266659897958436411780345

theorem tailTrace_3700217 : CollatzResearch.WordTrace tailWord_3700217 prefixEnd_3700217 1266659897958436411780345 := by
  unfold tailWord_3700217
  simp only [CollatzResearch.WordTrace]
  refine ⟨134958001235753230596858905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89972000823835487064572603 134958001235753230596858905)
  ·
    refine ⟨101218500926814922947644179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134958001235753230596858905 101218500926814922947644179)
    ·
      refine ⟨151827751390222384421466269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101218500926814922947644179 151827751390222384421466269)
      ·
        refine ⟨56935406771333394158049851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151827751390222384421466269 56935406771333394158049851)
        ·
          refine ⟨85403110157000091237074777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56935406771333394158049851 85403110157000091237074777)
          ·
            refine ⟨64052332617750068427806083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85403110157000091237074777 64052332617750068427806083)
            ·
              refine ⟨96078498926625102641709125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64052332617750068427806083 96078498926625102641709125)
              ·
                refine ⟨18014718548742206745320461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96078498926625102641709125 18014718548742206745320461)
                ·
                  refine ⟨6755519455778327529495173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18014718548742206745320461 6755519455778327529495173)
                  ·
                    refine ⟨1266659897958436411780345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6755519455778327529495173 1266659897958436411780345)
                    ·
                      rfl

theorem cell22_3700217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_3700217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700217 prefixEnd_3700217 := by exact prefixLift 3700217
  have htrace : WordTrace (prefixWord ++ tailWord_3700217) baseStart_3700217 baseEnd_3700217 := by
    simpa [prefixWord, tailWord_3700217, baseEnd_3700217] using wordTrace_append hprefix tailTrace_3700217
  have hstable : (prefixWord ++ tailWord_3700217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700217).length < 2 ^ (prefixWord ++ tailWord_3700217).sum := by decide
  have hdescent : baseEnd_3700217 < baseStart_3700217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700221 : List Nat := [1, 4, 1, 1, 1, 6, 2, 1, 5]
def baseStart_3700221 : Nat := 118140960795 + 3700221 * 2 ^ 59
def prefixEnd_3700221 : Nat := 4983230072969 + 3 ^ 40 * 3700221 * 2
def baseEnd_3700221 : Nat := 422220422413393911560111

theorem tailTrace_3700221 : CollatzResearch.WordTrace tailWord_3700221 prefixEnd_3700221 422220422413393911560111 := by
  unfold tailWord_3700221
  simp only [CollatzResearch.WordTrace]
  refine ⟨134958147127738739280004517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89972098085159159520003011 134958147127738739280004517)
  ·
    refine ⟨25304652586451013615000847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134958147127738739280004517 25304652586451013615000847)
    ·
      refine ⟨37956978879676520422501271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25304652586451013615000847 37956978879676520422501271)
      ·
        refine ⟨56935468319514780633751907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37956978879676520422501271 56935468319514780633751907)
        ·
          refine ⟨85403202479272170950627861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56935468319514780633751907 85403202479272170950627861)
          ·
            refine ⟨4003275116215883013310681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85403202479272170950627861 4003275116215883013310681)
            ·
              refine ⟨3002456337161912259983011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4003275116215883013310681 3002456337161912259983011)
              ·
                refine ⟨4503684505742868389974517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3002456337161912259983011 4503684505742868389974517)
                ·
                  refine ⟨422220422413393911560111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4503684505742868389974517 422220422413393911560111)
                  ·
                    rfl

theorem cell22_3700221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_3700221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700221 prefixEnd_3700221 := by exact prefixLift 3700221
  have htrace : WordTrace (prefixWord ++ tailWord_3700221) baseStart_3700221 baseEnd_3700221 := by
    simpa [prefixWord, tailWord_3700221, baseEnd_3700221] using wordTrace_append hprefix tailTrace_3700221
  have hstable : (prefixWord ++ tailWord_3700221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700221).length < 2 ^ (prefixWord ++ tailWord_3700221).sum := by decide
  have hdescent : baseEnd_3700221 < baseStart_3700221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700232 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 6]
def baseStart_3700232 : Nat := 118140960795 + 3700232 * 2 ^ 59
def prefixEnd_3700232 : Nat := 4983230072969 + 3 ^ 40 * 3700232 * 2
def baseEnd_3700232 : Nat := 422221677588327124218433

theorem tailTrace_3700232 : CollatzResearch.WordTrace tailWord_3700232 prefixEnd_3700232 422221677588327124218433 := by
  unfold tailWord_3700232
  simp only [CollatzResearch.WordTrace]
  refine ⟨67479274165349444079327475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89972365553799258772436633 67479274165349444079327475)
  ·
    refine ⟨101218911248024166118991213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67479274165349444079327475 101218911248024166118991213)
    ·
      refine ⟨37957091718009062294621705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101218911248024166118991213 37957091718009062294621705)
      ·
        refine ⟨28467818788506796720966279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37957091718009062294621705 28467818788506796720966279)
        ·
          refine ⟨42701728182760195081449419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28467818788506796720966279 42701728182760195081449419)
          ·
            refine ⟨64052592274140292622174129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42701728182760195081449419 64052592274140292622174129)
            ·
              refine ⟨48039444205605219466630597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64052592274140292622174129 48039444205605219466630597)
              ·
                refine ⟨9007395788550978649993237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48039444205605219466630597 9007395788550978649993237)
                ·
                  refine ⟨422221677588327124218433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9007395788550978649993237 422221677588327124218433)
                  ·
                    rfl

theorem cell22_3700232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 6].length) (baseStart_3700232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700232 prefixEnd_3700232 := by exact prefixLift 3700232
  have htrace : WordTrace (prefixWord ++ tailWord_3700232) baseStart_3700232 baseEnd_3700232 := by
    simpa [prefixWord, tailWord_3700232, baseEnd_3700232] using wordTrace_append hprefix tailTrace_3700232
  have hstable : (prefixWord ++ tailWord_3700232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700232).length < 2 ^ (prefixWord ++ tailWord_3700232).sum := by decide
  have hdescent : baseEnd_3700232 < baseStart_3700232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3700234 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_3700234 : Nat := 118140960795 + 3700234 * 2 ^ 59
def prefixEnd_3700234 : Nat := 4983230072969 + 3 ^ 40 * 3700234 * 2
def baseEnd_3700234 : Nat := 1266665717405854034105293

theorem tailTrace_3700234 : CollatzResearch.WordTrace tailWord_3700234 prefixEnd_3700234 1266665717405854034105293 := by
  unfold tailWord_3700234
  simp only [CollatzResearch.WordTrace]
  refine ⟨33739655319172910625056939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89972414184461095000151837 33739655319172910625056939)
  ·
    refine ⟨50609482978759365937585409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33739655319172910625056939 50609482978759365937585409)
    ·
      refine ⟨37957112234069524453189057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50609482978759365937585409 37957112234069524453189057)
      ·
        refine ⟨28467834175552143339891793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37957112234069524453189057 28467834175552143339891793)
        ·
          refine ⟨21350875631664107504918845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28467834175552143339891793 21350875631664107504918845)
          ·
            refine ⟨8006578361874040314344567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21350875631664107504918845 8006578361874040314344567)
            ·
              refine ⟨12009867542811060471516851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8006578361874040314344567 12009867542811060471516851)
              ·
                refine ⟨18014801314216590707275277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12009867542811060471516851 18014801314216590707275277)
                ·
                  refine ⟨6755550492831221515228229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18014801314216590707275277 6755550492831221515228229)
                  ·
                    refine ⟨1266665717405854034105293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6755550492831221515228229 1266665717405854034105293)
                    ·
                      rfl

theorem cell22_3700234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_3700234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3700234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3700234 prefixEnd_3700234 := by exact prefixLift 3700234
  have htrace : WordTrace (prefixWord ++ tailWord_3700234) baseStart_3700234 baseEnd_3700234 := by
    simpa [prefixWord, tailWord_3700234, baseEnd_3700234] using wordTrace_append hprefix tailTrace_3700234
  have hstable : (prefixWord ++ tailWord_3700234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3700234).length < 2 ^ (prefixWord ++ tailWord_3700234).sum := by decide
  have hdescent : baseEnd_3700234 < baseStart_3700234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3700234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
