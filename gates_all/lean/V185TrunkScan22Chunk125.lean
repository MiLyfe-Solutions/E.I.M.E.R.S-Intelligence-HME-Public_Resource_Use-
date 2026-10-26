import V185TrunkScan22Chunk124

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1118581 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1118581 : Nat := 118140960795 + 1118581 * 2 ^ 59
def prefixEnd_1118581 : Nat := 4983230072969 + 3 ^ 40 * 1118581 * 2
def baseEnd_1118581 : Nat := 382913135991328853595497

theorem tailTrace_1118581 : CollatzResearch.WordTrace tailWord_1118581 prefixEnd_1118581 382913135991328853595497 := by
  unfold tailWord_1118581
  simp only [CollatzResearch.WordTrace]
  refine ⟨40798000760579550270563597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27198667173719700180375731 40798000760579550270563597)
  ·
    refine ⟨15299250285217331351461349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40798000760579550270563597 15299250285217331351461349)
    ·
      refine ⟨2868609428478249628399003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15299250285217331351461349 2868609428478249628399003)
      ·
        refine ⟨4302914142717374442598505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2868609428478249628399003 4302914142717374442598505)
        ·
          refine ⟨3227185607038030831948879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4302914142717374442598505 3227185607038030831948879)
          ·
            refine ⟨4840778410557046247923319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3227185607038030831948879 4840778410557046247923319)
            ·
              refine ⟨7261167615835569371884979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4840778410557046247923319 7261167615835569371884979)
              ·
                refine ⟨10891751423753354057827469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7261167615835569371884979 10891751423753354057827469)
                ·
                  refine ⟨4084406783907507771685301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10891751423753354057827469 4084406783907507771685301)
                  ·
                    refine ⟨382913135991328853595497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4084406783907507771685301 382913135991328853595497)
                    ·
                      rfl

theorem cell22_1118581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1118581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118581 prefixEnd_1118581 := by exact prefixLift 1118581
  have htrace : WordTrace (prefixWord ++ tailWord_1118581) baseStart_1118581 baseEnd_1118581 := by
    simpa [prefixWord, tailWord_1118581, baseEnd_1118581] using wordTrace_append hprefix tailTrace_1118581
  have hstable : (prefixWord ++ tailWord_1118581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118581).length < 2 ^ (prefixWord ++ tailWord_1118581).sum := by decide
  have hdescent : baseEnd_1118581 < baseStart_1118581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118596 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_1118596 : Nat := 118140960795 + 1118596 * 2 ^ 59
def prefixEnd_1118596 : Nat := 4983230072969 + 3 ^ 40 * 1118596 * 2
def baseEnd_1118596 : Nat := 382918270797873814470451

theorem tailTrace_1118596 : CollatzResearch.WordTrace tailWord_1118596 prefixEnd_1118596 382918270797873814470451 := by
  unfold tailWord_1118596
  simp only [CollatzResearch.WordTrace]
  refine ⟨20399273927762603916179821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27199031903683471888239761 20399273927762603916179821)
  ·
    refine ⟨7649727722910976468567433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20399273927762603916179821 7649727722910976468567433)
    ·
      refine ⟨5737295792183232351425575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7649727722910976468567433 5737295792183232351425575)
      ·
        refine ⟨8605943688274848527138363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5737295792183232351425575 8605943688274848527138363)
        ·
          refine ⟨12908915532412272790707545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8605943688274848527138363 12908915532412272790707545)
          ·
            refine ⟨9681686649309204593030659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12908915532412272790707545 9681686649309204593030659)
            ·
              refine ⟨14522529973963806889545989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9681686649309204593030659 14522529973963806889545989)
              ·
                refine ⟨2722974370118213791789873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14522529973963806889545989 2722974370118213791789873)
                ·
                  refine ⟨2042230777588660343842405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2722974370118213791789873 2042230777588660343842405)
                  ·
                    refine ⟨382918270797873814470451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2042230777588660343842405 382918270797873814470451)
                    ·
                      rfl

theorem cell22_1118596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_1118596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118596 prefixEnd_1118596 := by exact prefixLift 1118596
  have htrace : WordTrace (prefixWord ++ tailWord_1118596) baseStart_1118596 baseEnd_1118596 := by
    simpa [prefixWord, tailWord_1118596, baseEnd_1118596] using wordTrace_append hprefix tailTrace_1118596
  have hstable : (prefixWord ++ tailWord_1118596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118596).length < 2 ^ (prefixWord ++ tailWord_1118596).sum := by decide
  have hdescent : baseEnd_1118596 < baseStart_1118596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118634 : List Nat := [3, 1, 6, 1, 1, 1, 2, 3, 4]
def baseStart_1118634 : Nat := 118140960795 + 1118634 * 2 ^ 59
def prefixEnd_1118634 : Nat := 4983230072969 + 3 ^ 40 * 1118634 * 2
def baseEnd_1118634 : Nat := 127643759658151460673445

theorem tailTrace_1118634 : CollatzResearch.WordTrace tailWord_1118634 prefixEnd_1118634 127643759658151460673445 := by
  unfold tailWord_1118634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10199983457346885080560739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27199955886258360214828637 10199983457346885080560739)
  ·
    refine ⟨15299975186020327620841109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10199983457346885080560739 15299975186020327620841109)
    ·
      refine ⟨717186336844702857226927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15299975186020327620841109 717186336844702857226927)
      ·
        refine ⟨1075779505267054285840391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717186336844702857226927 1075779505267054285840391)
        ·
          refine ⟨1613669257900581428760587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1075779505267054285840391 1613669257900581428760587)
          ·
            refine ⟨2420503886850872143140881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1613669257900581428760587 2420503886850872143140881)
            ·
              refine ⟨1815377915138154107355661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2420503886850872143140881 1815377915138154107355661)
              ·
                refine ⟨680766718176807790258373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1815377915138154107355661 680766718176807790258373)
                ·
                  refine ⟨127643759658151460673445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 680766718176807790258373 127643759658151460673445)
                  ·
                    rfl

theorem cell22_1118634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_1118634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118634 prefixEnd_1118634 := by exact prefixLift 1118634
  have htrace : WordTrace (prefixWord ++ tailWord_1118634) baseStart_1118634 baseEnd_1118634 := by
    simpa [prefixWord, tailWord_1118634, baseEnd_1118634] using wordTrace_append hprefix tailTrace_1118634
  have hstable : (prefixWord ++ tailWord_1118634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118634).length < 2 ^ (prefixWord ++ tailWord_1118634).sum := by decide
  have hdescent : baseEnd_1118634 < baseStart_1118634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118746 : List Nat := [3, 1, 1, 3, 1, 1, 4, 8]
def baseStart_1118746 : Nat := 118140960795 + 1118746 * 2 ^ 59
def prefixEnd_1118746 : Nat := 4983230072969 + 3 ^ 40 * 1118746 * 2
def baseEnd_1118746 : Nat := 42552179873702602579999

theorem tailTrace_1118746 : CollatzResearch.WordTrace tailWord_1118746 prefixEnd_1118746 42552179873702602579999 := by
  unfold tailWord_1118746
  simp only [CollatzResearch.WordTrace]
  refine ⟨10201004701245445862580023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27202679203321188966880061 10201004701245445862580023)
  ·
    refine ⟨15301507051868168793870035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10201004701245445862580023 15301507051868168793870035)
    ·
      refine ⟨22952260577802253190805053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15301507051868168793870035 22952260577802253190805053)
      ·
        refine ⟨8607097716675844946551895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22952260577802253190805053 8607097716675844946551895)
        ·
          refine ⟨12910646575013767419827843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8607097716675844946551895 12910646575013767419827843)
          ·
            refine ⟨19365969862520651129741765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12910646575013767419827843 19365969862520651129741765)
            ·
              refine ⟨3631119349222622086826581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19365969862520651129741765 3631119349222622086826581)
              ·
                refine ⟨42552179873702602579999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3631119349222622086826581 42552179873702602579999)
                ·
                  rfl

theorem cell22_1118746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_1118746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118746 prefixEnd_1118746 := by exact prefixLift 1118746
  have htrace : WordTrace (prefixWord ++ tailWord_1118746) baseStart_1118746 baseEnd_1118746 := by
    simpa [prefixWord, tailWord_1118746, baseEnd_1118746] using wordTrace_append hprefix tailTrace_1118746
  have hstable : (prefixWord ++ tailWord_1118746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118746).length < 2 ^ (prefixWord ++ tailWord_1118746).sum := by decide
  have hdescent : baseEnd_1118746 < baseStart_1118746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118748 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_1118748 : Nat := 118140960795 + 1118748 * 2 ^ 59
def prefixEnd_1118748 : Nat := 4983230072969 + 3 ^ 40 * 1118748 * 2
def baseEnd_1118748 : Nat := 382970303504196084669985

theorem tailTrace_1118748 : CollatzResearch.WordTrace tailWord_1118748 prefixEnd_1118748 382970303504196084669985 := by
  unfold tailWord_1118748
  simp only [CollatzResearch.WordTrace]
  refine ⟨20402045875487268895946449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27202727833983025194595265 20402045875487268895946449)
  ·
    refine ⟨15301534406615451671959837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20402045875487268895946449 15301534406615451671959837)
    ·
      refine ⟨5738075402480794376984939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15301534406615451671959837 5738075402480794376984939)
      ·
        refine ⟨8607113103721191565477409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5738075402480794376984939 8607113103721191565477409)
        ·
          refine ⟨6455334827790893674108057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8607113103721191565477409 6455334827790893674108057)
          ·
            refine ⟨4841501120843170255581043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6455334827790893674108057 4841501120843170255581043)
            ·
              refine ⟨7262251681264755383371565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4841501120843170255581043 7262251681264755383371565)
              ·
                refine ⟨2723344380474283268764337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7262251681264755383371565 2723344380474283268764337)
                ·
                  refine ⟨2042508285355712451573253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2723344380474283268764337 2042508285355712451573253)
                  ·
                    refine ⟨382970303504196084669985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2042508285355712451573253 382970303504196084669985)
                    ·
                      rfl

theorem cell22_1118748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_1118748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118748 prefixEnd_1118748 := by exact prefixLift 1118748
  have htrace : WordTrace (prefixWord ++ tailWord_1118748) baseStart_1118748 baseEnd_1118748 := by
    simpa [prefixWord, tailWord_1118748, baseEnd_1118748] using wordTrace_append hprefix tailTrace_1118748
  have hstable : (prefixWord ++ tailWord_1118748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118748).length < 2 ^ (prefixWord ++ tailWord_1118748).sum := by decide
  have hdescent : baseEnd_1118748 < baseStart_1118748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118776 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 1, 8]
def baseStart_1118776 : Nat := 118140960795 + 1118776 * 2 ^ 59
def prefixEnd_1118776 : Nat := 4983230072969 + 3 ^ 40 * 1118776 * 2
def baseEnd_1118776 : Nat := 382979888476413344969899

theorem tailTrace_1118776 : CollatzResearch.WordTrace tailWord_1118776 prefixEnd_1118776 382979888476413344969899 := by
  unfold tailWord_1118776
  simp only [CollatzResearch.WordTrace]
  refine ⟨20402556497436549286956091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27203408663248732382608121 20402556497436549286956091)
  ·
    refine ⟨30603834746154823930434137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20402556497436549286956091 30603834746154823930434137)
    ·
      refine ⟨22952876059616117947825603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30603834746154823930434137 22952876059616117947825603)
      ·
        refine ⟨34429314089424176921738405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22952876059616117947825603 34429314089424176921738405)
        ·
          refine ⟨6455496391767033172825951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34429314089424176921738405 6455496391767033172825951)
          ·
            refine ⟨9683244587650549759238927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6455496391767033172825951 9683244587650549759238927)
            ·
              refine ⟨14524866881475824638858391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9683244587650549759238927 14524866881475824638858391)
              ·
                refine ⟨21787300322213736958287587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14524866881475824638858391 21787300322213736958287587)
                ·
                  refine ⟨32680950483320605437431381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21787300322213736958287587 32680950483320605437431381)
                  ·
                    refine ⟨382979888476413344969899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32680950483320605437431381 382979888476413344969899)
                    ·
                      rfl

theorem cell22_1118776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_1118776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118776 prefixEnd_1118776 := by exact prefixLift 1118776
  have htrace : WordTrace (prefixWord ++ tailWord_1118776) baseStart_1118776 baseEnd_1118776 := by
    simpa [prefixWord, tailWord_1118776, baseEnd_1118776] using wordTrace_append hprefix tailTrace_1118776
  have hstable : (prefixWord ++ tailWord_1118776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118776).length < 2 ^ (prefixWord ++ tailWord_1118776).sum := by decide
  have hdescent : baseEnd_1118776 < baseStart_1118776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118853 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 6]
def baseStart_1118853 : Nat := 118140960795 + 1118853 * 2 ^ 59
def prefixEnd_1118853 : Nat := 4983230072969 + 3 ^ 40 * 1118853 * 2
def baseEnd_1118853 : Nat := 127668749050003603598221

theorem tailTrace_1118853 : CollatzResearch.WordTrace tailWord_1118853 prefixEnd_1118853 127668749050003603598221 := by
  unfold tailWord_1118853
  simp only [CollatzResearch.WordTrace]
  refine ⟨40807921415594140724465213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27205280943729427149643475 40807921415594140724465213)
  ·
    refine ⟨15302970530847802771674455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40807921415594140724465213 15302970530847802771674455)
    ·
      refine ⟨22954455796271704157511683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15302970530847802771674455 22954455796271704157511683)
      ·
        refine ⟨34431683694407556236267525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22954455796271704157511683 34431683694407556236267525)
        ·
          refine ⟨6455940692701416794300161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34431683694407556236267525 6455940692701416794300161)
          ·
            refine ⟨4841955519526062595725121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6455940692701416794300161 4841955519526062595725121)
            ·
              refine ⟨3631466639644546946793841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4841955519526062595725121 3631466639644546946793841)
              ·
                refine ⟨2723599979733410210095381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3631466639644546946793841 2723599979733410210095381)
                ·
                  refine ⟨127668749050003603598221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2723599979733410210095381 127668749050003603598221)
                  ·
                    rfl

theorem cell22_1118853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_1118853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118853 prefixEnd_1118853 := by exact prefixLift 1118853
  have htrace : WordTrace (prefixWord ++ tailWord_1118853) baseStart_1118853 baseEnd_1118853 := by
    simpa [prefixWord, tailWord_1118853, baseEnd_1118853] using wordTrace_append hprefix tailTrace_1118853
  have hstable : (prefixWord ++ tailWord_1118853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118853).length < 2 ^ (prefixWord ++ tailWord_1118853).sum := by decide
  have hdescent : baseEnd_1118853 < baseStart_1118853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118855 : List Nat := [1, 1, 4, 2, 1, 2, 4, 2, 1, 4]
def baseStart_1118855 : Nat := 118140960795 + 1118855 * 2 ^ 59
def prefixEnd_1118855 : Nat := 4983230072969 + 3 ^ 40 * 1118855 * 2
def baseEnd_1118855 : Nat := 383006931790883472244657

theorem tailTrace_1118855 : CollatzResearch.WordTrace tailWord_1118855 prefixEnd_1118855 383006931790883472244657 := by
  unfold tailWord_1118855
  simp only [CollatzResearch.WordTrace]
  refine ⟨40807994361586895066038019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27205329574391263377358679 40807994361586895066038019)
  ·
    refine ⟨61211991542380342599057029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40807994361586895066038019 61211991542380342599057029)
    ·
      refine ⟨11477248414196314237323193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61211991542380342599057029 11477248414196314237323193)
      ·
        refine ⟨8607936310647235677992395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11477248414196314237323193 8607936310647235677992395)
        ·
          refine ⟨12911904465970853516988593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8607936310647235677992395 12911904465970853516988593)
          ·
            refine ⟨9683928349478140137741445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12911904465970853516988593 9683928349478140137741445)
            ·
              refine ⟨1815736565527151275826521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9683928349478140137741445 1815736565527151275826521)
              ·
                refine ⟨1361802424145363456869891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1815736565527151275826521 1361802424145363456869891)
                ·
                  refine ⟨2042703636218045185304837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1361802424145363456869891 2042703636218045185304837)
                  ·
                    refine ⟨383006931790883472244657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2042703636218045185304837 383006931790883472244657)
                    ·
                      rfl

theorem cell22_1118855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_1118855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118855 prefixEnd_1118855 := by exact prefixLift 1118855
  have htrace : WordTrace (prefixWord ++ tailWord_1118855) baseStart_1118855 baseEnd_1118855 := by
    simpa [prefixWord, tailWord_1118855, baseEnd_1118855] using wordTrace_append hprefix tailTrace_1118855
  have hstable : (prefixWord ++ tailWord_1118855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118855).length < 2 ^ (prefixWord ++ tailWord_1118855).sum := by decide
  have hdescent : baseEnd_1118855 < baseStart_1118855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118885 : List Nat := [1, 3, 1, 2, 1, 2, 1, 6, 2, 3]
def baseStart_1118885 : Nat := 118140960795 + 1118885 * 2 ^ 59
def prefixEnd_1118885 : Nat := 4983230072969 + 3 ^ 40 * 1118885 * 2
def baseEnd_1118885 : Nat := 383017201403973393994565

theorem tailTrace_1118885 : CollatzResearch.WordTrace tailWord_1118885 prefixEnd_1118885 383017201403973393994565 := by
  unfold tailWord_1118885
  simp only [CollatzResearch.WordTrace]
  refine ⟨40809088551478210189630109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27206059034318806793086739 40809088551478210189630109)
  ·
    refine ⟨15303408206804328821111291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40809088551478210189630109 15303408206804328821111291)
    ·
      refine ⟨22955112310206493231666937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15303408206804328821111291 22955112310206493231666937)
      ·
        refine ⟨17216334232654869923750203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22955112310206493231666937 17216334232654869923750203)
        ·
          refine ⟨25824501348982304885625305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17216334232654869923750203 25824501348982304885625305)
          ·
            refine ⟨19368376011736728664218979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25824501348982304885625305 19368376011736728664218979)
            ·
              refine ⟨29052564017605092996328469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19368376011736728664218979 29052564017605092996328469)
              ·
                refine ⟨1361838938325238734202897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29052564017605092996328469 1361838938325238734202897)
                ·
                  refine ⟨1021379203743929050652173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1361838938325238734202897 1021379203743929050652173)
                  ·
                    refine ⟨383017201403973393994565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1021379203743929050652173 383017201403973393994565)
                    ·
                      rfl

theorem cell22_1118885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_1118885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118885 prefixEnd_1118885 := by exact prefixLift 1118885
  have htrace : WordTrace (prefixWord ++ tailWord_1118885) baseStart_1118885 baseEnd_1118885 := by
    simpa [prefixWord, tailWord_1118885, baseEnd_1118885] using wordTrace_append hprefix tailTrace_1118885
  have hstable : (prefixWord ++ tailWord_1118885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118885).length < 2 ^ (prefixWord ++ tailWord_1118885).sum := by decide
  have hdescent : baseEnd_1118885 < baseStart_1118885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1118988 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 10]
def baseStart_1118988 : Nat := 118140960795 + 1118988 * 2 ^ 59
def prefixEnd_1118988 : Nat := 4983230072969 + 3 ^ 40 * 1118988 * 2
def baseEnd_1118988 : Nat := 127684153469638486223083

theorem tailTrace_1118988 : CollatzResearch.WordTrace tailWord_1118988 prefixEnd_1118988 127684153469638486223083 := by
  unfold tailWord_1118988
  simp only [CollatzResearch.WordTrace]
  refine ⟨20406422635052529390314809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27208563513403372520419745 20406422635052529390314809)
  ·
    refine ⟨15304816976289397042736107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20406422635052529390314809 15304816976289397042736107)
    ·
      refine ⟨22957225464434095564104161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15304816976289397042736107 22957225464434095564104161)
      ·
        refine ⟨17217919098325571673078121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22957225464434095564104161 17217919098325571673078121)
        ·
          refine ⟨12913439323744178754808591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17217919098325571673078121 12913439323744178754808591)
          ·
            refine ⟨19370158985616268132212887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12913439323744178754808591 19370158985616268132212887)
            ·
              refine ⟨29055238478424402198319331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19370158985616268132212887 29055238478424402198319331)
              ·
                refine ⟨43582857717636603297478997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29055238478424402198319331 43582857717636603297478997)
                ·
                  refine ⟨127684153469638486223083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 43582857717636603297478997 127684153469638486223083)
                  ·
                    rfl

theorem cell22_1118988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_1118988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1118988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1118988 prefixEnd_1118988 := by exact prefixLift 1118988
  have htrace : WordTrace (prefixWord ++ tailWord_1118988) baseStart_1118988 baseEnd_1118988 := by
    simpa [prefixWord, tailWord_1118988, baseEnd_1118988] using wordTrace_append hprefix tailTrace_1118988
  have hstable : (prefixWord ++ tailWord_1118988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1118988).length < 2 ^ (prefixWord ++ tailWord_1118988).sum := by decide
  have hdescent : baseEnd_1118988 < baseStart_1118988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1118988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119022 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_1119022 : Nat := 118140960795 + 1119022 * 2 ^ 59
def prefixEnd_1119022 : Nat := 4983230072969 + 3 ^ 40 * 1119022 * 2
def baseEnd_1119022 : Nat := 127688033101250234439715

theorem tailTrace_1119022 : CollatzResearch.WordTrace tailWord_1119022 prefixEnd_1119022 127688033101250234439715 := by
  unfold tailWord_1119022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5101760668997735323420915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27209390234654588391578213 5101760668997735323420915)
  ·
    refine ⟨7652641003496602985131373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5101760668997735323420915 7652641003496602985131373)
    ·
      refine ⟨2869740376311226119424265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7652641003496602985131373 2869740376311226119424265)
      ·
        refine ⟨2152305282233419589568199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2869740376311226119424265 2152305282233419589568199)
        ·
          refine ⟨3228457923350129384352299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2152305282233419589568199 3228457923350129384352299)
          ·
            refine ⟨4842686885025194076528449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3228457923350129384352299 4842686885025194076528449)
            ·
              refine ⟨3632015163768895557396337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4842686885025194076528449 3632015163768895557396337)
              ·
                refine ⟨2724011372826671668047253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3632015163768895557396337 2724011372826671668047253)
                ·
                  refine ⟨127688033101250234439715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2724011372826671668047253 127688033101250234439715)
                  ·
                    rfl

theorem cell22_1119022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_1119022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119022 prefixEnd_1119022 := by exact prefixLift 1119022
  have htrace : WordTrace (prefixWord ++ tailWord_1119022) baseStart_1119022 baseEnd_1119022 := by
    simpa [prefixWord, tailWord_1119022, baseEnd_1119022] using wordTrace_append hprefix tailTrace_1119022
  have hstable : (prefixWord ++ tailWord_1119022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119022).length < 2 ^ (prefixWord ++ tailWord_1119022).sum := by decide
  have hdescent : baseEnd_1119022 < baseStart_1119022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119039 : List Nat := [1, 1, 2, 2, 5, 3, 1, 3, 4]
def baseStart_1119039 : Nat := 118140960795 + 1119039 * 2 ^ 59
def prefixEnd_1119039 : Nat := 4983230072969 + 3 ^ 40 * 1119039 * 2
def baseEnd_1119039 : Nat := 127689972917056108548031

theorem tailTrace_1119039 : CollatzResearch.WordTrace tailWord_1119039 prefixEnd_1119039 127689972917056108548031 := by
  unfold tailWord_1119039
  simp only [CollatzResearch.WordTrace]
  refine ⟨40814705392920294490736171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27209803595280196327157447 40814705392920294490736171)
  ·
    refine ⟨61222058089380441736104257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40814705392920294490736171 61222058089380441736104257)
    ·
      refine ⟨45916543567035331302078193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61222058089380441736104257 45916543567035331302078193)
      ·
        refine ⟨34437407675276498476558645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45916543567035331302078193 34437407675276498476558645)
        ·
          refine ⟨3228506969557171732177373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34437407675276498476558645 3228506969557171732177373)
          ·
            refine ⟨1210690113583939399566515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3228506969557171732177373 1210690113583939399566515)
            ·
              refine ⟨1816035170375909099349773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1210690113583939399566515 1816035170375909099349773)
              ·
                refine ⟨681013188890965912256165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1816035170375909099349773 681013188890965912256165)
                ·
                  refine ⟨127689972917056108548031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 681013188890965912256165 127689972917056108548031)
                  ·
                    rfl

theorem cell22_1119039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 4].length) (baseStart_1119039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119039 prefixEnd_1119039 := by exact prefixLift 1119039
  have htrace : WordTrace (prefixWord ++ tailWord_1119039) baseStart_1119039 baseEnd_1119039 := by
    simpa [prefixWord, tailWord_1119039, baseEnd_1119039] using wordTrace_append hprefix tailTrace_1119039
  have hstable : (prefixWord ++ tailWord_1119039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119039).length < 2 ^ (prefixWord ++ tailWord_1119039).sum := by decide
  have hdescent : baseEnd_1119039 < baseStart_1119039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119052 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_1119052 : Nat := 118140960795 + 1119052 * 2 ^ 59
def prefixEnd_1119052 : Nat := 4983230072969 + 3 ^ 40 * 1119052 * 2
def baseEnd_1119052 : Nat := 383074368916840625069053

theorem tailTrace_1119052 : CollatzResearch.WordTrace tailWord_1119052 prefixEnd_1119052 383074368916840625069053 := by
  unfold tailWord_1119052
  simp only [CollatzResearch.WordTrace]
  refine ⟨20407589770936598855479705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27210119694582131807306273 20407589770936598855479705)
  ·
    refine ⟨15305692328202449141609779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20407589770936598855479705 15305692328202449141609779)
    ·
      refine ⟨22958538492303673712414669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15305692328202449141609779 22958538492303673712414669)
      ·
        refine ⟨8609451934613877642155501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22958538492303673712414669 8609451934613877642155501)
        ·
          refine ⟨3228544475480204115808313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8609451934613877642155501 3228544475480204115808313)
          ·
            refine ⟨2421408356610153086856235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3228544475480204115808313 2421408356610153086856235)
            ·
              refine ⟨3632112534915229630284353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2421408356610153086856235 3632112534915229630284353)
              ·
                refine ⟨2724084401186422222713265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3632112534915229630284353 2724084401186422222713265)
                ·
                  refine ⟨2043063300889816667034949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2724084401186422222713265 2043063300889816667034949)
                  ·
                    refine ⟨383074368916840625069053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2043063300889816667034949 383074368916840625069053)
                    ·
                      rfl

theorem cell22_1119052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_1119052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119052 prefixEnd_1119052 := by exact prefixLift 1119052
  have htrace : WordTrace (prefixWord ++ tailWord_1119052) baseStart_1119052 baseEnd_1119052 := by
    simpa [prefixWord, tailWord_1119052, baseEnd_1119052] using wordTrace_append hprefix tailTrace_1119052
  have hstable : (prefixWord ++ tailWord_1119052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119052).length < 2 ^ (prefixWord ++ tailWord_1119052).sum := by decide
  have hdescent : baseEnd_1119052 < baseStart_1119052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119112 : List Nat := [2, 1, 3, 3, 2, 1, 1, 4, 5]
def baseStart_1119112 : Nat := 118140960795 + 1119112 * 2 ^ 59
def prefixEnd_1119112 : Nat := 4983230072969 + 3 ^ 40 * 1119112 * 2
def baseEnd_1119112 : Nat := 127698302714340156189623

theorem tailTrace_1119112 : CollatzResearch.WordTrace tailWord_1119112 prefixEnd_1119112 127698302714340156189623 := by
  unfold tailWord_1119112
  simp only [CollatzResearch.WordTrace]
  refine ⟨20408683960827913979071795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27211578614437218638762393 20408683960827913979071795)
  ·
    refine ⟨30613025941241870968607693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20408683960827913979071795 30613025941241870968607693)
    ·
      refine ⟨11479884727965701613227885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30613025941241870968607693 11479884727965701613227885)
      ·
        refine ⟨4304956772987138104960457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11479884727965701613227885 4304956772987138104960457)
        ·
          refine ⟨3228717579740353578720343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4304956772987138104960457 3228717579740353578720343)
          ·
            refine ⟨4843076369610530368080515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3228717579740353578720343 4843076369610530368080515)
            ·
              refine ⟨7264614554415795552120773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4843076369610530368080515 7264614554415795552120773)
              ·
                refine ⟨1362115228952961666022645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7264614554415795552120773 1362115228952961666022645)
                ·
                  refine ⟨127698302714340156189623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1362115228952961666022645 127698302714340156189623)
                  ·
                    rfl

theorem cell22_1119112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 4, 5].length) (baseStart_1119112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119112 prefixEnd_1119112 := by exact prefixLift 1119112
  have htrace : WordTrace (prefixWord ++ tailWord_1119112) baseStart_1119112 baseEnd_1119112 := by
    simpa [prefixWord, tailWord_1119112, baseEnd_1119112] using wordTrace_append hprefix tailTrace_1119112
  have hstable : (prefixWord ++ tailWord_1119112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119112).length < 2 ^ (prefixWord ++ tailWord_1119112).sum := by decide
  have hdescent : baseEnd_1119112 < baseStart_1119112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119116 : List Nat := [2, 2, 1, 2, 1, 2, 6, 2, 1, 3]
def baseStart_1119116 : Nat := 118140960795 + 1119116 * 2 ^ 59
def prefixEnd_1119116 : Nat := 4983230072969 + 3 ^ 40 * 1119116 * 2
def baseEnd_1119116 : Nat := 383096277424765791468857

theorem tailTrace_1119116 : CollatzResearch.WordTrace tailWord_1119116 prefixEnd_1119116 383096277424765791468857 := by
  unfold tailWord_1119116
  simp only [CollatzResearch.WordTrace]
  refine ⟨20408756906820668320644601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27211675875760891094192801 20408756906820668320644601)
  ·
    refine ⟨15306567680115501240483451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20408756906820668320644601 15306567680115501240483451)
    ·
      refine ⟨22959851520173251860725177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15306567680115501240483451 22959851520173251860725177)
      ·
        refine ⟨17219888640129938895543883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22959851520173251860725177 17219888640129938895543883)
        ·
          refine ⟨25829832960194908343315825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17219888640129938895543883 25829832960194908343315825)
          ·
            refine ⟨19372374720146181257486869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25829832960194908343315825 19372374720146181257486869)
            ·
              refine ⟨908080065006852246444697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19372374720146181257486869 908080065006852246444697)
              ·
                refine ⟨681060048755139184833523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 908080065006852246444697 681060048755139184833523)
                ·
                  refine ⟨1021590073132708777250285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681060048755139184833523 1021590073132708777250285)
                  ·
                    refine ⟨383096277424765791468857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1021590073132708777250285 383096277424765791468857)
                    ·
                      rfl

theorem cell22_1119116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_1119116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119116 prefixEnd_1119116 := by exact prefixLift 1119116
  have htrace : WordTrace (prefixWord ++ tailWord_1119116) baseStart_1119116 baseEnd_1119116 := by
    simpa [prefixWord, tailWord_1119116, baseEnd_1119116] using wordTrace_append hprefix tailTrace_1119116
  have hstable : (prefixWord ++ tailWord_1119116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119116).length < 2 ^ (prefixWord ++ tailWord_1119116).sum := by decide
  have hdescent : baseEnd_1119116 < baseStart_1119116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119155 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 3, 5]
def baseStart_1119155 : Nat := 118140960795 + 1119155 * 2 ^ 59
def prefixEnd_1119155 : Nat := 4983230072969 + 3 ^ 40 * 1119155 * 2
def baseEnd_1119155 : Nat := 383109627921782689743737

theorem tailTrace_1119155 : CollatzResearch.WordTrace tailWord_1119155 prefixEnd_1119155 383109627921782689743737 := by
  unfold tailWord_1119155
  simp only [CollatzResearch.WordTrace]
  refine ⟨40818936260500046301958919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27212624173666697534639279 40818936260500046301958919)
  ·
    refine ⟨61228404390750069452938379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40818936260500046301958919 61228404390750069452938379)
    ·
      refine ⟨91842606586125104179407569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61228404390750069452938379 91842606586125104179407569)
      ·
        refine ⟨68881954939593828134555677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91842606586125104179407569 68881954939593828134555677)
        ·
          refine ⟨25830733102347685550458379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68881954939593828134555677 25830733102347685550458379)
          ·
            refine ⟨38746099653521528325687569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25830733102347685550458379 38746099653521528325687569)
            ·
              refine ⟨29059574740141146244265677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38746099653521528325687569 29059574740141146244265677)
              ·
                refine ⟨10897340527552929841599629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29059574740141146244265677 10897340527552929841599629)
                ·
                  refine ⟨4086502697832348690599861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10897340527552929841599629 4086502697832348690599861)
                  ·
                    refine ⟨383109627921782689743737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4086502697832348690599861 383109627921782689743737)
                    ·
                      rfl

theorem cell22_1119155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 5].length) (baseStart_1119155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119155 prefixEnd_1119155 := by exact prefixLift 1119155
  have htrace : WordTrace (prefixWord ++ tailWord_1119155) baseStart_1119155 baseEnd_1119155 := by
    simpa [prefixWord, tailWord_1119155, baseEnd_1119155] using wordTrace_append hprefix tailTrace_1119155
  have hstable : (prefixWord ++ tailWord_1119155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119155).length < 2 ^ (prefixWord ++ tailWord_1119155).sum := by decide
  have hdescent : baseEnd_1119155 < baseStart_1119155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119159 : List Nat := [1, 1, 3, 1, 3, 1, 6, 1, 1, 4]
def baseStart_1119159 : Nat := 118140960795 + 1119159 * 2 ^ 59
def prefixEnd_1119159 : Nat := 4983230072969 + 3 ^ 40 * 1119159 * 2
def baseEnd_1119159 : Nat := 383110997203528012643725

theorem tailTrace_1119159 : CollatzResearch.WordTrace tailWord_1119159 prefixEnd_1119159 383110997203528012643725 := by
  unfold tailWord_1119159
  simp only [CollatzResearch.WordTrace]
  refine ⟨40819082152485554985104531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27212721434990369990069687 40819082152485554985104531)
  ·
    refine ⟨61228623228728332477656797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40819082152485554985104531 61228623228728332477656797)
    ·
      refine ⟨22960733710773124679121299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61228623228728332477656797 22960733710773124679121299)
      ·
        refine ⟨34441100566159687018681949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22960733710773124679121299 34441100566159687018681949)
        ·
          refine ⟨12915412712309882632005731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34441100566159687018681949 12915412712309882632005731)
          ·
            refine ⟨19373119068464823948008597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12915412712309882632005731 19373119068464823948008597)
            ·
              refine ⟨908114956334288622562903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19373119068464823948008597 908114956334288622562903)
              ·
                refine ⟨1362172434501432933844355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908114956334288622562903 1362172434501432933844355)
                ·
                  refine ⟨2043258651752149400766533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362172434501432933844355 2043258651752149400766533)
                  ·
                    refine ⟨383110997203528012643725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2043258651752149400766533 383110997203528012643725)
                    ·
                      rfl

theorem cell22_1119159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_1119159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119159 prefixEnd_1119159 := by exact prefixLift 1119159
  have htrace : WordTrace (prefixWord ++ tailWord_1119159) baseStart_1119159 baseEnd_1119159 := by
    simpa [prefixWord, tailWord_1119159, baseEnd_1119159] using wordTrace_append hprefix tailTrace_1119159
  have hstable : (prefixWord ++ tailWord_1119159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119159).length < 2 ^ (prefixWord ++ tailWord_1119159).sum := by decide
  have hdescent : baseEnd_1119159 < baseStart_1119159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119185 : List Nat := [1, 2, 2, 1, 2, 1, 4, 9]
def baseStart_1119185 : Nat := 118140960795 + 1119185 * 2 ^ 59
def prefixEnd_1119185 : Nat := 4983230072969 + 3 ^ 40 * 1119185 * 2
def baseEnd_1119185 : Nat := 42568877503874734610405

theorem tailTrace_1119185 : CollatzResearch.WordTrace tailWord_1119185 prefixEnd_1119185 42568877503874734610405 := by
  unfold tailWord_1119185
  simp only [CollatzResearch.WordTrace]
  refine ⟨40820030450391361425551009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27213353633594240950367339 40820030450391361425551009)
  ·
    refine ⟨30615022837793521069163257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40820030450391361425551009 30615022837793521069163257)
    ·
      refine ⟨22961267128345140801872443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30615022837793521069163257 22961267128345140801872443)
      ·
        refine ⟨34441900692517711202808665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22961267128345140801872443 34441900692517711202808665)
        ·
          refine ⟨25831425519388283402106499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34441900692517711202808665 25831425519388283402106499)
          ·
            refine ⟨38747138279082425103159749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25831425519388283402106499 38747138279082425103159749)
            ·
              refine ⟨7265088427327954706842453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38747138279082425103159749 7265088427327954706842453)
              ·
                refine ⟨42568877503874734610405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7265088427327954706842453 42568877503874734610405)
                ·
                  rfl

theorem cell22_1119185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 9].length) (baseStart_1119185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119185 prefixEnd_1119185 := by exact prefixLift 1119185
  have htrace : WordTrace (prefixWord ++ tailWord_1119185) baseStart_1119185 baseEnd_1119185 := by
    simpa [prefixWord, tailWord_1119185, baseEnd_1119185] using wordTrace_append hprefix tailTrace_1119185
  have hstable : (prefixWord ++ tailWord_1119185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119185).length < 2 ^ (prefixWord ++ tailWord_1119185).sum := by decide
  have hdescent : baseEnd_1119185 < baseStart_1119185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119309 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 8]
def baseStart_1119309 : Nat := 118140960795 + 1119309 * 2 ^ 59
def prefixEnd_1119309 : Nat := 4983230072969 + 3 ^ 40 * 1119309 * 2
def baseEnd_1119309 : Nat := 127720781756325873797755

theorem tailTrace_1119309 : CollatzResearch.WordTrace tailWord_1119309 prefixEnd_1119309 127720781756325873797755 := by
  unfold tailWord_1119309
  simp only [CollatzResearch.WordTrace]
  refine ⟨40824553101942130603064981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27216368734628087068709987 40824553101942130603064981)
  ·
    refine ⟨1913650926653537372018671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40824553101942130603064981 1913650926653537372018671)
    ·
      refine ⟨2870476389980306058028007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1913650926653537372018671 2870476389980306058028007)
      ·
        refine ⟨4305714584970459087042011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2870476389980306058028007 4305714584970459087042011)
        ·
          refine ⟨6458571877455688630563017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4305714584970459087042011 6458571877455688630563017)
          ·
            refine ⟨4843928908091766472922263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6458571877455688630563017 4843928908091766472922263)
            ·
              refine ⟨7265893362137649709383395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4843928908091766472922263 7265893362137649709383395)
              ·
                refine ⟨10898840043206474564075093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7265893362137649709383395 10898840043206474564075093)
                ·
                  refine ⟨127720781756325873797755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10898840043206474564075093 127720781756325873797755)
                  ·
                    rfl

theorem cell22_1119309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_1119309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119309 prefixEnd_1119309 := by exact prefixLift 1119309
  have htrace : WordTrace (prefixWord ++ tailWord_1119309) baseStart_1119309 baseEnd_1119309 := by
    simpa [prefixWord, tailWord_1119309, baseEnd_1119309] using wordTrace_append hprefix tailTrace_1119309
  have hstable : (prefixWord ++ tailWord_1119309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119309).length < 2 ^ (prefixWord ++ tailWord_1119309).sum := by decide
  have hdescent : baseEnd_1119309 < baseStart_1119309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119324 : List Nat := [2, 2, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1119324 : Nat := 118140960795 + 1119324 * 2 ^ 59
def prefixEnd_1119324 : Nat := 4983230072969 + 3 ^ 40 * 1119324 * 2
def baseEnd_1119324 : Nat := 383167480075522582268219

theorem tailTrace_1119324 : CollatzResearch.WordTrace tailWord_1119324 prefixEnd_1119324 383167480075522582268219 := by
  unfold tailWord_1119324
  simp only [CollatzResearch.WordTrace]
  refine ⟨20412550098443894082430513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27216733464591858776574017 20412550098443894082430513)
  ·
    refine ⟨15309412573832920561822885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20412550098443894082430513 15309412573832920561822885)
    ·
      refine ⟨2870514857593672605341791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15309412573832920561822885 2870514857593672605341791)
      ·
        refine ⟨4305772286390508908012687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2870514857593672605341791 4305772286390508908012687)
        ·
          refine ⟨6458658429585763362019031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4305772286390508908012687 6458658429585763362019031)
          ·
            refine ⟨9687987644378645043028547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6458658429585763362019031 9687987644378645043028547)
            ·
              refine ⟨14531981466567967564542821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9687987644378645043028547 14531981466567967564542821)
              ·
                refine ⟨2724746524981493918351779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14531981466567967564542821 2724746524981493918351779)
                ·
                  refine ⟨4087119787472240877527669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724746524981493918351779 4087119787472240877527669)
                  ·
                    refine ⟨383167480075522582268219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4087119787472240877527669 383167480075522582268219)
                    ·
                      rfl

theorem cell22_1119324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1119324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119324 prefixEnd_1119324 := by exact prefixLift 1119324
  have htrace : WordTrace (prefixWord ++ tailWord_1119324) baseStart_1119324 baseEnd_1119324 := by
    simpa [prefixWord, tailWord_1119324, baseEnd_1119324] using wordTrace_append hprefix tailTrace_1119324
  have hstable : (prefixWord ++ tailWord_1119324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119324).length < 2 ^ (prefixWord ++ tailWord_1119324).sum := by decide
  have hdescent : baseEnd_1119324 < baseStart_1119324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119337 : List Nat := [1, 2, 1, 1, 1, 7, 9]
def baseStart_1119337 : Nat := 118140960795 + 1119337 * 2 ^ 59
def prefixEnd_1119337 : Nat := 4983230072969 + 3 ^ 40 * 1119337 * 2
def baseEnd_1119337 : Nat := 14191552971896106729377

theorem tailTrace_1119337 : CollatzResearch.WordTrace tailWord_1119337 prefixEnd_1119337 14191552971896106729377 := by
  unfold tailWord_1119337
  simp only [CollatzResearch.WordTrace]
  refine ⟨40825574345840691385084265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27217049563893794256722843 40825574345840691385084265)
  ·
    refine ⟨30619180759380518538813199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40825574345840691385084265 30619180759380518538813199)
    ·
      refine ⟨45928771139070777808219799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30619180759380518538813199 45928771139070777808219799)
      ·
        refine ⟨68893156708606166712329699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45928771139070777808219799 68893156708606166712329699)
        ·
          refine ⟨103339735062909250068494549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68893156708606166712329699 103339735062909250068494549)
          ·
            refine ⟨2422025040536935548480341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 103339735062909250068494549 2422025040536935548480341)
            ·
              refine ⟨14191552971896106729377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2422025040536935548480341 14191552971896106729377)
              ·
                rfl

theorem cell22_1119337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 9].length) (baseStart_1119337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119337 prefixEnd_1119337 := by exact prefixLift 1119337
  have htrace : WordTrace (prefixWord ++ tailWord_1119337) baseStart_1119337 baseEnd_1119337 := by
    simpa [prefixWord, tailWord_1119337, baseEnd_1119337] using wordTrace_append hprefix tailTrace_1119337
  have hstable : (prefixWord ++ tailWord_1119337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119337).length < 2 ^ (prefixWord ++ tailWord_1119337).sum := by decide
  have hdescent : baseEnd_1119337 < baseStart_1119337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119341 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_1119341 : Nat := 118140960795 + 1119341 * 2 ^ 59
def prefixEnd_1119341 : Nat := 4983230072969 + 3 ^ 40 * 1119341 * 2
def baseEnd_1119341 : Nat := 383173299522940204593167

theorem tailTrace_1119341 : CollatzResearch.WordTrace tailWord_1119341 prefixEnd_1119341 383173299522940204593167 := by
  unfold tailWord_1119341
  simp only [CollatzResearch.WordTrace]
  refine ⟨40825720237826200068229877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27217146825217466712153251 40825720237826200068229877)
  ·
    refine ⟨3827411272296206256396551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40825720237826200068229877 3827411272296206256396551)
    ·
      refine ⟨5741116908444309384594827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3827411272296206256396551 5741116908444309384594827)
      ·
        refine ⟨8611675362666464076892241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5741116908444309384594827 8611675362666464076892241)
        ·
          refine ⟨6458756521999848057669181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8611675362666464076892241 6458756521999848057669181)
          ·
            refine ⟨2422033695749943021625943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6458756521999848057669181 2422033695749943021625943)
            ·
              refine ⟨3633050543624914532438915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2422033695749943021625943 3633050543624914532438915)
              ·
                refine ⟨5449575815437371798658373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3633050543624914532438915 5449575815437371798658373)
                ·
                  refine ⟨1021795465394507212248445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5449575815437371798658373 1021795465394507212248445)
                  ·
                    refine ⟨383173299522940204593167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1021795465394507212248445 383173299522940204593167)
                    ·
                      rfl

theorem cell22_1119341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_1119341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119341 prefixEnd_1119341 := by exact prefixLift 1119341
  have htrace : WordTrace (prefixWord ++ tailWord_1119341) baseStart_1119341 baseEnd_1119341 := by
    simpa [prefixWord, tailWord_1119341, baseEnd_1119341] using wordTrace_append hprefix tailTrace_1119341
  have hstable : (prefixWord ++ tailWord_1119341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119341).length < 2 ^ (prefixWord ++ tailWord_1119341).sum := by decide
  have hdescent : baseEnd_1119341 < baseStart_1119341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119491 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 2, 4]
def baseStart_1119491 : Nat := 118140960795 + 1119491 * 2 ^ 59
def prefixEnd_1119491 : Nat := 4983230072969 + 3 ^ 40 * 1119491 * 2
def baseEnd_1119491 : Nat := 383224647588389813342707

theorem tailTrace_1119491 : CollatzResearch.WordTrace tailWord_1119491 prefixEnd_1119491 383224647588389813342707 := by
  unfold tailWord_1119491
  simp only [CollatzResearch.WordTrace]
  refine ⟨40831191187282775686190327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27220794124855183790793551 40831191187282775686190327)
  ·
    refine ⟨61246786780924163529285491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40831191187282775686190327 61246786780924163529285491)
    ·
      refine ⟨91870180171386245293928237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61246786780924163529285491 91870180171386245293928237)
      ·
        refine ⟨34451317564269841985223089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91870180171386245293928237 34451317564269841985223089)
        ·
          refine ⟨25838488173202381488917317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34451317564269841985223089 25838488173202381488917317)
          ·
            refine ⟨4844716532475446529171997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25838488173202381488917317 4844716532475446529171997)
            ·
              refine ⟨1816768699678292448439499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4844716532475446529171997 1816768699678292448439499)
              ·
                refine ⟨2725153049517438672659249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1816768699678292448439499 2725153049517438672659249)
                ·
                  refine ⟨2043864787138079004494437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2725153049517438672659249 2043864787138079004494437)
                  ·
                    refine ⟨383224647588389813342707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2043864787138079004494437 383224647588389813342707)
                    ·
                      rfl

theorem cell22_1119491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 2, 4].length) (baseStart_1119491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119491 prefixEnd_1119491 := by exact prefixLift 1119491
  have htrace : WordTrace (prefixWord ++ tailWord_1119491) baseStart_1119491 baseEnd_1119491 := by
    simpa [prefixWord, tailWord_1119491, baseEnd_1119491] using wordTrace_append hprefix tailTrace_1119491
  have hstable : (prefixWord ++ tailWord_1119491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119491).length < 2 ^ (prefixWord ++ tailWord_1119491).sum := by decide
  have hdescent : baseEnd_1119491 < baseStart_1119491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119538 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_1119538 : Nat := 118140960795 + 1119538 * 2 ^ 59
def prefixEnd_1119538 : Nat := 4983230072969 + 3 ^ 40 * 1119538 * 2
def baseEnd_1119538 : Nat := 383240736648897357417563

theorem tailTrace_1119538 : CollatzResearch.WordTrace tailWord_1119538 prefixEnd_1119538 383240736648897357417563 := by
  unfold tailWord_1119538
  simp only [CollatzResearch.WordTrace]
  refine ⟨10208226354528125678287817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27221936945408335142100845 10208226354528125678287817)
  ·
    refine ⟨7656169765896094258715863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10208226354528125678287817 7656169765896094258715863)
    ·
      refine ⟨11484254648844141388073795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7656169765896094258715863 11484254648844141388073795)
      ·
        refine ⟨17226381973266212082110693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11484254648844141388073795 17226381973266212082110693)
        ·
          refine ⟨3229946619987414765395755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17226381973266212082110693 3229946619987414765395755)
          ·
            refine ⟨4844919929981122148093633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3229946619987414765395755 4844919929981122148093633)
            ·
              refine ⟨3633689947485841611070225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4844919929981122148093633 3633689947485841611070225)
              ·
                refine ⟨2725267460614381208302669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3633689947485841611070225 2725267460614381208302669)
                ·
                  refine ⟨1021975297730392953113501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2725267460614381208302669 1021975297730392953113501)
                  ·
                    refine ⟨383240736648897357417563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1021975297730392953113501 383240736648897357417563)
                    ·
                      rfl

theorem cell22_1119538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_1119538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119538 prefixEnd_1119538 := by exact prefixLift 1119538
  have htrace : WordTrace (prefixWord ++ tailWord_1119538) baseStart_1119538 baseEnd_1119538 := by
    simpa [prefixWord, tailWord_1119538, baseEnd_1119538] using wordTrace_append hprefix tailTrace_1119538
  have hstable : (prefixWord ++ tailWord_1119538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119538).length < 2 ^ (prefixWord ++ tailWord_1119538).sum := by decide
  have hdescent : baseEnd_1119538 < baseStart_1119538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119572 : List Nat := [2, 4, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_1119572 : Nat := 118140960795 + 1119572 * 2 ^ 59
def prefixEnd_1119572 : Nat := 4983230072969 + 3 ^ 40 * 1119572 * 2
def baseEnd_1119572 : Nat := 383252375543732602067459

theorem tailTrace_1119572 : CollatzResearch.WordTrace tailWord_1119572 prefixEnd_1119572 383252375543732602067459 := by
  unfold tailWord_1119572
  simp only [CollatzResearch.WordTrace]
  refine ⟨20417072749994663259944485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27222763666659551013259313 20417072749994663259944485)
  ·
    refine ⟨3828201140623999361239591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20417072749994663259944485 3828201140623999361239591)
    ·
      refine ⟨5742301710935999041859387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3828201140623999361239591 5742301710935999041859387)
      ·
        refine ⟨8613452566403998562789081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5742301710935999041859387 8613452566403998562789081)
        ·
          refine ⟨6460089424802998922091811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8613452566403998562789081 6460089424802998922091811)
          ·
            refine ⟨9690134137204498383137717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6460089424802998922091811 9690134137204498383137717)
            ·
              refine ⟨908450075362921723419161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9690134137204498383137717 908450075362921723419161)
              ·
                refine ⟨681337556522191292564371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 908450075362921723419161 681337556522191292564371)
                ·
                  refine ⟨1022006334783286938846557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681337556522191292564371 1022006334783286938846557)
                  ·
                    refine ⟨383252375543732602067459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1022006334783286938846557 383252375543732602067459)
                    ·
                      rfl

theorem cell22_1119572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_1119572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119572 prefixEnd_1119572 := by exact prefixLift 1119572
  have htrace : WordTrace (prefixWord ++ tailWord_1119572) baseStart_1119572 baseEnd_1119572 := by
    simpa [prefixWord, tailWord_1119572, baseEnd_1119572] using wordTrace_append hprefix tailTrace_1119572
  have hstable : (prefixWord ++ tailWord_1119572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119572).length < 2 ^ (prefixWord ++ tailWord_1119572).sum := by decide
  have hdescent : baseEnd_1119572 < baseStart_1119572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119611 : List Nat := [1, 1, 1, 1, 1, 6, 3, 2, 1, 5]
def baseStart_1119611 : Nat := 118140960795 + 1119611 * 2 ^ 59
def prefixEnd_1119611 : Nat := 4983230072969 + 3 ^ 40 * 1119611 * 2
def baseEnd_1119611 : Nat := 383265726040749500342339

theorem tailTrace_1119611 : CollatzResearch.WordTrace tailWord_1119611 prefixEnd_1119611 383265726040749500342339 := by
  unfold tailWord_1119611
  simp only [CollatzResearch.WordTrace]
  refine ⟨40835567946848036180558687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27223711964565357453705791 40835567946848036180558687)
  ·
    refine ⟨61253351920272054270838031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40835567946848036180558687 61253351920272054270838031)
    ·
      refine ⟨91880027880408081406257047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61253351920272054270838031 91880027880408081406257047)
      ·
        refine ⟨137820041820612122109385571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91880027880408081406257047 137820041820612122109385571)
        ·
          refine ⟨206730062730918183164078357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137820041820612122109385571 206730062730918183164078357)
          ·
            refine ⟨9690471690511789835816173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 206730062730918183164078357 9690471690511789835816173)
            ·
              refine ⟨3633926883941921188431065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9690471690511789835816173 3633926883941921188431065)
              ·
                refine ⟨2725445162956440891323299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3633926883941921188431065 2725445162956440891323299)
                ·
                  refine ⟨4088167744434661336984949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725445162956440891323299 4088167744434661336984949)
                  ·
                    refine ⟨383265726040749500342339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4088167744434661336984949 383265726040749500342339)
                    ·
                      rfl

theorem cell22_1119611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 5].length) (baseStart_1119611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119611 prefixEnd_1119611 := by exact prefixLift 1119611
  have htrace : WordTrace (prefixWord ++ tailWord_1119611) baseStart_1119611 baseEnd_1119611 := by
    simpa [prefixWord, tailWord_1119611, baseEnd_1119611] using wordTrace_append hprefix tailTrace_1119611
  have hstable : (prefixWord ++ tailWord_1119611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119611).length < 2 ^ (prefixWord ++ tailWord_1119611).sum := by decide
  have hdescent : baseEnd_1119611 < baseStart_1119611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119613 : List Nat := [1, 4, 1, 1, 2, 2, 2, 5, 4]
def baseStart_1119613 : Nat := 118140960795 + 1119613 * 2 ^ 59
def prefixEnd_1119613 : Nat := 4983230072969 + 3 ^ 40 * 1119613 * 2
def baseEnd_1119613 : Nat := 127755470227207387264111

theorem tailTrace_1119613 : CollatzResearch.WordTrace tailWord_1119613 prefixEnd_1119613 127755470227207387264111 := by
  unfold tailWord_1119613
  simp only [CollatzResearch.WordTrace]
  refine ⟨40835640892840790522131493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27223760595227193681420995 40835640892840790522131493)
  ·
    refine ⟨7656682667407648222899655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40835640892840790522131493 7656682667407648222899655)
    ·
      refine ⟨11485024001111472334349483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7656682667407648222899655 11485024001111472334349483)
      ·
        refine ⟨17227536001667208501524225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11485024001111472334349483 17227536001667208501524225)
        ·
          refine ⟨12920652001250406376143169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17227536001667208501524225 12920652001250406376143169)
          ·
            refine ⟨9690489000937804782107377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12920652001250406376143169 9690489000937804782107377)
            ·
              refine ⟨7267866750703353586580533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9690489000937804782107377 7267866750703353586580533)
              ·
                refine ⟨681362507878439398741925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7267866750703353586580533 681362507878439398741925)
                ·
                  refine ⟨127755470227207387264111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 681362507878439398741925 127755470227207387264111)
                  ·
                    rfl

theorem cell22_1119613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_1119613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119613 prefixEnd_1119613 := by exact prefixLift 1119613
  have htrace : WordTrace (prefixWord ++ tailWord_1119613) baseStart_1119613 baseEnd_1119613 := by
    simpa [prefixWord, tailWord_1119613, baseEnd_1119613] using wordTrace_append hprefix tailTrace_1119613
  have hstable : (prefixWord ++ tailWord_1119613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119613).length < 2 ^ (prefixWord ++ tailWord_1119613).sum := by decide
  have hdescent : baseEnd_1119613 < baseStart_1119613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119641 : List Nat := [1, 2, 1, 2, 1, 5, 3, 7]
def baseStart_1119641 : Nat := 118140960795 + 1119641 * 2 ^ 59
def prefixEnd_1119641 : Nat := 4983230072969 + 3 ^ 40 * 1119641 * 2
def baseEnd_1119641 : Nat := 42586221739315491343583

theorem tailTrace_1119641 : CollatzResearch.WordTrace tailWord_1119641 prefixEnd_1119641 42586221739315491343583 := by
  unfold tailWord_1119641
  simp only [CollatzResearch.WordTrace]
  refine ⟨40836662136739351304150777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27224441424492900869433851 40836662136739351304150777)
  ·
    refine ⟨30627496602554513478113083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40836662136739351304150777 30627496602554513478113083)
    ·
      refine ⟨45941244903831770217169625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30627496602554513478113083 45941244903831770217169625)
      ·
        refine ⟨34455933677873827662877219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45941244903831770217169625 34455933677873827662877219)
        ·
          refine ⟨51683900516810741494315829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34455933677873827662877219 51683900516810741494315829)
          ·
            refine ⟨4845365673451007015092109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51683900516810741494315829 4845365673451007015092109)
            ·
              refine ⟨1817012127544127630659541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4845365673451007015092109 1817012127544127630659541)
              ·
                refine ⟨42586221739315491343583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1817012127544127630659541 42586221739315491343583)
                ·
                  rfl

theorem cell22_1119641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 7].length) (baseStart_1119641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119641 prefixEnd_1119641 := by exact prefixLift 1119641
  have htrace : WordTrace (prefixWord ++ tailWord_1119641) baseStart_1119641 baseEnd_1119641 := by
    simpa [prefixWord, tailWord_1119641, baseEnd_1119641] using wordTrace_append hprefix tailTrace_1119641
  have hstable : (prefixWord ++ tailWord_1119641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119641).length < 2 ^ (prefixWord ++ tailWord_1119641).sum := by decide
  have hdescent : baseEnd_1119641 < baseStart_1119641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119645 : List Nat := [1, 4, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1119645 : Nat := 118140960795 + 1119645 * 2 ^ 59
def prefixEnd_1119645 : Nat := 4983230072969 + 3 ^ 40 * 1119645 * 2
def baseEnd_1119645 : Nat := 383277364935584744992235

theorem tailTrace_1119645 : CollatzResearch.WordTrace tailWord_1119645 prefixEnd_1119645 383277364935584744992235 := by
  unfold tailWord_1119645
  simp only [CollatzResearch.WordTrace]
  refine ⟨40836808028724859987296389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27224538685816573324864259 40836808028724859987296389)
  ·
    refine ⟨7656901505385911247618073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40836808028724859987296389 7656901505385911247618073)
    ·
      refine ⟨5742676129039433435713555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7656901505385911247618073 5742676129039433435713555)
      ·
        refine ⟨8614014193559150153570333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5742676129039433435713555 8614014193559150153570333)
        ·
          refine ⟨3230255322584681307588875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8614014193559150153570333 3230255322584681307588875)
          ·
            refine ⟨4845382983877021961383313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3230255322584681307588875 4845382983877021961383313)
            ·
              refine ⟨3634037237907766471037485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4845382983877021961383313 3634037237907766471037485)
              ·
                refine ⟨1362763964215412426639057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3634037237907766471037485 1362763964215412426639057)
                ·
                  refine ⟨1022072973161559319979293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1362763964215412426639057 1022072973161559319979293)
                  ·
                    refine ⟨383277364935584744992235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1022072973161559319979293 383277364935584744992235)
                    ·
                      rfl

theorem cell22_1119645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1119645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119645 prefixEnd_1119645 := by exact prefixLift 1119645
  have htrace : WordTrace (prefixWord ++ tailWord_1119645) baseStart_1119645 baseEnd_1119645 := by
    simpa [prefixWord, tailWord_1119645, baseEnd_1119645] using wordTrace_append hprefix tailTrace_1119645
  have hstable : (prefixWord ++ tailWord_1119645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119645).length < 2 ^ (prefixWord ++ tailWord_1119645).sum := by decide
  have hdescent : baseEnd_1119645 < baseStart_1119645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119690 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 3, 3]
def baseStart_1119690 : Nat := 118140960795 + 1119690 * 2 ^ 59
def prefixEnd_1119690 : Nat := 4983230072969 + 3 ^ 40 * 1119690 * 2
def baseEnd_1119690 : Nat := 383292769355219627617097

theorem tailTrace_1119690 : CollatzResearch.WordTrace tailWord_1119690 prefixEnd_1119690 383292769355219627617097 := by
  unfold tailWord_1119690
  simp only [CollatzResearch.WordTrace]
  refine ⟨10209612328390458168171131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27225632875707888448456349 10209612328390458168171131)
  ·
    refine ⟨15314418492585687252256697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10209612328390458168171131 15314418492585687252256697)
    ·
      refine ⟨11485813869439265439192523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15314418492585687252256697 11485813869439265439192523)
      ·
        refine ⟨17228720804158898158788785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11485813869439265439192523 17228720804158898158788785)
        ·
          refine ⟨12921540603119173619091589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17228720804158898158788785 12921540603119173619091589)
          ·
            refine ⟨2422788863084845053579673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12921540603119173619091589 2422788863084845053579673)
            ·
              refine ⟨1817091647313633790184755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2422788863084845053579673 1817091647313633790184755)
              ·
                refine ⟨2725637470970450685277133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817091647313633790184755 2725637470970450685277133)
                ·
                  refine ⟨1022114051613919006978925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2725637470970450685277133 1022114051613919006978925)
                  ·
                    refine ⟨383292769355219627617097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1022114051613919006978925 383292769355219627617097)
                    ·
                      rfl

theorem cell22_1119690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_1119690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119690 prefixEnd_1119690 := by exact prefixLift 1119690
  have htrace : WordTrace (prefixWord ++ tailWord_1119690) baseStart_1119690 baseEnd_1119690 := by
    simpa [prefixWord, tailWord_1119690, baseEnd_1119690] using wordTrace_append hprefix tailTrace_1119690
  have hstable : (prefixWord ++ tailWord_1119690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119690).length < 2 ^ (prefixWord ++ tailWord_1119690).sum := by decide
  have hdescent : baseEnd_1119690 < baseStart_1119690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119716 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_1119716 : Nat := 118140960795 + 1119716 * 2 ^ 59
def prefixEnd_1119716 : Nat := 4983230072969 + 3 ^ 40 * 1119716 * 2
def baseEnd_1119716 : Nat := 383301669686564226467017

theorem tailTrace_1119716 : CollatzResearch.WordTrace tailWord_1119716 prefixEnd_1119716 383301669686564226467017 := by
  unfold tailWord_1119716
  simp only [CollatzResearch.WordTrace]
  refine ⟨20419698805733819556565501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27226265074311759408754001 20419698805733819556565501)
  ·
    refine ⟨7657387052150182333712063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20419698805733819556565501 7657387052150182333712063)
    ·
      refine ⟨11486080578225273500568095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7657387052150182333712063 11486080578225273500568095)
      ·
        refine ⟨17229120867337910250852143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11486080578225273500568095 17229120867337910250852143)
        ·
          refine ⟨25843681301006865376278215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17229120867337910250852143 25843681301006865376278215)
          ·
            refine ⟨38765521951510298064417323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25843681301006865376278215 38765521951510298064417323)
            ·
              refine ⟨58148282927265447096625985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38765521951510298064417323 58148282927265447096625985)
              ·
                refine ⟨43611212195449085322469489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58148282927265447096625985 43611212195449085322469489)
                ·
                  refine ⟨32708409146586813991852117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43611212195449085322469489 32708409146586813991852117)
                  ·
                    refine ⟨383301669686564226467017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32708409146586813991852117 383301669686564226467017)
                    ·
                      rfl

theorem cell22_1119716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_1119716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119716 prefixEnd_1119716 := by exact prefixLift 1119716
  have htrace : WordTrace (prefixWord ++ tailWord_1119716) baseStart_1119716 baseEnd_1119716 := by
    simpa [prefixWord, tailWord_1119716, baseEnd_1119716] using wordTrace_append hprefix tailTrace_1119716
  have hstable : (prefixWord ++ tailWord_1119716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119716).length < 2 ^ (prefixWord ++ tailWord_1119716).sum := by decide
  have hdescent : baseEnd_1119716 < baseStart_1119716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119778 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1119778 : Nat := 118140960795 + 1119778 * 2 ^ 59
def prefixEnd_1119778 : Nat := 4983230072969 + 3 ^ 40 * 1119778 * 2
def baseEnd_1119778 : Nat := 383322893553616731416827

theorem tailTrace_1119778 : CollatzResearch.WordTrace tailWord_1119778 prefixEnd_1119778 383322893553616731416827 := by
  unfold tailWord_1119778
  simp only [CollatzResearch.WordTrace]
  refine ⟨10210414734310755925471997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27227772624828682467925325 10210414734310755925471997)
  ·
    refine ⟨3828905525366533472051999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10210414734310755925471997 3828905525366533472051999)
    ·
      refine ⟨5743358288049800208077999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3828905525366533472051999 5743358288049800208077999)
      ·
        refine ⟨8615037432074700312116999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5743358288049800208077999 8615037432074700312116999)
        ·
          refine ⟨12922556148112050468175499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8615037432074700312116999 12922556148112050468175499)
          ·
            refine ⟨19383834222168075702263249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12922556148112050468175499 19383834222168075702263249)
            ·
              refine ⟨14537875666626056776697437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19383834222168075702263249 14537875666626056776697437)
              ·
                refine ⟨5451703374984771291261539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14537875666626056776697437 5451703374984771291261539)
                ·
                  refine ⟨8177555062477156936892309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5451703374984771291261539 8177555062477156936892309)
                  ·
                    refine ⟨383322893553616731416827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8177555062477156936892309 383322893553616731416827)
                    ·
                      rfl

theorem cell22_1119778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1119778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119778 prefixEnd_1119778 := by exact prefixLift 1119778
  have htrace : WordTrace (prefixWord ++ tailWord_1119778) baseStart_1119778 baseEnd_1119778 := by
    simpa [prefixWord, tailWord_1119778, baseEnd_1119778] using wordTrace_append hprefix tailTrace_1119778
  have hstable : (prefixWord ++ tailWord_1119778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119778).length < 2 ^ (prefixWord ++ tailWord_1119778).sum := by decide
  have hdescent : baseEnd_1119778 < baseStart_1119778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119784 : List Nat := [2, 1, 5, 2, 2, 1, 3, 1, 1, 4]
def baseStart_1119784 : Nat := 118140960795 + 1119784 * 2 ^ 59
def prefixEnd_1119784 : Nat := 4983230072969 + 3 ^ 40 * 1119784 * 2
def baseEnd_1119784 : Nat := 383324947476234715766809

theorem tailTrace_1119784 : CollatzResearch.WordTrace tailWord_1119784 prefixEnd_1119784 383324947476234715766809 := by
  unfold tailWord_1119784
  simp only [CollatzResearch.WordTrace]
  refine ⟨20420938887610643363303203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27227918516814191151070937 20420938887610643363303203)
  ·
    refine ⟨30631408331415965044954805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20420938887610643363303203 30631408331415965044954805)
    ·
      refine ⟨2871694531070246722964513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30631408331415965044954805 2871694531070246722964513)
      ·
        refine ⟨2153770898302685042223385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2871694531070246722964513 2153770898302685042223385)
        ·
          refine ⟨1615328173727013781667539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2153770898302685042223385 1615328173727013781667539)
          ·
            refine ⟨2422992260590520672501309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615328173727013781667539 2422992260590520672501309)
            ·
              refine ⟨908622097721445252187991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2422992260590520672501309 908622097721445252187991)
              ·
                refine ⟨1362933146582167878281987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 908622097721445252187991 1362933146582167878281987)
                ·
                  refine ⟨2044399719873251817422981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1362933146582167878281987 2044399719873251817422981)
                  ·
                    refine ⟨383324947476234715766809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2044399719873251817422981 383324947476234715766809)
                    ·
                      rfl

theorem cell22_1119784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_1119784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119784 prefixEnd_1119784 := by exact prefixLift 1119784
  have htrace : WordTrace (prefixWord ++ tailWord_1119784) baseStart_1119784 baseEnd_1119784 := by
    simpa [prefixWord, tailWord_1119784, baseEnd_1119784] using wordTrace_append hprefix tailTrace_1119784
  have hstable : (prefixWord ++ tailWord_1119784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119784).length < 2 ^ (prefixWord ++ tailWord_1119784).sum := by decide
  have hdescent : baseEnd_1119784 < baseStart_1119784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119797 : List Nat := [1, 3, 3, 1, 1, 4, 2, 2, 2, 3]
def baseStart_1119797 : Nat := 118140960795 + 1119797 * 2 ^ 59
def prefixEnd_1119797 : Nat := 4983230072969 + 3 ^ 40 * 1119797 * 2
def baseEnd_1119797 : Nat := 383329397641907015191769

theorem tailTrace_1119797 : CollatzResearch.WordTrace tailWord_1119797 prefixEnd_1119797 383329397641907015191769 := by
  unfold tailWord_1119797
  simp only [CollatzResearch.WordTrace]
  refine ⟨40842351924174189946829645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27228234616116126631219763 40842351924174189946829645)
  ·
    refine ⟨15315881971565321230061117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40842351924174189946829645 15315881971565321230061117)
    ·
      refine ⟨5743455739336995461272919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15315881971565321230061117 5743455739336995461272919)
      ·
        refine ⟨8615183609005493191909379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5743455739336995461272919 8615183609005493191909379)
        ·
          refine ⟨12922775413508239787864069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8615183609005493191909379 12922775413508239787864069)
          ·
            refine ⟨2423020390032794960224513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12922775413508239787864069 2423020390032794960224513)
            ·
              refine ⟨1817265292524596220168385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2423020390032794960224513 1817265292524596220168385)
              ·
                refine ⟨1362948969393447165126289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1817265292524596220168385 1362948969393447165126289)
                ·
                  refine ⟨1022211727045085373844717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1362948969393447165126289 1022211727045085373844717)
                  ·
                    refine ⟨383329397641907015191769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1022211727045085373844717 383329397641907015191769)
                    ·
                      rfl

theorem cell22_1119797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_1119797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119797 prefixEnd_1119797 := by exact prefixLift 1119797
  have htrace : WordTrace (prefixWord ++ tailWord_1119797) baseStart_1119797 baseEnd_1119797 := by
    simpa [prefixWord, tailWord_1119797, baseEnd_1119797] using wordTrace_append hprefix tailTrace_1119797
  have hstable : (prefixWord ++ tailWord_1119797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119797).length < 2 ^ (prefixWord ++ tailWord_1119797).sum := by decide
  have hdescent : baseEnd_1119797 < baseStart_1119797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119814 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1119814 : Nat := 118140960795 + 1119814 * 2 ^ 59
def prefixEnd_1119814 : Nat := 4983230072969 + 3 ^ 40 * 1119814 * 2
def baseEnd_1119814 : Nat := 383335217089324637516717

theorem tailTrace_1119814 : CollatzResearch.WordTrace tailWord_1119814 prefixEnd_1119814 383335217089324637516717 := by
  unfold tailWord_1119814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1276342873909768807818703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27228647976741734566798997 1276342873909768807818703)
  ·
    refine ⟨1914514310864653211728055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1276342873909768807818703 1914514310864653211728055)
    ·
      refine ⟨2871771466296979817592083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1914514310864653211728055 2871771466296979817592083)
      ·
        refine ⟨4307657199445469726388125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2871771466296979817592083 4307657199445469726388125)
        ·
          refine ⟨1615371449792051147395547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4307657199445469726388125 1615371449792051147395547)
          ·
            refine ⟨2423057174688076721093321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1615371449792051147395547 2423057174688076721093321)
            ·
              refine ⟨1817292881016057540819991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2423057174688076721093321 1817292881016057540819991)
              ·
                refine ⟨2725939321524086311229987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817292881016057540819991 2725939321524086311229987)
                ·
                  refine ⟨4088908982286129466844981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2725939321524086311229987 4088908982286129466844981)
                  ·
                    refine ⟨383335217089324637516717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4088908982286129466844981 383335217089324637516717)
                    ·
                      rfl

theorem cell22_1119814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1119814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119814 prefixEnd_1119814 := by exact prefixLift 1119814
  have htrace : WordTrace (prefixWord ++ tailWord_1119814) baseStart_1119814 baseEnd_1119814 := by
    simpa [prefixWord, tailWord_1119814, baseEnd_1119814] using wordTrace_append hprefix tailTrace_1119814
  have hstable : (prefixWord ++ tailWord_1119814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119814).length < 2 ^ (prefixWord ++ tailWord_1119814).sum := by decide
  have hdescent : baseEnd_1119814 < baseStart_1119814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119825 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 3, 3]
def baseStart_1119825 : Nat := 118140960795 + 1119825 * 2 ^ 59
def prefixEnd_1119825 : Nat := 4983230072969 + 3 ^ 40 * 1119825 * 2
def baseEnd_1119825 : Nat := 383338982614124275491683

theorem tailTrace_1119825 : CollatzResearch.WordTrace tailWord_1119825 prefixEnd_1119825 383338982614124275491683 := by
  unfold tailWord_1119825
  simp only [CollatzResearch.WordTrace]
  refine ⟨40843373168072750728848929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27228915445381833819232619 40843373168072750728848929)
  ·
    refine ⟨30632529876054563046636697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40843373168072750728848929 30632529876054563046636697)
    ·
      refine ⟨22974397407040922284977523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30632529876054563046636697 22974397407040922284977523)
      ·
        refine ⟨34461596110561383427466285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22974397407040922284977523 34461596110561383427466285)
        ·
          refine ⟨12923098541460518785299857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34461596110561383427466285 12923098541460518785299857)
          ·
            refine ⟨9692323906095389088974893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12923098541460518785299857 9692323906095389088974893)
            ·
              refine ⟨3634621464785770908365585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9692323906095389088974893 3634621464785770908365585)
              ·
                refine ⟨2725966098589328181274189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3634621464785770908365585 2725966098589328181274189)
                ·
                  refine ⟨1022237286970998067977821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2725966098589328181274189 1022237286970998067977821)
                  ·
                    refine ⟨383338982614124275491683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1022237286970998067977821 383338982614124275491683)
                    ·
                      rfl

theorem cell22_1119825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_1119825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119825 prefixEnd_1119825 := by exact prefixLift 1119825
  have htrace : WordTrace (prefixWord ++ tailWord_1119825) baseStart_1119825 baseEnd_1119825 := by
    simpa [prefixWord, tailWord_1119825, baseEnd_1119825] using wordTrace_append hprefix tailTrace_1119825
  have hstable : (prefixWord ++ tailWord_1119825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119825).length < 2 ^ (prefixWord ++ tailWord_1119825).sum := by decide
  have hdescent : baseEnd_1119825 < baseStart_1119825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119883 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 6]
def baseStart_1119883 : Nat := 118140960795 + 1119883 * 2 ^ 59
def prefixEnd_1119883 : Nat := 4983230072969 + 3 ^ 40 * 1119883 * 2
def baseEnd_1119883 : Nat := 127786279066477152513835

theorem tailTrace_1119883 : CollatzResearch.WordTrace tailWord_1119883 prefixEnd_1119883 127786279066477152513835 := by
  unfold tailWord_1119883
  simp only [CollatzResearch.WordTrace]
  refine ⟨40845488601862626634460303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27230325734575084422973535 40845488601862626634460303)
  ·
    refine ⟨61268232902793939951690455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40845488601862626634460303 61268232902793939951690455)
    ·
      refine ⟨91902349354190909927535683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61268232902793939951690455 91902349354190909927535683)
      ·
        refine ⟨137853524031286364891303525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91902349354190909927535683 137853524031286364891303525)
        ·
          refine ⟨25847535755866193417119411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137853524031286364891303525 25847535755866193417119411)
          ·
            refine ⟨38771303633799290125679117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25847535755866193417119411 38771303633799290125679117)
            ·
              refine ⟨14539238862674733797129669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38771303633799290125679117 14539238862674733797129669)
              ·
                refine ⟨2726107286751512586961813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14539238862674733797129669 2726107286751512586961813)
                ·
                  refine ⟨127786279066477152513835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2726107286751512586961813 127786279066477152513835)
                  ·
                    rfl

theorem cell22_1119883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 6].length) (baseStart_1119883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119883 prefixEnd_1119883 := by exact prefixLift 1119883
  have htrace : WordTrace (prefixWord ++ tailWord_1119883) baseStart_1119883 baseEnd_1119883 := by
    simpa [prefixWord, tailWord_1119883, baseEnd_1119883] using wordTrace_append hprefix tailTrace_1119883
  have hstable : (prefixWord ++ tailWord_1119883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119883).length < 2 ^ (prefixWord ++ tailWord_1119883).sum := by decide
  have hdescent : baseEnd_1119883 < baseStart_1119883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1119949 : List Nat := [1, 6, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1119949 : Nat := 118140960795 + 1119949 * 2 ^ 59
def prefixEnd_1119949 : Nat := 4983230072969 + 3 ^ 40 * 1119949 * 2
def baseEnd_1119949 : Nat := 383381430348229285391303

theorem tailTrace_1119949 : CollatzResearch.WordTrace tailWord_1119949 prefixEnd_1119949 383381430348229285391303 := by
  unfold tailWord_1119949
  simp only [CollatzResearch.WordTrace]
  refine ⟨40847895819623519906362901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27231930546415679937575267 40847895819623519906362901)
  ·
    refine ⟨1914745116544852495610761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40847895819623519906362901 1914745116544852495610761)
    ·
      refine ⟨1436058837408639371708071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1914745116544852495610761 1436058837408639371708071)
      ·
        refine ⟨2154088256112959057562107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1436058837408639371708071 2154088256112959057562107)
        ·
          refine ⟨3231132384169438586343161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2154088256112959057562107 3231132384169438586343161)
          ·
            refine ⟨2423349288127078939757371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3231132384169438586343161 2423349288127078939757371)
            ·
              refine ⟨3635023932190618409636057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2423349288127078939757371 3635023932190618409636057)
              ·
                refine ⟨2726267949142963807227043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3635023932190618409636057 2726267949142963807227043)
                ·
                  refine ⟨4089401923714445710840565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2726267949142963807227043 4089401923714445710840565)
                  ·
                    refine ⟨383381430348229285391303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4089401923714445710840565 383381430348229285391303)
                    ·
                      rfl

theorem cell22_1119949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1119949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1119949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1119949 prefixEnd_1119949 := by exact prefixLift 1119949
  have htrace : WordTrace (prefixWord ++ tailWord_1119949) baseStart_1119949 baseEnd_1119949 := by
    simpa [prefixWord, tailWord_1119949, baseEnd_1119949] using wordTrace_append hprefix tailTrace_1119949
  have hstable : (prefixWord ++ tailWord_1119949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1119949).length < 2 ^ (prefixWord ++ tailWord_1119949).sum := by decide
  have hdescent : baseEnd_1119949 < baseStart_1119949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1119949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120035 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 6]
def baseStart_1120035 : Nat := 118140960795 + 1120035 * 2 ^ 59
def prefixEnd_1120035 : Nat := 4983230072969 + 3 ^ 40 * 1120035 * 2
def baseEnd_1120035 : Nat := 127803623301917909247013

theorem tailTrace_1120035 : CollatzResearch.WordTrace tailWord_1120035 prefixEnd_1120035 127803623301917909247013 := by
  unfold tailWord_1120035
  simp only [CollatzResearch.WordTrace]
  refine ⟨40851032497311956593993559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27234021664874637729329039 40851032497311956593993559)
  ·
    refine ⟨61276548745967934890990339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40851032497311956593993559 61276548745967934890990339)
    ·
      refine ⟨91914823118951902336485509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61276548745967934890990339 91914823118951902336485509)
      ·
        refine ⟨17234029334803481688091033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91914823118951902336485509 17234029334803481688091033)
        ·
          refine ⟨12925522001102611266068275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17234029334803481688091033 12925522001102611266068275)
          ·
            refine ⟨19388283001653916899102413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12925522001102611266068275 19388283001653916899102413)
            ·
              refine ⟨7270606125620218837163405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19388283001653916899102413 7270606125620218837163405)
              ·
                refine ⟨2726477297107582063936277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7270606125620218837163405 2726477297107582063936277)
                ·
                  refine ⟨127803623301917909247013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2726477297107582063936277 127803623301917909247013)
                  ·
                    rfl

theorem cell22_1120035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 6].length) (baseStart_1120035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120035 prefixEnd_1120035 := by exact prefixLift 1120035
  have htrace : WordTrace (prefixWord ++ tailWord_1120035) baseStart_1120035 baseEnd_1120035 := by
    simpa [prefixWord, tailWord_1120035, baseEnd_1120035] using wordTrace_append hprefix tailTrace_1120035
  have hstable : (prefixWord ++ tailWord_1120035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120035).length < 2 ^ (prefixWord ++ tailWord_1120035).sum := by decide
  have hdescent : baseEnd_1120035 < baseStart_1120035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120067 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 4, 3]
def baseStart_1120067 : Nat := 118140960795 + 1120067 * 2 ^ 59
def prefixEnd_1120067 : Nat := 4983230072969 + 3 ^ 40 * 1120067 * 2
def baseEnd_1120067 : Nat := 383421824159716310940941

theorem tailTrace_1120067 : CollatzResearch.WordTrace tailWord_1120067 prefixEnd_1120067 383421824159716310940941 := by
  unfold tailWord_1120067
  simp only [CollatzResearch.WordTrace]
  refine ⟨40852199633196026059158455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27234799755464017372772303 40852199633196026059158455)
  ·
    refine ⟨61278299449794039088737683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40852199633196026059158455 61278299449794039088737683)
    ·
      refine ⟨91917449174691058633106525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61278299449794039088737683 91917449174691058633106525)
      ·
        refine ⟨34469043440509146987414947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91917449174691058633106525 34469043440509146987414947)
        ·
          refine ⟨51703565160763720481122421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34469043440509146987414947 51703565160763720481122421)
          ·
            refine ⟨4847209233821598795105227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51703565160763720481122421 4847209233821598795105227)
            ·
              refine ⟨7270813850732398192657841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4847209233821598795105227 7270813850732398192657841)
              ·
                refine ⟨5453110388049298644493381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7270813850732398192657841 5453110388049298644493381)
                ·
                  refine ⟨1022458197759243495842509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5453110388049298644493381 1022458197759243495842509)
                  ·
                    refine ⟨383421824159716310940941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1022458197759243495842509 383421824159716310940941)
                    ·
                      rfl

theorem cell22_1120067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 4, 3].length) (baseStart_1120067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120067 prefixEnd_1120067 := by exact prefixLift 1120067
  have htrace : WordTrace (prefixWord ++ tailWord_1120067) baseStart_1120067 baseEnd_1120067 := by
    simpa [prefixWord, tailWord_1120067, baseEnd_1120067] using wordTrace_append hprefix tailTrace_1120067
  have hstable : (prefixWord ++ tailWord_1120067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120067).length < 2 ^ (prefixWord ++ tailWord_1120067).sum := by decide
  have hdescent : baseEnd_1120067 < baseStart_1120067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120082 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1120082 : Nat := 118140960795 + 1120082 * 2 ^ 59
def prefixEnd_1120082 : Nat := 4983230072969 + 3 ^ 40 * 1120082 * 2
def baseEnd_1120082 : Nat := 383426958966261271815895

theorem tailTrace_1120082 : CollatzResearch.WordTrace tailWord_1120082 prefixEnd_1120082 383426958966261271815895 := by
  unfold tailWord_1120082
  simp only [CollatzResearch.WordTrace]
  refine ⟨10213186682035420905238625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27235164485427789080636333 10213186682035420905238625)
  ·
    refine ⟨7659890011526565678928969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10213186682035420905238625 7659890011526565678928969)
    ·
      refine ⟨5744917508644924259196727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7659890011526565678928969 5744917508644924259196727)
      ·
        refine ⟨8617376262967386388795091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5744917508644924259196727 8617376262967386388795091)
        ·
          refine ⟨12926064394451079583192637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8617376262967386388795091 12926064394451079583192637)
          ·
            refine ⟨4847274147919154843697239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12926064394451079583192637 4847274147919154843697239)
            ·
              refine ⟨7270911221878732265545859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4847274147919154843697239 7270911221878732265545859)
              ·
                refine ⟨10906366832818098398318789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7270911221878732265545859 10906366832818098398318789)
                ·
                  refine ⟨2044943781153393449684773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10906366832818098398318789 2044943781153393449684773)
                  ·
                    refine ⟨383426958966261271815895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2044943781153393449684773 383426958966261271815895)
                    ·
                      rfl

theorem cell22_1120082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1120082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120082 prefixEnd_1120082 := by exact prefixLift 1120082
  have htrace : WordTrace (prefixWord ++ tailWord_1120082) baseStart_1120082 baseEnd_1120082 := by
    simpa [prefixWord, tailWord_1120082, baseEnd_1120082] using wordTrace_append hprefix tailTrace_1120082
  have hstable : (prefixWord ++ tailWord_1120082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120082).length < 2 ^ (prefixWord ++ tailWord_1120082).sum := by decide
  have hdescent : baseEnd_1120082 < baseStart_1120082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120084 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_1120084 : Nat := 118140960795 + 1120084 * 2 ^ 59
def prefixEnd_1120084 : Nat := 4983230072969 + 3 ^ 40 * 1120084 * 2
def baseEnd_1120084 : Nat := 383427643607133933265889

theorem tailTrace_1120084 : CollatzResearch.WordTrace tailWord_1120084 prefixEnd_1120084 383427643607133933265889 := by
  unfold tailWord_1120084
  simp only [CollatzResearch.WordTrace]
  refine ⟨20426409837067218981263653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27235213116089625308351537 20426409837067218981263653)
  ·
    refine ⟨3829951844450103558986935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20426409837067218981263653 3829951844450103558986935)
    ·
      refine ⟨5744927766675155338480403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3829951844450103558986935 5744927766675155338480403)
      ·
        refine ⟨8617391650012733007720605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5744927766675155338480403 8617391650012733007720605)
        ·
          refine ⟨3231521868754774877895227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8617391650012733007720605 3231521868754774877895227)
          ·
            refine ⟨4847282803132162316842841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3231521868754774877895227 4847282803132162316842841)
            ·
              refine ⟨3635462102349121737632131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4847282803132162316842841 3635462102349121737632131)
              ·
                refine ⟨5453193153523682606448197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3635462102349121737632131 5453193153523682606448197)
                ·
                  refine ⟨1022473716285690488709037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5453193153523682606448197 1022473716285690488709037)
                  ·
                    refine ⟨383427643607133933265889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1022473716285690488709037 383427643607133933265889)
                    ·
                      rfl

theorem cell22_1120084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_1120084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120084 prefixEnd_1120084 := by exact prefixLift 1120084
  have htrace : WordTrace (prefixWord ++ tailWord_1120084) baseStart_1120084 baseEnd_1120084 := by
    simpa [prefixWord, tailWord_1120084, baseEnd_1120084] using wordTrace_append hprefix tailTrace_1120084
  have hstable : (prefixWord ++ tailWord_1120084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120084).length < 2 ^ (prefixWord ++ tailWord_1120084).sum := by decide
  have hdescent : baseEnd_1120084 < baseStart_1120084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120112 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 5, 3]
def baseStart_1120112 : Nat := 118140960795 + 1120112 * 2 ^ 59
def prefixEnd_1120112 : Nat := 4983230072969 + 3 ^ 40 * 1120112 * 2
def baseEnd_1120112 : Nat := 383437228579351193565803

theorem tailTrace_1120112 : CollatzResearch.WordTrace tailWord_1120112 prefixEnd_1120112 383437228579351193565803 := by
  unfold tailWord_1120112
  simp only [CollatzResearch.WordTrace]
  refine ⟨20426920459016499372273295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27235893945355332496364393 20426920459016499372273295)
  ·
    refine ⟨30640380688524749058409943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20426920459016499372273295 30640380688524749058409943)
    ·
      refine ⟨45960571032787123587614915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30640380688524749058409943 45960571032787123587614915)
      ·
        refine ⟨68940856549180685381422373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45960571032787123587614915 68940856549180685381422373)
        ·
          refine ⟨12926410602971378509016695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68940856549180685381422373 12926410602971378509016695)
          ·
            refine ⟨19389615904457067763525043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12926410602971378509016695 19389615904457067763525043)
            ·
              refine ⟨29084423856685601645287565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19389615904457067763525043 29084423856685601645287565)
              ·
                refine ⟨10906658946257100616982837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29084423856685601645287565 10906658946257100616982837)
                ·
                  refine ⟨1022499276211603182842141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10906658946257100616982837 1022499276211603182842141)
                  ·
                    refine ⟨383437228579351193565803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1022499276211603182842141 383437228579351193565803)
                    ·
                      rfl

theorem cell22_1120112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 5, 3].length) (baseStart_1120112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120112 prefixEnd_1120112 := by exact prefixLift 1120112
  have htrace : WordTrace (prefixWord ++ tailWord_1120112) baseStart_1120112 baseEnd_1120112 := by
    simpa [prefixWord, tailWord_1120112, baseEnd_1120112] using wordTrace_append hprefix tailTrace_1120112
  have hstable : (prefixWord ++ tailWord_1120112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120112).length < 2 ^ (prefixWord ++ tailWord_1120112).sum := by decide
  have hdescent : baseEnd_1120112 < baseStart_1120112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120157 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1120157 : Nat := 118140960795 + 1120157 * 2 ^ 59
def prefixEnd_1120157 : Nat := 4983230072969 + 3 ^ 40 * 1120157 * 2
def baseEnd_1120157 : Nat := 383452632998986076190665

theorem tailTrace_1120157 : CollatzResearch.WordTrace tailWord_1120157 prefixEnd_1120157 383452632998986076190665 := by
  unfold tailWord_1120157
  simp only [CollatzResearch.WordTrace]
  refine ⟨40855482202869971429934725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27236988135246647619956483 40855482202869971429934725)
  ·
    refine ⟨7660402913038119643112761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40855482202869971429934725 7660402913038119643112761)
    ·
      refine ⟨5745302184778589732334571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7660402913038119643112761 5745302184778589732334571)
      ·
        refine ⟨8617953277167884598501857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5745302184778589732334571 8617953277167884598501857)
        ·
          refine ⟨6463464957875913448876393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8617953277167884598501857 6463464957875913448876393)
          ·
            refine ⟨4847598718406935086657295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6463464957875913448876393 4847598718406935086657295)
            ·
              refine ⟨7271398077610402629985943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4847598718406935086657295 7271398077610402629985943)
              ·
                refine ⟨10907097116415603944978915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7271398077610402629985943 10907097116415603944978915)
                ·
                  refine ⟨16360645674623405917468373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10907097116415603944978915 16360645674623405917468373)
                  ·
                    refine ⟨383452632998986076190665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16360645674623405917468373 383452632998986076190665)
                    ·
                      rfl

theorem cell22_1120157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1120157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120157 prefixEnd_1120157 := by exact prefixLift 1120157
  have htrace : WordTrace (prefixWord ++ tailWord_1120157) baseStart_1120157 baseEnd_1120157 := by
    simpa [prefixWord, tailWord_1120157, baseEnd_1120157] using wordTrace_append hprefix tailTrace_1120157
  have hstable : (prefixWord ++ tailWord_1120157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120157).length < 2 ^ (prefixWord ++ tailWord_1120157).sum := by decide
  have hdescent : baseEnd_1120157 < baseStart_1120157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120202 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_1120202 : Nat := 118140960795 + 1120202 * 2 ^ 59
def prefixEnd_1120202 : Nat := 4983230072969 + 3 ^ 40 * 1120202 * 2
def baseEnd_1120202 : Nat := 383468037418620958815527

theorem tailTrace_1120202 : CollatzResearch.WordTrace tailWord_1120202 prefixEnd_1120202 383468037418620958815527 := by
  unfold tailWord_1120202
  simp only [CollatzResearch.WordTrace]
  refine ⟨10214280871926736028830715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27238082325137962743548573 10214280871926736028830715)
  ·
    refine ⟨15321421307890104043246073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10214280871926736028830715 15321421307890104043246073)
    ·
      refine ⟨11491065980917578032434555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15321421307890104043246073 11491065980917578032434555)
      ·
        refine ⟨17236598971376367048651833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11491065980917578032434555 17236598971376367048651833)
        ·
          refine ⟨12927449228532275286488875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17236598971376367048651833 12927449228532275286488875)
          ·
            refine ⟨19391173842798412929733313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12927449228532275286488875 19391173842798412929733313)
            ·
              refine ⟨14543380382098809697299985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19391173842798412929733313 14543380382098809697299985)
              ·
                refine ⟨10907535286574107272974989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14543380382098809697299985 10907535286574107272974989)
                ·
                  refine ⟨4090325732465290227365621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10907535286574107272974989 4090325732465290227365621)
                  ·
                    refine ⟨383468037418620958815527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4090325732465290227365621 383468037418620958815527)
                    ·
                      rfl

theorem cell22_1120202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_1120202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120202 prefixEnd_1120202 := by exact prefixLift 1120202
  have htrace : WordTrace (prefixWord ++ tailWord_1120202) baseStart_1120202 baseEnd_1120202 := by
    simpa [prefixWord, tailWord_1120202, baseEnd_1120202] using wordTrace_append hprefix tailTrace_1120202
  have hstable : (prefixWord ++ tailWord_1120202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120202).length < 2 ^ (prefixWord ++ tailWord_1120202).sum := by decide
  have hdescent : baseEnd_1120202 < baseStart_1120202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120204 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 6]
def baseStart_1120204 : Nat := 118140960795 + 1120204 * 2 ^ 59
def prefixEnd_1120204 : Nat := 4983230072969 + 3 ^ 40 * 1120204 * 2
def baseEnd_1120204 : Nat := 127822907353164540088507

theorem tailTrace_1120204 : CollatzResearch.WordTrace tailWord_1120204 prefixEnd_1120204 127822907353164540088507 := by
  unfold tailWord_1120204
  simp only [CollatzResearch.WordTrace]
  refine ⟨20428598216849849228447833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27238130955799798971263777 20428598216849849228447833)
  ·
    refine ⟨15321448662637386921335875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20428598216849849228447833 15321448662637386921335875)
    ·
      refine ⟨22982172993956080382003813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15321448662637386921335875 22982172993956080382003813)
      ·
        refine ⟨4309157436366765071625715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22982172993956080382003813 4309157436366765071625715)
        ·
          refine ⟨6463736154550147607438573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4309157436366765071625715 6463736154550147607438573)
          ·
            refine ⟨2423901057956305352789465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6463736154550147607438573 2423901057956305352789465)
            ·
              refine ⟨1817925793467229014592099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2423901057956305352789465 1817925793467229014592099)
              ·
                refine ⟨2726888690200843521888149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1817925793467229014592099 2726888690200843521888149)
                ·
                  refine ⟨127822907353164540088507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2726888690200843521888149 127822907353164540088507)
                  ·
                    rfl

theorem cell22_1120204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_1120204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120204 prefixEnd_1120204 := by exact prefixLift 1120204
  have htrace : WordTrace (prefixWord ++ tailWord_1120204) baseStart_1120204 baseEnd_1120204 := by
    simpa [prefixWord, tailWord_1120204, baseEnd_1120204] using wordTrace_append hprefix tailTrace_1120204
  have hstable : (prefixWord ++ tailWord_1120204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120204).length < 2 ^ (prefixWord ++ tailWord_1120204).sum := by decide
  have hdescent : baseEnd_1120204 < baseStart_1120204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120234 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_1120234 : Nat := 118140960795 + 1120234 * 2 ^ 59
def prefixEnd_1120234 : Nat := 4983230072969 + 3 ^ 40 * 1120234 * 2
def baseEnd_1120234 : Nat := 383478991672583542015429

theorem tailTrace_1120234 : CollatzResearch.WordTrace tailWord_1120234 prefixEnd_1120234 383478991672583542015429 := by
  unfold tailWord_1120234
  simp only [CollatzResearch.WordTrace]
  refine ⟨10214572655897753395121939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27238860415727342386991837 10214572655897753395121939)
  ·
    refine ⟨15321858983846630092682909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10214572655897753395121939 15321858983846630092682909)
    ·
      refine ⟨5745697118942486284756091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15321858983846630092682909 5745697118942486284756091)
      ·
        refine ⟨8618545678413729427134137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5745697118942486284756091 8618545678413729427134137)
        ·
          refine ⟨6463909258810297070350603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8618545678413729427134137 6463909258810297070350603)
          ·
            refine ⟨9695863888215445605525905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6463909258810297070350603 9695863888215445605525905)
            ·
              refine ⟨7271897916161584204144429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9695863888215445605525905 7271897916161584204144429)
              ·
                refine ⟨2726961718560594076554161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7271897916161584204144429 2726961718560594076554161)
                ·
                  refine ⟨2045221288920445557415621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2726961718560594076554161 2045221288920445557415621)
                  ·
                    refine ⟨383478991672583542015429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2045221288920445557415621 383478991672583542015429)
                    ·
                      rfl

theorem cell22_1120234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_1120234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120234 prefixEnd_1120234 := by exact prefixLift 1120234
  have htrace : WordTrace (prefixWord ++ tailWord_1120234) baseStart_1120234 baseEnd_1120234 := by
    simpa [prefixWord, tailWord_1120234, baseEnd_1120234] using wordTrace_append hprefix tailTrace_1120234
  have hstable : (prefixWord ++ tailWord_1120234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120234).length < 2 ^ (prefixWord ++ tailWord_1120234).sum := by decide
  have hdescent : baseEnd_1120234 < baseStart_1120234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120238 : List Nat := [4, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_1120238 : Nat := 118140960795 + 1120238 * 2 ^ 59
def prefixEnd_1120238 : Nat := 4983230072969 + 3 ^ 40 * 1120238 * 2
def baseEnd_1120238 : Nat := 127826786984776288305139

theorem tailTrace_1120238 : CollatzResearch.WordTrace tailWord_1120238 prefixEnd_1120238 127826786984776288305139 := by
  unfold tailWord_1120238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5107304564447065282954171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27238957677051014842422245 5107304564447065282954171)
  ·
    refine ⟨7660956846670597924431257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5107304564447065282954171 7660956846670597924431257)
    ·
      refine ⟨5745717635002948443323443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7660956846670597924431257 5745717635002948443323443)
      ·
        refine ⟨8618576452504422664985165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5745717635002948443323443 8618576452504422664985165)
        ·
          refine ⟨3231966169689158499369437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8618576452504422664985165 3231966169689158499369437)
          ·
            refine ⟨1211987313633434437263539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3231966169689158499369437 1211987313633434437263539)
            ·
              refine ⟨1817980970450151655895309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211987313633434437263539 1817980970450151655895309)
              ·
                refine ⟨681742863918806870960741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1817980970450151655895309 681742863918806870960741)
                ·
                  refine ⟨127826786984776288305139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 681742863918806870960741 127826786984776288305139)
                  ·
                    rfl

theorem cell22_1120238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_1120238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120238 prefixEnd_1120238 := by exact prefixLift 1120238
  have htrace : WordTrace (prefixWord ++ tailWord_1120238) baseStart_1120238 baseEnd_1120238 := by
    simpa [prefixWord, tailWord_1120238, baseEnd_1120238] using wordTrace_append hprefix tailTrace_1120238
  have hstable : (prefixWord ++ tailWord_1120238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120238).length < 2 ^ (prefixWord ++ tailWord_1120238).sum := by decide
  have hdescent : baseEnd_1120238 < baseStart_1120238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120356 : List Nat := [2, 3, 1, 1, 2, 1, 3, 5, 4]
def baseStart_1120356 : Nat := 118140960795 + 1120356 * 2 ^ 59
def prefixEnd_1120356 : Nat := 4983230072969 + 3 ^ 40 * 1120356 * 2
def baseEnd_1120356 : Nat := 127840251588605296821685

theorem tailTrace_1120356 : CollatzResearch.WordTrace tailWord_1120356 prefixEnd_1120356 127840251588605296821685 := by
  unfold tailWord_1120356
  simp only [CollatzResearch.WordTrace]
  refine ⟨20431370164574514208214461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27241826886099352277619281 20431370164574514208214461)
  ·
    refine ⟨7661763811715442828080423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20431370164574514208214461 7661763811715442828080423)
    ·
      refine ⟨11492645717573164242120635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7661763811715442828080423 11492645717573164242120635)
      ·
        refine ⟨17238968576359746363180953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11492645717573164242120635 17238968576359746363180953)
        ·
          refine ⟨12929226432269809772385715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17238968576359746363180953 12929226432269809772385715)
          ·
            refine ⟨19393839648404714658578573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12929226432269809772385715 19393839648404714658578573)
            ·
              refine ⟨7272689868151767996966965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19393839648404714658578573 7272689868151767996966965)
              ·
                refine ⟨681814675139228249715653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7272689868151767996966965 681814675139228249715653)
                ·
                  refine ⟨127840251588605296821685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 681814675139228249715653 127840251588605296821685)
                  ·
                    rfl

theorem cell22_1120356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_1120356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120356 prefixEnd_1120356 := by exact prefixLift 1120356
  have htrace : WordTrace (prefixWord ++ tailWord_1120356) baseStart_1120356 baseEnd_1120356 := by
    simpa [prefixWord, tailWord_1120356, baseEnd_1120356] using wordTrace_append hprefix tailTrace_1120356
  have hstable : (prefixWord ++ tailWord_1120356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120356).length < 2 ^ (prefixWord ++ tailWord_1120356).sum := by decide
  have hdescent : baseEnd_1120356 < baseStart_1120356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120369 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 4, 4]
def baseStart_1120369 : Nat := 118140960795 + 1120369 * 2 ^ 59
def prefixEnd_1120369 : Nat := 4983230072969 + 3 ^ 40 * 1120369 * 2
def baseEnd_1120369 : Nat := 383525204931488189890015

theorem tailTrace_1120369 : CollatzResearch.WordTrace tailWord_1120369 prefixEnd_1120369 383525204931488189890015 := by
  unfold tailWord_1120369
  simp only [CollatzResearch.WordTrace]
  refine ⟨40863214478101931636652161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27242142985401287757768107 40863214478101931636652161)
  ·
    refine ⟨30647410858576448727489121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40863214478101931636652161 30647410858576448727489121)
    ·
      refine ⟨22985558143932336545616841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30647410858576448727489121 22985558143932336545616841)
      ·
        refine ⟨17239168607949252409212631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22985558143932336545616841 17239168607949252409212631)
        ·
          refine ⟨25858752911923878613818947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17239168607949252409212631 25858752911923878613818947)
          ·
            refine ⟨38788129367885817920728421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25858752911923878613818947 38788129367885817920728421)
            ·
              refine ⟨7272774256478590860136579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38788129367885817920728421 7272774256478590860136579)
              ·
                refine ⟨10909161384717886290204869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7272774256478590860136579 10909161384717886290204869)
                ·
                  refine ⟨2045467759634603679413413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10909161384717886290204869 2045467759634603679413413)
                  ·
                    refine ⟨383525204931488189890015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2045467759634603679413413 383525204931488189890015)
                    ·
                      rfl

theorem cell22_1120369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_1120369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120369 prefixEnd_1120369 := by exact prefixLift 1120369
  have htrace : WordTrace (prefixWord ++ tailWord_1120369) baseStart_1120369 baseEnd_1120369 := by
    simpa [prefixWord, tailWord_1120369, baseEnd_1120369] using wordTrace_append hprefix tailTrace_1120369
  have hstable : (prefixWord ++ tailWord_1120369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120369).length < 2 ^ (prefixWord ++ tailWord_1120369).sum := by decide
  have hdescent : baseEnd_1120369 < baseStart_1120369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120506 : List Nat := [3, 1, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_1120506 : Nat := 118140960795 + 1120506 * 2 ^ 59
def prefixEnd_1120506 : Nat := 4983230072969 + 3 ^ 40 * 1120506 * 2
def baseEnd_1120506 : Nat := 383572102831265499214595

theorem tailTrace_1120506 : CollatzResearch.WordTrace tailWord_1120506 prefixEnd_1120506 383572102831265499214595 := by
  unfold tailWord_1120506
  simp only [CollatzResearch.WordTrace]
  refine ⟨10217052819651401008597343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27245474185737069356259581 10217052819651401008597343)
  ·
    refine ⟨15325579229477101512896015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10217052819651401008597343 15325579229477101512896015)
    ·
      refine ⟨22988368844215652269344023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15325579229477101512896015 22988368844215652269344023)
      ·
        refine ⟨34482553266323478404016035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22988368844215652269344023 34482553266323478404016035)
        ·
          refine ⟨51723829899485217606024053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34482553266323478404016035 51723829899485217606024053)
          ·
            refine ⟨4849109053076739150564755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51723829899485217606024053 4849109053076739150564755)
            ·
              refine ⟨7273663579615108725847133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4849109053076739150564755 7273663579615108725847133)
              ·
                refine ⟨2727623842355665772192675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7273663579615108725847133 2727623842355665772192675)
                ·
                  refine ⟨4091435763533498658289013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2727623842355665772192675 4091435763533498658289013)
                  ·
                    refine ⟨383572102831265499214595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4091435763533498658289013 383572102831265499214595)
                    ·
                      rfl

theorem cell22_1120506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_1120506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120506 prefixEnd_1120506 := by exact prefixLift 1120506
  have htrace : WordTrace (prefixWord ++ tailWord_1120506) baseStart_1120506 baseEnd_1120506 := by
    simpa [prefixWord, tailWord_1120506, baseEnd_1120506] using wordTrace_append hprefix tailTrace_1120506
  have hstable : (prefixWord ++ tailWord_1120506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120506).length < 2 ^ (prefixWord ++ tailWord_1120506).sum := by decide
  have hdescent : baseEnd_1120506 < baseStart_1120506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120521 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 1, 6]
def baseStart_1120521 : Nat := 118140960795 + 1120521 * 2 ^ 59
def prefixEnd_1120521 : Nat := 4983230072969 + 3 ^ 40 * 1120521 * 2
def baseEnd_1120521 : Nat := 383577237637810460089549

theorem tailTrace_1120521 : CollatzResearch.WordTrace tailWord_1120521 prefixEnd_1120521 383577237637810460089549 := by
  unfold tailWord_1120521
  simp only [CollatzResearch.WordTrace]
  refine ⟨40868758373551261596185417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27245838915700841064123611 40868758373551261596185417)
  ·
    refine ⟨30651568780163446197139063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40868758373551261596185417 30651568780163446197139063)
    ·
      refine ⟨45977353170245169295708595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30651568780163446197139063 45977353170245169295708595)
      ·
        refine ⟨68966029755367753943562893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45977353170245169295708595 68966029755367753943562893)
        ·
          refine ⟨25862261158262907728836085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68966029755367753943562893 25862261158262907728836085)
          ·
            refine ⟨2424586983587147599578383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25862261158262907728836085 2424586983587147599578383)
            ·
              refine ⟨3636880475380721399367575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2424586983587147599578383 3636880475380721399367575)
              ·
                refine ⟨5455320713071082099051363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3636880475380721399367575 5455320713071082099051363)
                ·
                  refine ⟨8182981069606623148577045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5455320713071082099051363 8182981069606623148577045)
                  ·
                    refine ⟨383577237637810460089549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8182981069606623148577045 383577237637810460089549)
                    ·
                      rfl

theorem cell22_1120521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_1120521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120521 prefixEnd_1120521 := by exact prefixLift 1120521
  have htrace : WordTrace (prefixWord ++ tailWord_1120521) baseStart_1120521 baseEnd_1120521 := by
    simpa [prefixWord, tailWord_1120521, baseEnd_1120521] using wordTrace_append hprefix tailTrace_1120521
  have hstable : (prefixWord ++ tailWord_1120521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120521).length < 2 ^ (prefixWord ++ tailWord_1120521).sum := by decide
  have hdescent : baseEnd_1120521 < baseStart_1120521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120542 : List Nat := [4, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_1120542 : Nat := 118140960795 + 1120542 * 2 ^ 59
def prefixEnd_1120542 : Nat := 4983230072969 + 3 ^ 40 * 1120542 * 2
def baseEnd_1120542 : Nat := 127861475455657801771495

theorem tailTrace_1120542 : CollatzResearch.WordTrace tailWord_1120542 prefixEnd_1120542 127861475455657801771495 := by
  unfold tailWord_1120542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5108690538309397772837485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27246349537650121455133253 5108690538309397772837485)
  ·
    refine ⟨1915758951866024164814057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5108690538309397772837485 1915758951866024164814057)
    ·
      refine ⟨1436819213899518123610543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1915758951866024164814057 1436819213899518123610543)
      ·
        refine ⟨2155228820849277185415815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1436819213899518123610543 2155228820849277185415815)
        ·
          refine ⟨3232843231273915778123723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2155228820849277185415815 3232843231273915778123723)
          ·
            refine ⟨4849264846910873667185585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3232843231273915778123723 4849264846910873667185585)
            ·
              refine ⟨3636948635183155250389189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4849264846910873667185585 3636948635183155250389189)
              ·
                refine ⟨681927869096841609447973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3636948635183155250389189 681927869096841609447973)
                ·
                  refine ⟨127861475455657801771495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 681927869096841609447973 127861475455657801771495)
                  ·
                    rfl

theorem cell22_1120542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_1120542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120542 prefixEnd_1120542 := by exact prefixLift 1120542
  have htrace : WordTrace (prefixWord ++ tailWord_1120542) baseStart_1120542 baseEnd_1120542 := by
    simpa [prefixWord, tailWord_1120542, baseEnd_1120542] using wordTrace_append hprefix tailTrace_1120542
  have hstable : (prefixWord ++ tailWord_1120542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120542).length < 2 ^ (prefixWord ++ tailWord_1120542).sum := by decide
  have hdescent : baseEnd_1120542 < baseStart_1120542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120557 : List Nat := [1, 5, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1120557 : Nat := 118140960795 + 1120557 * 2 ^ 59
def prefixEnd_1120557 : Nat := 4983230072969 + 3 ^ 40 * 1120557 * 2
def baseEnd_1120557 : Nat := 383589561173518366189439

theorem tailTrace_1120557 : CollatzResearch.WordTrace tailWord_1120557 prefixEnd_1120557 383589561173518366189439 := by
  unfold tailWord_1120557
  simp only [CollatzResearch.WordTrace]
  refine ⟨40870071401420839744495925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27246714267613893162997283 40870071401420839744495925)
  ·
    refine ⟨3831569193883203726046493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40870071401420839744495925 3831569193883203726046493)
    ·
      refine ⟨1436838447706201397267435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3831569193883203726046493 1436838447706201397267435)
      ·
        refine ⟨2155257671559302095901153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1436838447706201397267435 2155257671559302095901153)
        ·
          refine ⟨1616443253669476571925865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2155257671559302095901153 1616443253669476571925865)
          ·
            refine ⟨1212332440252107428944399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1616443253669476571925865 1212332440252107428944399)
            ·
              refine ⟨1818498660378161143416599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212332440252107428944399 1818498660378161143416599)
              ·
                refine ⟨2727747990567241715124899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1818498660378161143416599 2727747990567241715124899)
                ·
                  refine ⟨4091621985850862572687349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2727747990567241715124899 4091621985850862572687349)
                  ·
                    refine ⟨383589561173518366189439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4091621985850862572687349 383589561173518366189439)
                    ·
                      rfl

theorem cell22_1120557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1120557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120557 prefixEnd_1120557 := by exact prefixLift 1120557
  have htrace : WordTrace (prefixWord ++ tailWord_1120557) baseStart_1120557 baseEnd_1120557 := by
    simpa [prefixWord, tailWord_1120557, baseEnd_1120557] using wordTrace_append hprefix tailTrace_1120557
  have hstable : (prefixWord ++ tailWord_1120557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120557).length < 2 ^ (prefixWord ++ tailWord_1120557).sum := by decide
  have hdescent : baseEnd_1120557 < baseStart_1120557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120568 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 3, 3]
def baseStart_1120568 : Nat := 118140960795 + 1120568 * 2 ^ 59
def prefixEnd_1120568 : Nat := 4983230072969 + 3 ^ 40 * 1120568 * 2
def baseEnd_1120568 : Nat := 383593326698318004164405

theorem tailTrace_1120568 : CollatzResearch.WordTrace tailWord_1120568 prefixEnd_1120568 383593326698318004164405 := by
  unfold tailWord_1120568
  simp only [CollatzResearch.WordTrace]
  refine ⟨20435236302190494311573179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27246981736253992415430905 20435236302190494311573179)
  ·
    refine ⟨30652854453285741467359769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20435236302190494311573179 30652854453285741467359769)
    ·
      refine ⟨22989640839964306100519827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30652854453285741467359769 22989640839964306100519827)
      ·
        refine ⟨34484461259946459150779741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22989640839964306100519827 34484461259946459150779741)
        ·
          refine ⟨12931672972479922181542403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34484461259946459150779741 12931672972479922181542403)
          ·
            refine ⟨19397509458719883272313605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12931672972479922181542403 19397509458719883272313605)
            ·
              refine ⟨3637033023509978113558801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19397509458719883272313605 3637033023509978113558801)
              ·
                refine ⟨2727774767632483585169101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3637033023509978113558801 2727774767632483585169101)
                ·
                  refine ⟨1022915537862181344438413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2727774767632483585169101 1022915537862181344438413)
                  ·
                    refine ⟨383593326698318004164405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1022915537862181344438413 383593326698318004164405)
                    ·
                      rfl

theorem cell22_1120568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_1120568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120568 prefixEnd_1120568 := by exact prefixLift 1120568
  have htrace : WordTrace (prefixWord ++ tailWord_1120568) baseStart_1120568 baseEnd_1120568 := by
    simpa [prefixWord, tailWord_1120568, baseEnd_1120568] using wordTrace_append hprefix tailTrace_1120568
  have hstable : (prefixWord ++ tailWord_1120568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120568).length < 2 ^ (prefixWord ++ tailWord_1120568).sum := by decide
  have hdescent : baseEnd_1120568 < baseStart_1120568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120615 : List Nat := [1, 1, 5, 1, 3, 1, 4, 1, 5]
def baseStart_1120615 : Nat := 118140960795 + 1120615 * 2 ^ 59
def prefixEnd_1120615 : Nat := 4983230072969 + 3 ^ 40 * 1120615 * 2
def baseEnd_1120615 : Nat := 127869805252941849413087

theorem tailTrace_1120615 : CollatzResearch.WordTrace tailWord_1120615 prefixEnd_1120615 127869805252941849413087 := by
  unfold tailWord_1120615
  simp only [CollatzResearch.WordTrace]
  refine ⟨40872186835210715650107299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27248124556807143766738199 40872186835210715650107299)
  ·
    refine ⟨61308280252816073475160949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40872186835210715650107299 61308280252816073475160949)
    ·
      refine ⟨5747651273701506888296339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61308280252816073475160949 5747651273701506888296339)
      ·
        refine ⟨8621476910552260332444509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5747651273701506888296339 8621476910552260332444509)
        ·
          refine ⟨3233053841457097624666691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8621476910552260332444509 3233053841457097624666691)
          ·
            refine ⟨4849580762185646437000037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3233053841457097624666691 4849580762185646437000037)
            ·
              refine ⟨909296392909808706937507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4849580762185646437000037 909296392909808706937507)
              ·
                refine ⟨1363944589364713060406261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909296392909808706937507 1363944589364713060406261)
                ·
                  refine ⟨127869805252941849413087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1363944589364713060406261 127869805252941849413087)
                  ·
                    rfl

theorem cell22_1120615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 5].length) (baseStart_1120615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120615 prefixEnd_1120615 := by exact prefixLift 1120615
  have htrace : WordTrace (prefixWord ++ tailWord_1120615) baseStart_1120615 baseEnd_1120615 := by
    simpa [prefixWord, tailWord_1120615, baseEnd_1120615] using wordTrace_append hprefix tailTrace_1120615
  have hstable : (prefixWord ++ tailWord_1120615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120615).length < 2 ^ (prefixWord ++ tailWord_1120615).sum := by decide
  have hdescent : baseEnd_1120615 < baseStart_1120615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120675 : List Nat := [1, 1, 1, 4, 1, 4, 2, 3, 2, 3]
def baseStart_1120675 : Nat := 118140960795 + 1120675 * 2 ^ 59
def prefixEnd_1120675 : Nat := 4983230072969 + 3 ^ 40 * 1120675 * 2
def baseEnd_1120675 : Nat := 383629954985005391739077

theorem tailTrace_1120675 : CollatzResearch.WordTrace tailWord_1120675 prefixEnd_1120675 383629954985005391739077 := by
  unfold tailWord_1120675
  simp only [CollatzResearch.WordTrace]
  refine ⟨40874375214993345897291479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27249583476662230598194319 40874375214993345897291479)
  ·
    refine ⟨61311562822490018845937219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40874375214993345897291479 61311562822490018845937219)
    ·
      refine ⟨91967344233735028268905829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61311562822490018845937219 91967344233735028268905829)
      ·
        refine ⟨17243877043825317800419843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 91967344233735028268905829 17243877043825317800419843)
        ·
          refine ⟨25865815565737976700629765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17243877043825317800419843 25865815565737976700629765)
          ·
            refine ⟨4849840418575870631368081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25865815565737976700629765 4849840418575870631368081)
            ·
              refine ⟨3637380313931902973526061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4849840418575870631368081 3637380313931902973526061)
              ·
                refine ⟨1364017617724463615072273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3637380313931902973526061 1364017617724463615072273)
                ·
                  refine ⟨1023013213293347711304205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1364017617724463615072273 1023013213293347711304205)
                  ·
                    refine ⟨383629954985005391739077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1023013213293347711304205 383629954985005391739077)
                    ·
                      rfl

theorem cell22_1120675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 2, 3].length) (baseStart_1120675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120675 prefixEnd_1120675 := by exact prefixLift 1120675
  have htrace : WordTrace (prefixWord ++ tailWord_1120675) baseStart_1120675 baseEnd_1120675 := by
    simpa [prefixWord, tailWord_1120675, baseEnd_1120675] using wordTrace_append hprefix tailTrace_1120675
  have hstable : (prefixWord ++ tailWord_1120675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120675).length < 2 ^ (prefixWord ++ tailWord_1120675).sum := by decide
  have hdescent : baseEnd_1120675 < baseStart_1120675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120797 : List Nat := [1, 4, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1120797 : Nat := 118140960795 + 1120797 * 2 ^ 59
def prefixEnd_1120797 : Nat := 4983230072969 + 3 ^ 40 * 1120797 * 2
def baseEnd_1120797 : Nat := 383671718078237740188703

theorem tailTrace_1120797 : CollatzResearch.WordTrace tailWord_1120797 prefixEnd_1120797 383671718078237740188703 := by
  unfold tailWord_1120797
  simp only [CollatzResearch.WordTrace]
  refine ⟨40878824920551360733232645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27252549947034240488821763 40878824920551360733232645)
  ·
    refine ⟨7664779672603380137481121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40878824920551360733232645 7664779672603380137481121)
    ·
      refine ⟨5748584754452535103110841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7664779672603380137481121 5748584754452535103110841)
      ·
        refine ⟨4311438565839401327333131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5748584754452535103110841 4311438565839401327333131)
        ·
          refine ⟨6467157848759101990999697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4311438565839401327333131 6467157848759101990999697)
          ·
            refine ⟨4850368386569326493249773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6467157848759101990999697 4850368386569326493249773)
            ·
              refine ⟨1818888144963497434968665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4850368386569326493249773 1818888144963497434968665)
              ·
                refine ⟨1364166108722623076226499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1818888144963497434968665 1364166108722623076226499)
                ·
                  refine ⟨2046249163083934614339749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1364166108722623076226499 2046249163083934614339749)
                  ·
                    refine ⟨383671718078237740188703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2046249163083934614339749 383671718078237740188703)
                    ·
                      rfl

theorem cell22_1120797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1120797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120797 prefixEnd_1120797 := by exact prefixLift 1120797
  have htrace : WordTrace (prefixWord ++ tailWord_1120797) baseStart_1120797 baseEnd_1120797 := by
    simpa [prefixWord, tailWord_1120797, baseEnd_1120797] using wordTrace_append hprefix tailTrace_1120797
  have hstable : (prefixWord ++ tailWord_1120797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120797).length < 2 ^ (prefixWord ++ tailWord_1120797).sum := by decide
  have hdescent : baseEnd_1120797 < baseStart_1120797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120810 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1120810 : Nat := 118140960795 + 1120810 * 2 ^ 59
def prefixEnd_1120810 : Nat := 4983230072969 + 3 ^ 40 * 1120810 * 2
def baseEnd_1120810 : Nat := 383676168243910039613663

theorem tailTrace_1120810 : CollatzResearch.WordTrace tailWord_1120810 prefixEnd_1120810 383676168243910039613663 := by
  unfold tailWord_1120810
  simp only [CollatzResearch.WordTrace]
  refine ⟨10219824767376065988363971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27252866046336175968970589 10219824767376065988363971)
  ·
    refine ⟨15329737151064098982545957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10219824767376065988363971 15329737151064098982545957)
    ·
      refine ⟨2874325715824518559227367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15329737151064098982545957 2874325715824518559227367)
      ·
        refine ⟨4311488573736777838841051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2874325715824518559227367 4311488573736777838841051)
        ·
          refine ⟨6467232860605166758261577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4311488573736777838841051 6467232860605166758261577)
          ·
            refine ⟨4850424645453875068696183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6467232860605166758261577 4850424645453875068696183)
            ·
              refine ⟨7275636968180812603044275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4850424645453875068696183 7275636968180812603044275)
              ·
                refine ⟨10913455452271218904566413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7275636968180812603044275 10913455452271218904566413)
                ·
                  refine ⟨4092545794601707089212405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10913455452271218904566413 4092545794601707089212405)
                  ·
                    refine ⟨383676168243910039613663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4092545794601707089212405 383676168243910039613663)
                    ·
                      rfl

theorem cell22_1120810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1120810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120810 prefixEnd_1120810 := by exact prefixLift 1120810
  have htrace : WordTrace (prefixWord ++ tailWord_1120810) baseStart_1120810 baseEnd_1120810 := by
    simpa [prefixWord, tailWord_1120810, baseEnd_1120810] using wordTrace_append hprefix tailTrace_1120810
  have hstable : (prefixWord ++ tailWord_1120810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120810).length < 2 ^ (prefixWord ++ tailWord_1120810).sum := by decide
  have hdescent : baseEnd_1120810 < baseStart_1120810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120825 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 2, 4]
def baseStart_1120825 : Nat := 118140960795 + 1120825 * 2 ^ 59
def prefixEnd_1120825 : Nat := 4983230072969 + 3 ^ 40 * 1120825 * 2
def baseEnd_1120825 : Nat := 383681303050455000488617

theorem tailTrace_1120825 : CollatzResearch.WordTrace tailWord_1120825 prefixEnd_1120825 383681303050455000488617 := by
  unfold tailWord_1120825
  simp only [CollatzResearch.WordTrace]
  refine ⟨40879846164449921515251929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27253230776299947676834619 40879846164449921515251929)
  ·
    refine ⟨30659884623337441136438947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40879846164449921515251929 30659884623337441136438947)
    ·
      refine ⟨45989826935006161704658421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30659884623337441136438947 45989826935006161704658421)
      ·
        refine ⟨4311546275156827659811727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45989826935006161704658421 4311546275156827659811727)
        ·
          refine ⟨6467319412735241489717591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4311546275156827659811727 6467319412735241489717591)
          ·
            refine ⟨9700979119102862234576387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6467319412735241489717591 9700979119102862234576387)
            ·
              refine ⟨14551468678654293351864581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9700979119102862234576387 14551468678654293351864581)
              ·
                refine ⟨2728400377247680003474609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14551468678654293351864581 2728400377247680003474609)
                ·
                  refine ⟨2046300282935760002605957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2728400377247680003474609 2046300282935760002605957)
                  ·
                    refine ⟨383681303050455000488617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2046300282935760002605957 383681303050455000488617)
                    ·
                      rfl

theorem cell22_1120825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_1120825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120825 prefixEnd_1120825 := by exact prefixLift 1120825
  have htrace : WordTrace (prefixWord ++ tailWord_1120825) baseStart_1120825 baseEnd_1120825 := by
    simpa [prefixWord, tailWord_1120825, baseEnd_1120825] using wordTrace_append hprefix tailTrace_1120825
  have hstable : (prefixWord ++ tailWord_1120825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120825).length < 2 ^ (prefixWord ++ tailWord_1120825).sum := by decide
  have hdescent : baseEnd_1120825 < baseStart_1120825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120829 : List Nat := [1, 4, 1, 3, 2, 1, 4, 2, 4]
def baseStart_1120829 : Nat := 118140960795 + 1120829 * 2 ^ 59
def prefixEnd_1120829 : Nat := 4983230072969 + 3 ^ 40 * 1120829 * 2
def baseEnd_1120829 : Nat := 127894224110733441129535

theorem tailTrace_1120829 : CollatzResearch.WordTrace tailWord_1120829 prefixEnd_1120829 127894224110733441129535 := by
  unfold tailWord_1120829
  simp only [CollatzResearch.WordTrace]
  refine ⟨40879992056435430198397541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27253328037623620132265027 40879992056435430198397541)
  ·
    refine ⟨7664998510581643162199539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40879992056435430198397541 7664998510581643162199539)
    ·
      refine ⟨11497497765872464743299309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7664998510581643162199539 11497497765872464743299309)
      ·
        refine ⟨4311561662202174278737241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11497497765872464743299309 4311561662202174278737241)
        ·
          refine ⟨3233671246651630709052931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4311561662202174278737241 3233671246651630709052931)
          ·
            refine ⟨4850506869977446063579397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3233671246651630709052931 4850506869977446063579397)
            ·
              refine ⟨909470038120771136921137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4850506869977446063579397 909470038120771136921137)
              ·
                refine ⟨682102528590578352690853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 909470038120771136921137 682102528590578352690853)
                ·
                  refine ⟨127894224110733441129535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 682102528590578352690853 127894224110733441129535)
                  ·
                    rfl

theorem cell22_1120829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_1120829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120829 prefixEnd_1120829 := by exact prefixLift 1120829
  have htrace : WordTrace (prefixWord ++ tailWord_1120829) baseStart_1120829 baseEnd_1120829 := by
    simpa [prefixWord, tailWord_1120829, baseEnd_1120829] using wordTrace_append hprefix tailTrace_1120829
  have hstable : (prefixWord ++ tailWord_1120829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120829).length < 2 ^ (prefixWord ++ tailWord_1120829).sum := by decide
  have hdescent : baseEnd_1120829 < baseStart_1120829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120889 : List Nat := [1, 2, 1, 3, 3, 2, 2, 4, 1, 3]
def baseStart_1120889 : Nat := 118140960795 + 1120889 * 2 ^ 59
def prefixEnd_1120889 : Nat := 4983230072969 + 3 ^ 40 * 1120889 * 2
def baseEnd_1120889 : Nat := 383703211558380166888421

theorem tailTrace_1120889 : CollatzResearch.WordTrace tailWord_1120889 prefixEnd_1120889 383703211558380166888421 := by
  unfold tailWord_1120889
  simp only [CollatzResearch.WordTrace]
  refine ⟨40882180436218060445581721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27254786957478706963721147 40882180436218060445581721)
  ·
    refine ⟨30661635327163545334186291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40882180436218060445581721 30661635327163545334186291)
    ·
      refine ⟨45992452990745318001279437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30661635327163545334186291 45992452990745318001279437)
      ·
        refine ⟨17247169871529494250479789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45992452990745318001279437 17247169871529494250479789)
        ·
          refine ⟨6467688701823560343929921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17247169871529494250479789 6467688701823560343929921)
          ·
            refine ⟨4850766526367670257947441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6467688701823560343929921 4850766526367670257947441)
            ·
              refine ⟨3638074894775752693460581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4850766526367670257947441 3638074894775752693460581)
              ·
                refine ⟨682139042770453630023859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3638074894775752693460581 682139042770453630023859)
                ·
                  refine ⟨1023208564155680445035789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682139042770453630023859 1023208564155680445035789)
                  ·
                    refine ⟨383703211558380166888421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1023208564155680445035789 383703211558380166888421)
                    ·
                      rfl

theorem cell22_1120889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 1, 3].length) (baseStart_1120889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120889 prefixEnd_1120889 := by exact prefixLift 1120889
  have htrace : WordTrace (prefixWord ++ tailWord_1120889) baseStart_1120889 baseEnd_1120889 := by
    simpa [prefixWord, tailWord_1120889, baseEnd_1120889] using wordTrace_append hprefix tailTrace_1120889
  have hstable : (prefixWord ++ tailWord_1120889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120889).length < 2 ^ (prefixWord ++ tailWord_1120889).sum := by decide
  have hdescent : baseEnd_1120889 < baseStart_1120889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120932 : List Nat := [2, 3, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_1120932 : Nat := 118140960795 + 1120932 * 2 ^ 59
def prefixEnd_1120932 : Nat := 4983230072969 + 3 ^ 40 * 1120932 * 2
def baseEnd_1120932 : Nat := 383717931337142388063289

theorem tailTrace_1120932 : CollatzResearch.WordTrace tailWord_1120932 prefixEnd_1120932 383717931337142388063289 := by
  unfold tailWord_1120932
  simp only [CollatzResearch.WordTrace]
  refine ⟨20441874387531139394698525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27255832516708185859598033 20441874387531139394698525)
  ·
    refine ⟨7665702895324177273011947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20441874387531139394698525 7665702895324177273011947)
    ·
      refine ⟨11498554342986265909517921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7665702895324177273011947 11498554342986265909517921)
      ·
        refine ⟨8623915757239699432138441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11498554342986265909517921 8623915757239699432138441)
        ·
          refine ⟨6467936817929774574103831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8623915757239699432138441 6467936817929774574103831)
          ·
            refine ⟨9701905226894661861155747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6467936817929774574103831 9701905226894661861155747)
            ·
              refine ⟨14552857840341992791733621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9701905226894661861155747 14552857840341992791733621)
              ·
                refine ⟨1364330422532061824225027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14552857840341992791733621 1364330422532061824225027)
                ·
                  refine ⟨2046495633798092736337541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1364330422532061824225027 2046495633798092736337541)
                  ·
                    refine ⟨383717931337142388063289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2046495633798092736337541 383717931337142388063289)
                    ·
                      rfl

theorem cell22_1120932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_1120932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120932 prefixEnd_1120932 := by exact prefixLift 1120932
  have htrace : WordTrace (prefixWord ++ tailWord_1120932) baseStart_1120932 baseEnd_1120932 := by
    simpa [prefixWord, tailWord_1120932, baseEnd_1120932] using wordTrace_append hprefix tailTrace_1120932
  have hstable : (prefixWord ++ tailWord_1120932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120932).length < 2 ^ (prefixWord ++ tailWord_1120932).sum := by decide
  have hdescent : baseEnd_1120932 < baseStart_1120932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120947 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 6]
def baseStart_1120947 : Nat := 118140960795 + 1120947 * 2 ^ 59
def prefixEnd_1120947 : Nat := 4983230072969 + 3 ^ 40 * 1120947 * 2
def baseEnd_1120947 : Nat := 127907688714562449646081

theorem tailTrace_1120947 : CollatzResearch.WordTrace tailWord_1120947 prefixEnd_1120947 127907688714562449646081 := by
  unfold tailWord_1120947
  simp only [CollatzResearch.WordTrace]
  refine ⟨40884295870007936351193095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27256197246671957567462063 40884295870007936351193095)
  ·
    refine ⟨61326443805011904526789643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40884295870007936351193095 61326443805011904526789643)
    ·
      refine ⟨91989665707517856790184465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61326443805011904526789643 91989665707517856790184465)
      ·
        refine ⟨68992249280638392592638349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91989665707517856790184465 68992249280638392592638349)
        ·
          refine ⟨25872093480239397222239381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68992249280638392592638349 25872093480239397222239381)
          ·
            refine ⟨1212754381886221744792471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25872093480239397222239381 1212754381886221744792471)
            ·
              refine ⟨1819131572829332617188707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212754381886221744792471 1819131572829332617188707)
              ·
                refine ⟨2728697359243998925783061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819131572829332617188707 2728697359243998925783061)
                ·
                  refine ⟨127907688714562449646081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2728697359243998925783061 127907688714562449646081)
                  ·
                    rfl

theorem cell22_1120947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 6].length) (baseStart_1120947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120947 prefixEnd_1120947 := by exact prefixLift 1120947
  have htrace : WordTrace (prefixWord ++ tailWord_1120947) baseStart_1120947 baseEnd_1120947 := by
    simpa [prefixWord, tailWord_1120947, baseEnd_1120947] using wordTrace_append hprefix tailTrace_1120947
  have hstable : (prefixWord ++ tailWord_1120947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120947).length < 2 ^ (prefixWord ++ tailWord_1120947).sum := by decide
  have hdescent : baseEnd_1120947 < baseStart_1120947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1120977 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 2, 4]
def baseStart_1120977 : Nat := 118140960795 + 1120977 * 2 ^ 59
def prefixEnd_1120977 : Nat := 4983230072969 + 3 ^ 40 * 1120977 * 2
def baseEnd_1120977 : Nat := 383733335756777270688151

theorem tailTrace_1120977 : CollatzResearch.WordTrace tailWord_1120977 prefixEnd_1120977 383733335756777270688151 := by
  unfold tailWord_1120977
  simp only [CollatzResearch.WordTrace]
  refine ⟨40885390059899251474785185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27256926706599500983190123 40885390059899251474785185)
  ·
    refine ⟨30664042544924438606088889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40885390059899251474785185 30664042544924438606088889)
    ·
      refine ⟨22998031908693328954566667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30664042544924438606088889 22998031908693328954566667)
      ·
        refine ⟨34497047863039993431850001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22998031908693328954566667 34497047863039993431850001)
        ·
          refine ⟨25872785897279995073887501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34497047863039993431850001 25872785897279995073887501)
          ·
            refine ⟨9702294711479998152707813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25872785897279995073887501 9702294711479998152707813)
            ·
              refine ⟨1819180258402499653632715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9702294711479998152707813 1819180258402499653632715)
              ·
                refine ⟨2728770387603749480449073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819180258402499653632715 2728770387603749480449073)
                ·
                  refine ⟨2046577790702812110336805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2728770387603749480449073 2046577790702812110336805)
                  ·
                    refine ⟨383733335756777270688151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2046577790702812110336805 383733335756777270688151)
                    ·
                      rfl

theorem cell22_1120977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_1120977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1120977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1120977 prefixEnd_1120977 := by exact prefixLift 1120977
  have htrace : WordTrace (prefixWord ++ tailWord_1120977) baseStart_1120977 baseEnd_1120977 := by
    simpa [prefixWord, tailWord_1120977, baseEnd_1120977] using wordTrace_append hprefix tailTrace_1120977
  have hstable : (prefixWord ++ tailWord_1120977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1120977).length < 2 ^ (prefixWord ++ tailWord_1120977).sum := by decide
  have hdescent : baseEnd_1120977 < baseStart_1120977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1120977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121013 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1121013 : Nat := 118140960795 + 1121013 * 2 ^ 59
def prefixEnd_1121013 : Nat := 4983230072969 + 3 ^ 40 * 1121013 * 2
def baseEnd_1121013 : Nat := 383745659292485176788041

theorem tailTrace_1121013 : CollatzResearch.WordTrace tailWord_1121013 prefixEnd_1121013 383745659292485176788041 := by
  unfold tailWord_1121013
  simp only [CollatzResearch.WordTrace]
  refine ⟨40886703087768829623095693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27257802058512553082063795 40886703087768829623095693)
  ·
    refine ⟨15332513657913311108660885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40886703087768829623095693 15332513657913311108660885)
    ·
      refine ⟨718711577714686458218479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15332513657913311108660885 718711577714686458218479)
      ·
        refine ⟨1078067366572029687327719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718711577714686458218479 1078067366572029687327719)
        ·
          refine ⟨1617101049858044530991579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1078067366572029687327719 1617101049858044530991579)
          ·
            refine ⟨2425651574787066796487369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1617101049858044530991579 2425651574787066796487369)
            ·
              refine ⟨1819238681090300097365527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2425651574787066796487369 1819238681090300097365527)
              ·
                refine ⟨2728858021635450146048291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819238681090300097365527 2728858021635450146048291)
                ·
                  refine ⟨4093287032453175219072437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2728858021635450146048291 4093287032453175219072437)
                  ·
                    refine ⟨383745659292485176788041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4093287032453175219072437 383745659292485176788041)
                    ·
                      rfl

theorem cell22_1121013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1121013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121013 prefixEnd_1121013 := by exact prefixLift 1121013
  have htrace : WordTrace (prefixWord ++ tailWord_1121013) baseStart_1121013 baseEnd_1121013 := by
    simpa [prefixWord, tailWord_1121013, baseEnd_1121013] using wordTrace_append hprefix tailTrace_1121013
  have hstable : (prefixWord ++ tailWord_1121013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121013).length < 2 ^ (prefixWord ++ tailWord_1121013).sum := by decide
  have hdescent : baseEnd_1121013 < baseStart_1121013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121035 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 3, 7]
def baseStart_1121035 : Nat := 118140960795 + 1121035 * 2 ^ 59
def prefixEnd_1121035 : Nat := 4983230072969 + 3 ^ 40 * 1121035 * 2
def baseEnd_1121035 : Nat := 383753190342084452737973

theorem tailTrace_1121035 : CollatzResearch.WordTrace tailWord_1121035 prefixEnd_1121035 383753190342084452737973 := by
  unfold tailWord_1121035
  simp only [CollatzResearch.WordTrace]
  refine ⟨40887505493689127380396559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27258336995792751586931039 40887505493689127380396559)
  ·
    refine ⟨61331258240533691070594839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40887505493689127380396559 61331258240533691070594839)
    ·
      refine ⟨91996887360800536605892259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61331258240533691070594839 91996887360800536605892259)
      ·
        refine ⟨137995331041200804908838389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91996887360800536605892259 137995331041200804908838389)
        ·
          refine ⟨12937062285112575460203599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 137995331041200804908838389 12937062285112575460203599)
          ·
            refine ⟨19405593427668863190305399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12937062285112575460203599 19405593427668863190305399)
            ·
              refine ⟨29108390141503294785458099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19405593427668863190305399 29108390141503294785458099)
              ·
                refine ⟨43662585212254942178187149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29108390141503294785458099 43662585212254942178187149)
                ·
                  refine ⟨16373469454595603316820181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43662585212254942178187149 16373469454595603316820181)
                  ·
                    refine ⟨383753190342084452737973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16373469454595603316820181 383753190342084452737973)
                    ·
                      rfl

theorem cell22_1121035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_1121035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121035 prefixEnd_1121035 := by exact prefixLift 1121035
  have htrace : WordTrace (prefixWord ++ tailWord_1121035) baseStart_1121035 baseEnd_1121035 := by
    simpa [prefixWord, tailWord_1121035, baseEnd_1121035] using wordTrace_append hprefix tailTrace_1121035
  have hstable : (prefixWord ++ tailWord_1121035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121035).length < 2 ^ (prefixWord ++ tailWord_1121035).sum := by decide
  have hdescent : baseEnd_1121035 < baseStart_1121035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121052 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_1121052 : Nat := 118140960795 + 1121052 * 2 ^ 59
def prefixEnd_1121052 : Nat := 4983230072969 + 3 ^ 40 * 1121052 * 2
def baseEnd_1121052 : Nat := 383759009789502075062921

theorem tailTrace_1121052 : CollatzResearch.WordTrace tailWord_1121052 prefixEnd_1121052 383759009789502075062921 := by
  unfold tailWord_1121052
  simp only [CollatzResearch.WordTrace]
  refine ⟨20444062767313769641882705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27258750356418359522510273 20444062767313769641882705)
  ·
    refine ⟨15333047075485327231412029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20444062767313769641882705 15333047075485327231412029)
    ·
      refine ⟨5749892653306997711779511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15333047075485327231412029 5749892653306997711779511)
      ·
        refine ⟨8624838979960496567669267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5749892653306997711779511 8624838979960496567669267)
        ·
          refine ⟨12937258469940744851503901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8624838979960496567669267 12937258469940744851503901)
          ·
            refine ⟨4851471926227779319313963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12937258469940744851503901 4851471926227779319313963)
            ·
              refine ⟨7277207889341668978970945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4851471926227779319313963 7277207889341668978970945)
              ·
                refine ⟨5457905917006251734228209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7277207889341668978970945 5457905917006251734228209)
                ·
                  refine ⟨4093429437754688800671157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5457905917006251734228209 4093429437754688800671157)
                  ·
                    refine ⟨383759009789502075062921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4093429437754688800671157 383759009789502075062921)
                    ·
                      rfl

theorem cell22_1121052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_1121052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121052 prefixEnd_1121052 := by exact prefixLift 1121052
  have htrace : WordTrace (prefixWord ++ tailWord_1121052) baseStart_1121052 baseEnd_1121052 := by
    simpa [prefixWord, tailWord_1121052, baseEnd_1121052] using wordTrace_append hprefix tailTrace_1121052
  have hstable : (prefixWord ++ tailWord_1121052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121052).length < 2 ^ (prefixWord ++ tailWord_1121052).sum := by decide
  have hdescent : baseEnd_1121052 < baseStart_1121052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121065 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 10]
def baseStart_1121065 : Nat := 118140960795 + 1121065 * 2 ^ 59
def prefixEnd_1121065 : Nat := 4983230072969 + 3 ^ 40 * 1121065 * 2
def baseEnd_1121065 : Nat := 127921153318391458162627

theorem tailTrace_1121065 : CollatzResearch.WordTrace tailWord_1121065 prefixEnd_1121065 127921153318391458162627 := by
  unfold tailWord_1121065
  simp only [CollatzResearch.WordTrace]
  refine ⟨40888599683580442503988649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27259066455720295002659099 40888599683580442503988649)
  ·
    refine ⟨30666449762685331877991487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40888599683580442503988649 30666449762685331877991487)
    ·
      refine ⟨45999674644027997816987231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30666449762685331877991487 45999674644027997816987231)
      ·
        refine ⟨68999511966041996725480847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45999674644027997816987231 68999511966041996725480847)
        ·
          refine ⟨103499267949062995088221271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68999511966041996725480847 103499267949062995088221271)
          ·
            refine ⟨155248901923594492632331907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103499267949062995088221271 155248901923594492632331907)
            ·
              refine ⟨232873352885391738948497861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155248901923594492632331907 232873352885391738948497861)
              ·
                refine ⟨43663753666010951052843349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232873352885391738948497861 43663753666010951052843349)
                ·
                  refine ⟨127921153318391458162627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 43663753666010951052843349 127921153318391458162627)
                  ·
                    rfl

theorem cell22_1121065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_1121065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121065 prefixEnd_1121065 := by exact prefixLift 1121065
  have htrace : WordTrace (prefixWord ++ tailWord_1121065) baseStart_1121065 baseEnd_1121065 := by
    simpa [prefixWord, tailWord_1121065, baseEnd_1121065] using wordTrace_append hprefix tailTrace_1121065
  have hstable : (prefixWord ++ tailWord_1121065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121065).length < 2 ^ (prefixWord ++ tailWord_1121065).sum := by decide
  have hdescent : baseEnd_1121065 < baseStart_1121065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121092 : List Nat := [2, 3, 4, 2, 1, 2, 1, 3, 1, 3]
def baseStart_1121092 : Nat := 118140960795 + 1121092 * 2 ^ 59
def prefixEnd_1121092 : Nat := 4983230072969 + 3 ^ 40 * 1121092 * 2
def baseEnd_1121092 : Nat := 383772702606955304062799

theorem tailTrace_1121092 : CollatzResearch.WordTrace tailWord_1121092 prefixEnd_1121092 383772702606955304062799 := by
  unfold tailWord_1121092
  simp only [CollatzResearch.WordTrace]
  refine ⟨20444792227241313057610765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27259722969655084076814353 20444792227241313057610765)
  ·
    refine ⟨7666797085215492396604037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20444792227241313057610765 7666797085215492396604037)
    ·
      refine ⟨1437524453477904824363257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7666797085215492396604037 1437524453477904824363257)
      ·
        refine ⟨1078143340108428618272443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1437524453477904824363257 1078143340108428618272443)
        ·
          refine ⟨1617215010162642927408665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1078143340108428618272443 1617215010162642927408665)
          ·
            refine ⟨1212911257621982195556499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1617215010162642927408665 1212911257621982195556499)
            ·
              refine ⟨1819366886432973293334749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212911257621982195556499 1819366886432973293334749)
              ·
                refine ⟨682262582412364985000531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1819366886432973293334749 682262582412364985000531)
                ·
                  refine ⟨1023393873618547477500797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682262582412364985000531 1023393873618547477500797)
                  ·
                    refine ⟨383772702606955304062799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1023393873618547477500797 383772702606955304062799)
                    ·
                      rfl

theorem cell22_1121092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_1121092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121092 prefixEnd_1121092 := by exact prefixLift 1121092
  have htrace : WordTrace (prefixWord ++ tailWord_1121092) baseStart_1121092 baseEnd_1121092 := by
    simpa [prefixWord, tailWord_1121092, baseEnd_1121092] using wordTrace_append hprefix tailTrace_1121092
  have hstable : (prefixWord ++ tailWord_1121092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121092).length < 2 ^ (prefixWord ++ tailWord_1121092).sum := by decide
  have hdescent : baseEnd_1121092 < baseStart_1121092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121114 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 4, 3]
def baseStart_1121114 : Nat := 118140960795 + 1121114 * 2 ^ 59
def prefixEnd_1121114 : Nat := 4983230072969 + 3 ^ 40 * 1121114 * 2
def baseEnd_1121114 : Nat := 383780233656554580012731

theorem tailTrace_1121114 : CollatzResearch.WordTrace tailWord_1121114 prefixEnd_1121114 383780233656554580012731 := by
  unfold tailWord_1121114
  simp only [CollatzResearch.WordTrace]
  refine ⟨10222596715100730968130599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27260257906935282581681597 10222596715100730968130599)
  ·
    refine ⟨15333895072651096452195899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10222596715100730968130599 15333895072651096452195899)
    ·
      refine ⟨23000842608976644678293849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15333895072651096452195899 23000842608976644678293849)
      ·
        refine ⟨17250631956732483508720387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23000842608976644678293849 17250631956732483508720387)
        ·
          refine ⟨25875947935098725263080581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17250631956732483508720387 25875947935098725263080581)
          ·
            refine ⟨4851740237831010986827609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25875947935098725263080581 4851740237831010986827609)
            ·
              refine ⟨3638805178373258240120707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4851740237831010986827609 3638805178373258240120707)
              ·
                refine ⟨5458207767559887360181061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3638805178373258240120707 5458207767559887360181061)
                ·
                  refine ⟨1023413956417478880033949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5458207767559887360181061 1023413956417478880033949)
                  ·
                    refine ⟨383780233656554580012731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1023413956417478880033949 383780233656554580012731)
                    ·
                      rfl

theorem cell22_1121114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_1121114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121114 prefixEnd_1121114 := by exact prefixLift 1121114
  have htrace : WordTrace (prefixWord ++ tailWord_1121114) baseStart_1121114 baseEnd_1121114 := by
    simpa [prefixWord, tailWord_1121114, baseEnd_1121114] using wordTrace_append hprefix tailTrace_1121114
  have hstable : (prefixWord ++ tailWord_1121114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121114).length < 2 ^ (prefixWord ++ tailWord_1121114).sum := by decide
  have hdescent : baseEnd_1121114 < baseStart_1121114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121116 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 6]
def baseStart_1121116 : Nat := 118140960795 + 1121116 * 2 ^ 59
def prefixEnd_1121116 : Nat := 4983230072969 + 3 ^ 40 * 1121116 * 2
def baseEnd_1121116 : Nat := 127926972765809080487575

theorem tailTrace_1121116 : CollatzResearch.WordTrace tailWord_1121116 prefixEnd_1121116 127926972765809080487575 := by
  unfold tailWord_1121116
  simp only [CollatzResearch.WordTrace]
  refine ⟨20445229903197839107047601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27260306537597118809396801 20445229903197839107047601)
  ·
    refine ⟨15333922427398379330285701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20445229903197839107047601 15333922427398379330285701)
    ·
      refine ⟨2875110455137196124428569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15333922427398379330285701 2875110455137196124428569)
      ·
        refine ⟨2156332841352897093321427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2875110455137196124428569 2156332841352897093321427)
        ·
          refine ⟨3234499262029345639982141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2156332841352897093321427 3234499262029345639982141)
          ·
            refine ⟨1212937223261004614993303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3234499262029345639982141 1212937223261004614993303)
            ·
              refine ⟨1819405834891506922489955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1212937223261004614993303 1819405834891506922489955)
              ·
                refine ⟨2729108752337260383734933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819405834891506922489955 2729108752337260383734933)
                ·
                  refine ⟨127926972765809080487575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2729108752337260383734933 127926972765809080487575)
                  ·
                    rfl

theorem cell22_1121116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_1121116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121116 prefixEnd_1121116 := by exact prefixLift 1121116
  have htrace : WordTrace (prefixWord ++ tailWord_1121116) baseStart_1121116 baseEnd_1121116 := by
    simpa [prefixWord, tailWord_1121116, baseEnd_1121116] using wordTrace_append hprefix tailTrace_1121116
  have hstable : (prefixWord ++ tailWord_1121116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121116).length < 2 ^ (prefixWord ++ tailWord_1121116).sum := by decide
  have hdescent : baseEnd_1121116 < baseStart_1121116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121127 : List Nat := [1, 1, 5, 1, 2, 2, 1, 9]
def baseStart_1121127 : Nat := 118140960795 + 1121127 * 2 ^ 59
def prefixEnd_1121127 : Nat := 4983230072969 + 3 ^ 40 * 1121127 * 2
def baseEnd_1121127 : Nat := 42642742646914097715299

theorem tailTrace_1121127 : CollatzResearch.WordTrace tailWord_1121127 prefixEnd_1121127 42642742646914097715299 := by
  unfold tailWord_1121127
  simp only [CollatzResearch.WordTrace]
  refine ⟨40890861009355827092745635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27260574006237218061830423 40890861009355827092745635)
  ·
    refine ⟨61336291514033740639118453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40890861009355827092745635 61336291514033740639118453)
    ·
      refine ⟨5750277329440663184917355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61336291514033740639118453 5750277329440663184917355)
      ·
        refine ⟨8625415994160994777376033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5750277329440663184917355 8625415994160994777376033)
        ·
          refine ⟨6469061995620746083032025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8625415994160994777376033 6469061995620746083032025)
          ·
            refine ⟨4851796496715559562274019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6469061995620746083032025 4851796496715559562274019)
            ·
              refine ⟨7277694745073339343411029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4851796496715559562274019 7277694745073339343411029)
              ·
                refine ⟨42642742646914097715299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7277694745073339343411029 42642742646914097715299)
                ·
                  rfl

theorem cell22_1121127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 9].length) (baseStart_1121127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121127 prefixEnd_1121127 := by exact prefixLift 1121127
  have htrace : WordTrace (prefixWord ++ tailWord_1121127) baseStart_1121127 baseEnd_1121127 := by
    simpa [prefixWord, tailWord_1121127, baseEnd_1121127] using wordTrace_append hprefix tailTrace_1121127
  have hstable : (prefixWord ++ tailWord_1121127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121127).length < 2 ^ (prefixWord ++ tailWord_1121127).sum := by decide
  have hdescent : baseEnd_1121127 < baseStart_1121127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121131 : List Nat := [1, 1, 1, 1, 2, 2, 8, 1, 2, 3]
def baseStart_1121131 : Nat := 118140960795 + 1121131 * 2 ^ 59
def prefixEnd_1121131 : Nat := 4983230072969 + 3 ^ 40 * 1121131 * 2
def baseEnd_1121131 : Nat := 383786053103972202337679

theorem tailTrace_1121131 : CollatzResearch.WordTrace tailWord_1121131 prefixEnd_1121131 383786053103972202337679 := by
  unfold tailWord_1121131
  simp only [CollatzResearch.WordTrace]
  refine ⟨40891006901341335775891247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27260671267560890517260831 40891006901341335775891247)
  ·
    refine ⟨61336510352012003663836871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40891006901341335775891247 61336510352012003663836871)
    ·
      refine ⟨92004765528018005495755307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61336510352012003663836871 92004765528018005495755307)
      ·
        refine ⟨138007148292027008243632961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92004765528018005495755307 138007148292027008243632961)
        ·
          refine ⟨103505361219020256182724721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138007148292027008243632961 103505361219020256182724721)
          ·
            refine ⟨77629020914265192137043541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103505361219020256182724721 77629020914265192137043541)
            ·
              refine ⟨909715088839045220355979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 77629020914265192137043541 909715088839045220355979)
              ·
                refine ⟨1364572633258567830533969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909715088839045220355979 1364572633258567830533969)
                ·
                  refine ⟨1023429474943925872900477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1364572633258567830533969 1023429474943925872900477)
                  ·
                    refine ⟨383786053103972202337679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1023429474943925872900477 383786053103972202337679)
                    ·
                      rfl

theorem cell22_1121131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 2, 3].length) (baseStart_1121131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121131 prefixEnd_1121131 := by exact prefixLift 1121131
  have htrace : WordTrace (prefixWord ++ tailWord_1121131) baseStart_1121131 baseEnd_1121131 := by
    simpa [prefixWord, tailWord_1121131, baseEnd_1121131] using wordTrace_append hprefix tailTrace_1121131
  have hstable : (prefixWord ++ tailWord_1121131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121131).length < 2 ^ (prefixWord ++ tailWord_1121131).sum := by decide
  have hdescent : baseEnd_1121131 < baseStart_1121131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121187 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 1, 7]
def baseStart_1121187 : Nat := 118140960795 + 1121187 * 2 ^ 59
def prefixEnd_1121187 : Nat := 4983230072969 + 3 ^ 40 * 1121187 * 2
def baseEnd_1121187 : Nat := 383805223048406722937507

theorem tailTrace_1121187 : CollatzResearch.WordTrace tailWord_1121187 prefixEnd_1121187 383805223048406722937507 := by
  unfold tailWord_1121187
  simp only [CollatzResearch.WordTrace]
  refine ⟨40893049389138457339929815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27262032926092304893286543 40893049389138457339929815)
  ·
    refine ⟨61339574083707686009894723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40893049389138457339929815 61339574083707686009894723)
    ·
      refine ⟨92009361125561529014842085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61339574083707686009894723 92009361125561529014842085)
      ·
        refine ⟨17251755211042786690282891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92009361125561529014842085 17251755211042786690282891)
        ·
          refine ⟨25877632816564180035424337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17251755211042786690282891 25877632816564180035424337)
          ·
            refine ⟨19408224612423135026568253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25877632816564180035424337 19408224612423135026568253)
            ·
              refine ⟨7278084229658675634963095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19408224612423135026568253 7278084229658675634963095)
              ·
                refine ⟨10917126344488013452444643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7278084229658675634963095 10917126344488013452444643)
                ·
                  refine ⟨16375689516732020178666965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10917126344488013452444643 16375689516732020178666965)
                  ·
                    refine ⟨383805223048406722937507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16375689516732020178666965 383805223048406722937507)
                    ·
                      rfl

theorem cell22_1121187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 7].length) (baseStart_1121187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121187 prefixEnd_1121187 := by exact prefixLift 1121187
  have htrace : WordTrace (prefixWord ++ tailWord_1121187) baseStart_1121187 baseEnd_1121187 := by
    simpa [prefixWord, tailWord_1121187, baseEnd_1121187] using wordTrace_append hprefix tailTrace_1121187
  have hstable : (prefixWord ++ tailWord_1121187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121187).length < 2 ^ (prefixWord ++ tailWord_1121187).sum := by decide
  have hdescent : baseEnd_1121187 < baseStart_1121187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121219 : List Nat := [1, 1, 1, 3, 1, 1, 2, 7, 1, 4]
def baseStart_1121219 : Nat := 118140960795 + 1121219 * 2 ^ 59
def prefixEnd_1121219 : Nat := 4983230072969 + 3 ^ 40 * 1121219 * 2
def baseEnd_1121219 : Nat := 383816177302369306137409

theorem tailTrace_1121219 : CollatzResearch.WordTrace tailWord_1121219 prefixEnd_1121219 383816177302369306137409 := by
  unfold tailWord_1121219
  simp only [CollatzResearch.WordTrace]
  refine ⟨40894216525022526805094711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27262811016681684536729807 40894216525022526805094711)
  ·
    refine ⟨61341324787533790207642067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40894216525022526805094711 61341324787533790207642067)
    ·
      refine ⟨92011987181300685311463101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61341324787533790207642067 92011987181300685311463101)
      ·
        refine ⟨34504495192987756991798663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92011987181300685311463101 34504495192987756991798663)
        ·
          refine ⟨51756742789481635487697995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34504495192987756991798663 51756742789481635487697995)
          ·
            refine ⟨77635114184222453231546993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51756742789481635487697995 77635114184222453231546993)
            ·
              refine ⟨58226335638166839923660245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77635114184222453231546993 58226335638166839923660245)
              ·
                refine ⟨1364679741519535310710787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 58226335638166839923660245 1364679741519535310710787)
                ·
                  refine ⟨2047019612279302966066181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1364679741519535310710787 2047019612279302966066181)
                  ·
                    refine ⟨383816177302369306137409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2047019612279302966066181 383816177302369306137409)
                    ·
                      rfl

theorem cell22_1121219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 4].length) (baseStart_1121219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121219 prefixEnd_1121219 := by exact prefixLift 1121219
  have htrace : WordTrace (prefixWord ++ tailWord_1121219) baseStart_1121219 baseEnd_1121219 := by
    simpa [prefixWord, tailWord_1121219, baseEnd_1121219] using wordTrace_append hprefix tailTrace_1121219
  have hstable : (prefixWord ++ tailWord_1121219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121219).length < 2 ^ (prefixWord ++ tailWord_1121219).sum := by decide
  have hdescent : baseEnd_1121219 < baseStart_1121219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121264 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 2, 4]
def baseStart_1121264 : Nat := 118140960795 + 1121264 * 2 ^ 59
def prefixEnd_1121264 : Nat := 4983230072969 + 3 ^ 40 * 1121264 * 2
def baseEnd_1121264 : Nat := 383831581722004188762271

theorem tailTrace_1121264 : CollatzResearch.WordTrace tailWord_1121264 prefixEnd_1121264 383831581722004188762271 := by
  unfold tailWord_1121264
  simp only [CollatzResearch.WordTrace]
  refine ⟨20447928904929749745241423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27263905206572999660321897 20447928904929749745241423)
  ·
    refine ⟨30671893357394624617862135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20447928904929749745241423 30671893357394624617862135)
    ·
      refine ⟨46007840036091936926793203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30671893357394624617862135 46007840036091936926793203)
      ·
        refine ⟨69011760054137905390189805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46007840036091936926793203 69011760054137905390189805)
        ·
          refine ⟨25879410020301714521321177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69011760054137905390189805 25879410020301714521321177)
          ·
            refine ⟨19409557515226285890990883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25879410020301714521321177 19409557515226285890990883)
            ·
              refine ⟨29114336272839428836486325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19409557515226285890990883 29114336272839428836486325)
              ·
                refine ⟨2729469025578696453420593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29114336272839428836486325 2729469025578696453420593)
                ·
                  refine ⟨2047101769184022340065445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2729469025578696453420593 2047101769184022340065445)
                  ·
                    refine ⟨383831581722004188762271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2047101769184022340065445 383831581722004188762271)
                    ·
                      rfl

theorem cell22_1121264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_1121264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121264 prefixEnd_1121264 := by exact prefixLift 1121264
  have htrace : WordTrace (prefixWord ++ tailWord_1121264) baseStart_1121264 baseEnd_1121264 := by
    simpa [prefixWord, tailWord_1121264, baseEnd_1121264] using wordTrace_append hprefix tailTrace_1121264
  have hstable : (prefixWord ++ tailWord_1121264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121264).length < 2 ^ (prefixWord ++ tailWord_1121264).sum := by decide
  have hdescent : baseEnd_1121264 < baseStart_1121264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121281 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1121281 : Nat := 118140960795 + 1121281 * 2 ^ 59
def prefixEnd_1121281 : Nat := 4983230072969 + 3 ^ 40 * 1121281 * 2
def baseEnd_1121281 : Nat := 383837401169421811087219

theorem tailTrace_1121281 : CollatzResearch.WordTrace tailWord_1121281 prefixEnd_1121281 383837401169421811087219 := by
  unfold tailWord_1121281
  simp only [CollatzResearch.WordTrace]
  refine ⟨40896477850797911393851697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27264318567198607595901131 40896477850797911393851697)
  ·
    refine ⟨30672358388098433545388773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40896477850797911393851697 30672358388098433545388773)
    ·
      refine ⟨5751067197768456289760395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30672358388098433545388773 5751067197768456289760395)
      ·
        refine ⟨8626600796652684434640593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5751067197768456289760395 8626600796652684434640593)
        ·
          refine ⟨6469950597489513325980445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8626600796652684434640593 6469950597489513325980445)
          ·
            refine ⟨2426231474058567497242667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6469950597489513325980445 2426231474058567497242667)
            ·
              refine ⟨3639347211087851245864001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2426231474058567497242667 3639347211087851245864001)
              ·
                refine ⟨2729510408315888434398001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3639347211087851245864001 2729510408315888434398001)
                ·
                  refine ⟨2047132806236916325798501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2729510408315888434398001 2047132806236916325798501)
                  ·
                    refine ⟨383837401169421811087219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2047132806236916325798501 383837401169421811087219)
                    ·
                      rfl

theorem cell22_1121281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1121281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121281 prefixEnd_1121281 := by exact prefixLift 1121281
  have htrace : WordTrace (prefixWord ++ tailWord_1121281) baseStart_1121281 baseEnd_1121281 := by
    simpa [prefixWord, tailWord_1121281, baseEnd_1121281] using wordTrace_append hprefix tailTrace_1121281
  have hstable : (prefixWord ++ tailWord_1121281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121281).length < 2 ^ (prefixWord ++ tailWord_1121281).sum := by decide
  have hdescent : baseEnd_1121281 < baseStart_1121281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121328 : List Nat := [2, 1, 1, 1, 2, 4, 2, 5, 1, 3]
def baseStart_1121328 : Nat := 118140960795 + 1121328 * 2 ^ 59
def prefixEnd_1121328 : Nat := 4983230072969 + 3 ^ 40 * 1121328 * 2
def baseEnd_1121328 : Nat := 383853490229929355162075

theorem tailTrace_1121328 : CollatzResearch.WordTrace tailWord_1121328 prefixEnd_1121328 383853490229929355162075 := by
  unfold tailWord_1121328
  simp only [CollatzResearch.WordTrace]
  refine ⟨20449096040813819210406319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27265461387751758947208425 20449096040813819210406319)
  ·
    refine ⟨30673644061220728815609479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20449096040813819210406319 30673644061220728815609479)
    ·
      refine ⟨46010466091831093223414219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30673644061220728815609479 46010466091831093223414219)
      ·
        refine ⟨69015699137746639835121329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46010466091831093223414219 69015699137746639835121329)
        ·
          refine ⟨51761774353309979876340997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69015699137746639835121329 51761774353309979876340997)
          ·
            refine ⟨9705332691245621226813937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51761774353309979876340997 9705332691245621226813937)
            ·
              refine ⟨7278999518434215920110453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9705332691245621226813937 7278999518434215920110453)
              ·
                refine ⟨682406204853207742510355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7278999518434215920110453 682406204853207742510355)
                ·
                  refine ⟨1023609307279811613765533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682406204853207742510355 1023609307279811613765533)
                  ·
                    refine ⟨383853490229929355162075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1023609307279811613765533 383853490229929355162075)
                    ·
                      rfl

theorem cell22_1121328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 1, 3].length) (baseStart_1121328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121328 prefixEnd_1121328 := by exact prefixLift 1121328
  have htrace : WordTrace (prefixWord ++ tailWord_1121328) baseStart_1121328 baseEnd_1121328 := by
    simpa [prefixWord, tailWord_1121328, baseEnd_1121328] using wordTrace_append hprefix tailTrace_1121328
  have hstable : (prefixWord ++ tailWord_1121328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121328).length < 2 ^ (prefixWord ++ tailWord_1121328).sum := by decide
  have hdescent : baseEnd_1121328 < baseStart_1121328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121341 : List Nat := [1, 4, 1, 3, 1, 2, 1, 4, 5]
def baseStart_1121341 : Nat := 118140960795 + 1121341 * 2 ^ 59
def prefixEnd_1121341 : Nat := 4983230072969 + 3 ^ 40 * 1121341 * 2
def baseEnd_1121341 : Nat := 127952646798533884862345

theorem tailTrace_1121341 : CollatzResearch.WordTrace tailWord_1121341 prefixEnd_1121341 127952646798533884862345 := by
  unfold tailWord_1121341
  simp only [CollatzResearch.WordTrace]
  refine ⟨40898666230580541641035877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27265777487053694427357251 40898666230580541641035877)
  ·
    refine ⟨7668499918233851557694227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40898666230580541641035877 7668499918233851557694227)
    ·
      refine ⟨11502749877350777336541341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7668499918233851557694227 11502749877350777336541341)
      ·
        refine ⟨4313531204006541501203003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11502749877350777336541341 4313531204006541501203003)
        ·
          refine ⟨6470296806009812251804505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4313531204006541501203003 6470296806009812251804505)
          ·
            refine ⟨4852722604507359188853379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6470296806009812251804505 4852722604507359188853379)
            ·
              refine ⟨7279083906761038783280069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4852722604507359188853379 7279083906761038783280069)
              ·
                refine ⟨1364828232517694771865013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7279083906761038783280069 1364828232517694771865013)
                ·
                  refine ⟨127952646798533884862345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1364828232517694771865013 127952646798533884862345)
                  ·
                    rfl

theorem cell22_1121341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_1121341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121341 prefixEnd_1121341 := by exact prefixLift 1121341
  have htrace : WordTrace (prefixWord ++ tailWord_1121341) baseStart_1121341 baseEnd_1121341 := by
    simpa [prefixWord, tailWord_1121341, baseEnd_1121341] using wordTrace_append hprefix tailTrace_1121341
  have hstable : (prefixWord ++ tailWord_1121341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121341).length < 2 ^ (prefixWord ++ tailWord_1121341).sum := by decide
  have hdescent : baseEnd_1121341 < baseStart_1121341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121431 : List Nat := [1, 1, 3, 3, 3, 2, 1, 8]
def baseStart_1121431 : Nat := 118140960795 + 1121431 * 2 ^ 59
def prefixEnd_1121431 : Nat := 4983230072969 + 3 ^ 40 * 1121431 * 2
def baseEnd_1121431 : Nat := 42654305470541268870751

theorem tailTrace_1121431 : CollatzResearch.WordTrace tailWord_1121431 prefixEnd_1121431 42654305470541268870751 := by
  unfold tailWord_1121431
  simp only [CollatzResearch.WordTrace]
  refine ⟨40901948800254487011812147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27267965866836324674541431 40901948800254487011812147)
  ·
    refine ⟨61352923200381730517718221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40901948800254487011812147 61352923200381730517718221)
    ·
      refine ⟨23007346200143148944144333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61352923200381730517718221 23007346200143148944144333)
      ·
        refine ⟨8627754825053680854054125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23007346200143148944144333 8627754825053680854054125)
        ·
          refine ⟨3235408059395130320270297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8627754825053680854054125 3235408059395130320270297)
          ·
            refine ⟨2426556044546347740202723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3235408059395130320270297 2426556044546347740202723)
            ·
              refine ⟨3639834066819521610304085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2426556044546347740202723 3639834066819521610304085)
              ·
                refine ⟨42654305470541268870751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3639834066819521610304085 42654305470541268870751)
                ·
                  rfl

theorem cell22_1121431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 8].length) (baseStart_1121431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121431 prefixEnd_1121431 := by exact prefixLift 1121431
  have htrace : WordTrace (prefixWord ++ tailWord_1121431) baseStart_1121431 baseEnd_1121431 := by
    simpa [prefixWord, tailWord_1121431, baseEnd_1121431] using wordTrace_append hprefix tailTrace_1121431
  have hstable : (prefixWord ++ tailWord_1121431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121431).length < 2 ^ (prefixWord ++ tailWord_1121431).sum := by decide
  have hdescent : baseEnd_1121431 < baseStart_1121431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121450 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1121450 : Nat := 118140960795 + 1121450 * 2 ^ 59
def prefixEnd_1121450 : Nat := 4983230072969 + 3 ^ 40 * 1121450 * 2
def baseEnd_1121450 : Nat := 383895253323161703611701

theorem tailTrace_1121450 : CollatzResearch.WordTrace tailWord_1121450 prefixEnd_1121450 383895253323161703611701 := by
  unfold tailWord_1121450
  simp only [CollatzResearch.WordTrace]
  refine ⟨10225660446796413314188451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27268427858123768837835869 10225660446796413314188451)
  ·
    refine ⟨15338490670194619971282677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10225660446796413314188451 15338490670194619971282677)
    ·
      refine ⟨1437983500330745622307751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15338490670194619971282677 1437983500330745622307751)
      ·
        refine ⟨2156975250496118433461627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1437983500330745622307751 2156975250496118433461627)
        ·
          refine ⟨3235462875744177650192441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2156975250496118433461627 3235462875744177650192441)
          ·
            refine ⟨2426597156808133237644331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3235462875744177650192441 2426597156808133237644331)
            ·
              refine ⟨3639895735212199856466497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2426597156808133237644331 3639895735212199856466497)
              ·
                refine ⟨2729921801409149892349873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3639895735212199856466497 2729921801409149892349873)
                ·
                  refine ⟨2047441351056862419262405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2729921801409149892349873 2047441351056862419262405)
                  ·
                    refine ⟨383895253323161703611701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2047441351056862419262405 383895253323161703611701)
                    ·
                      rfl

theorem cell22_1121450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1121450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121450 prefixEnd_1121450 := by exact prefixLift 1121450
  have htrace : WordTrace (prefixWord ++ tailWord_1121450) baseStart_1121450 baseEnd_1121450 := by
    simpa [prefixWord, tailWord_1121450, baseEnd_1121450] using wordTrace_append hprefix tailTrace_1121450
  have hstable : (prefixWord ++ tailWord_1121450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121450).length < 2 ^ (prefixWord ++ tailWord_1121450).sum := by decide
  have hdescent : baseEnd_1121450 < baseStart_1121450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121514 : List Nat := [3, 1, 3, 1, 1, 5, 2, 2, 1, 3]
def baseStart_1121514 : Nat := 118140960795 + 1121514 * 2 ^ 59
def prefixEnd_1121514 : Nat := 4983230072969 + 3 ^ 40 * 1121514 * 2
def baseEnd_1121514 : Nat := 383917161831086870011505

theorem tailTrace_1121514 : CollatzResearch.WordTrace tailWord_1121514 prefixEnd_1121514 383917161831086870011505 := by
  unfold tailWord_1121514
  simp only [CollatzResearch.WordTrace]
  refine ⟨10226244014738448046770899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27269984039302528124722397 10226244014738448046770899)
  ·
    refine ⟨15339366022107672070156349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10226244014738448046770899 15339366022107672070156349)
    ·
      refine ⟨5752262258290377026308631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15339366022107672070156349 5752262258290377026308631)
      ·
        refine ⟨8628393387435565539462947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5752262258290377026308631 8628393387435565539462947)
        ·
          refine ⟨12942590081153348309194421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8628393387435565539462947 12942590081153348309194421)
          ·
            refine ⟨1213367820108126403986977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12942590081153348309194421 1213367820108126403986977)
            ·
              refine ⟨910025865081094802990233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1213367820108126403986977 910025865081094802990233)
              ·
                refine ⟨682519398810821102242675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 910025865081094802990233 682519398810821102242675)
                ·
                  refine ⟨1023779098216231653364013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682519398810821102242675 1023779098216231653364013)
                  ·
                    refine ⟨383917161831086870011505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1023779098216231653364013 383917161831086870011505)
                    ·
                      rfl

theorem cell22_1121514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_1121514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121514 prefixEnd_1121514 := by exact prefixLift 1121514
  have htrace : WordTrace (prefixWord ++ tailWord_1121514) baseStart_1121514 baseEnd_1121514 := by
    simpa [prefixWord, tailWord_1121514, baseEnd_1121514] using wordTrace_append hprefix tailTrace_1121514
  have hstable : (prefixWord ++ tailWord_1121514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121514).length < 2 ^ (prefixWord ++ tailWord_1121514).sum := by decide
  have hdescent : baseEnd_1121514 < baseStart_1121514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121521 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 6]
def baseStart_1121521 : Nat := 118140960795 + 1121521 * 2 ^ 59
def prefixEnd_1121521 : Nat := 4983230072969 + 3 ^ 40 * 1121521 * 2
def baseEnd_1121521 : Nat := 127973186024713728362161

theorem tailTrace_1121521 : CollatzResearch.WordTrace tailWord_1121521 prefixEnd_1121521 127973186024713728362161 := by
  unfold tailWord_1121521
  simp only [CollatzResearch.WordTrace]
  refine ⟨40905231369928432382588417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27270154246618954921725611 40905231369928432382588417)
  ·
    refine ⟨30678923527446324286941313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40905231369928432382588417 30678923527446324286941313)
    ·
      refine ⟨23009192645584743215205985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30678923527446324286941313 23009192645584743215205985)
      ·
        refine ⟨17256894484188557411404489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23009192645584743215205985 17256894484188557411404489)
        ·
          refine ⟨12942670863141418058553367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17256894484188557411404489 12942670863141418058553367)
          ·
            refine ⟨19414006294712127087830051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12942670863141418058553367 19414006294712127087830051)
            ·
              refine ⟨29121009442068190631745077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19414006294712127087830051 29121009442068190631745077)
              ·
                refine ⟨2730094635193892871726101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29121009442068190631745077 2730094635193892871726101)
                ·
                  refine ⟨127973186024713728362161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2730094635193892871726101 127973186024713728362161)
                  ·
                    rfl

theorem cell22_1121521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_1121521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121521 prefixEnd_1121521 := by exact prefixLift 1121521
  have htrace : WordTrace (prefixWord ++ tailWord_1121521) baseStart_1121521 baseEnd_1121521 := by
    simpa [prefixWord, tailWord_1121521, baseEnd_1121521] using wordTrace_append hprefix tailTrace_1121521
  have hstable : (prefixWord ++ tailWord_1121521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121521).length < 2 ^ (prefixWord ++ tailWord_1121521).sum := by decide
  have hdescent : baseEnd_1121521 < baseStart_1121521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121553 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 4, 3]
def baseStart_1121553 : Nat := 118140960795 + 1121553 * 2 ^ 59
def prefixEnd_1121553 : Nat := 4983230072969 + 3 ^ 40 * 1121553 * 2
def baseEnd_1121553 : Nat := 383930512328103768286385

theorem tailTrace_1121553 : CollatzResearch.WordTrace tailWord_1121553 prefixEnd_1121553 383930512328103768286385 := by
  unfold tailWord_1121553
  simp only [CollatzResearch.WordTrace]
  refine ⟨40906398505812501847753313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27270932337208334565168875 40906398505812501847753313)
  ·
    refine ⟨30679798879359376385814985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40906398505812501847753313 30679798879359376385814985)
    ·
      refine ⟨23009849159519532289361239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30679798879359376385814985 23009849159519532289361239)
      ·
        refine ⟨34514773739279298434041859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23009849159519532289361239 34514773739279298434041859)
        ·
          refine ⟨51772160608918947651062789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34514773739279298434041859 51772160608918947651062789)
          ·
            refine ⟨9707280114172302684574273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51772160608918947651062789 9707280114172302684574273)
            ·
              refine ⟨7280460085629227013430705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9707280114172302684574273 7280460085629227013430705)
              ·
                refine ⟨5460345064221920260073029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7280460085629227013430705 5460345064221920260073029)
                ·
                  refine ⟨1023814699541610048763693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5460345064221920260073029 1023814699541610048763693)
                  ·
                    refine ⟨383930512328103768286385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1023814699541610048763693 383930512328103768286385)
                    ·
                      rfl

theorem cell22_1121553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_1121553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121553 prefixEnd_1121553 := by exact prefixLift 1121553
  have htrace : WordTrace (prefixWord ++ tailWord_1121553) baseStart_1121553 baseEnd_1121553 := by
    simpa [prefixWord, tailWord_1121553, baseEnd_1121553] using wordTrace_append hprefix tailTrace_1121553
  have hstable : (prefixWord ++ tailWord_1121553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121553).length < 2 ^ (prefixWord ++ tailWord_1121553).sum := by decide
  have hdescent : baseEnd_1121553 < baseStart_1121553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121587 : List Nat := [1, 1, 1, 2, 5, 3, 3, 1, 2, 3]
def baseStart_1121587 : Nat := 118140960795 + 1121587 * 2 ^ 59
def prefixEnd_1121587 : Nat := 4983230072969 + 3 ^ 40 * 1121587 * 2
def baseEnd_1121587 : Nat := 383942151222939012936281

theorem tailTrace_1121587 : CollatzResearch.WordTrace tailWord_1121587 prefixEnd_1121587 383942151222939012936281 := by
  unfold tailWord_1121587
  simp only [CollatzResearch.WordTrace]
  refine ⟨40907638587689325654491015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27271759058459550436327343 40907638587689325654491015)
  ·
    refine ⟨61361457881533988481736523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40907638587689325654491015 61361457881533988481736523)
    ·
      refine ⟨92042186822300982722604785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61361457881533988481736523 92042186822300982722604785)
      ·
        refine ⟨69031640116725737041953589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92042186822300982722604785 69031640116725737041953589)
        ·
          refine ⟨6471716260943037847683149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69031640116725737041953589 6471716260943037847683149)
          ·
            refine ⟨2426893597853639192881181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6471716260943037847683149 2426893597853639192881181)
            ·
              refine ⟨910085099195114697330443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2426893597853639192881181 910085099195114697330443)
              ·
                refine ⟨1365127648792672045995665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910085099195114697330443 1365127648792672045995665)
                ·
                  refine ⟨1023845736594504034496749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1365127648792672045995665 1023845736594504034496749)
                  ·
                    refine ⟨383942151222939012936281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1023845736594504034496749 383942151222939012936281)
                    ·
                      rfl

theorem cell22_1121587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 2, 3].length) (baseStart_1121587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121587 prefixEnd_1121587 := by exact prefixLift 1121587
  have htrace : WordTrace (prefixWord ++ tailWord_1121587) baseStart_1121587 baseEnd_1121587 := by
    simpa [prefixWord, tailWord_1121587, baseEnd_1121587] using wordTrace_append hprefix tailTrace_1121587
  have hstable : (prefixWord ++ tailWord_1121587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121587).length < 2 ^ (prefixWord ++ tailWord_1121587).sum := by decide
  have hdescent : baseEnd_1121587 < baseStart_1121587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121598 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_1121598 : Nat := 118140960795 + 1121598 * 2 ^ 59
def prefixEnd_1121598 : Nat := 4983230072969 + 3 ^ 40 * 1121598 * 2
def baseEnd_1121598 : Nat := 383945916747738650911247

theorem tailTrace_1121598 : CollatzResearch.WordTrace tailWord_1121598 prefixEnd_1121598 383945916747738650911247 := by
  unfold tailWord_1121598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5113504973831184316642681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27272026527099649688760965 5113504973831184316642681)
  ·
    refine ⟨3835128730373388237482011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5113504973831184316642681 3835128730373388237482011)
    ·
      refine ⟨5752693095560082356223017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3835128730373388237482011 5752693095560082356223017)
      ·
        refine ⟨4314519821670061767167263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5752693095560082356223017 4314519821670061767167263)
        ·
          refine ⟨6471779732505092650750895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4314519821670061767167263 6471779732505092650750895)
          ·
            refine ⟨9707669598757638976126343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6471779732505092650750895 9707669598757638976126343)
            ·
              refine ⟨14561504398136458464189515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9707669598757638976126343 14561504398136458464189515)
              ·
                refine ⟨21842256597204687696284273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14561504398136458464189515 21842256597204687696284273)
                ·
                  refine ⟨16381692447903515772213205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21842256597204687696284273 16381692447903515772213205)
                  ·
                    refine ⟨383945916747738650911247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16381692447903515772213205 383945916747738650911247)
                    ·
                      rfl

theorem cell22_1121598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_1121598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121598 prefixEnd_1121598 := by exact prefixLift 1121598
  have htrace : WordTrace (prefixWord ++ tailWord_1121598) baseStart_1121598 baseEnd_1121598 := by
    simpa [prefixWord, tailWord_1121598, baseEnd_1121598] using wordTrace_append hprefix tailTrace_1121598
  have hstable : (prefixWord ++ tailWord_1121598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121598).length < 2 ^ (prefixWord ++ tailWord_1121598).sum := by decide
  have hdescent : baseEnd_1121598 < baseStart_1121598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121632 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 3, 3]
def baseStart_1121632 : Nat := 118140960795 + 1121632 * 2 ^ 59
def prefixEnd_1121632 : Nat := 4983230072969 + 3 ^ 40 * 1121632 * 2
def baseEnd_1121632 : Nat := 383957555642573895561143

theorem tailTrace_1121632 : CollatzResearch.WordTrace tailWord_1121632 prefixEnd_1121632 383957555642573895561143 := by
  unfold tailWord_1121632
  simp only [CollatzResearch.WordTrace]
  refine ⟨20454639936263149169939575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27272853248350865559919433 20454639936263149169939575)
  ·
    refine ⟨30681959904394723754909363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20454639936263149169939575 30681959904394723754909363)
    ·
      refine ⟨46022939856592085632364045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30681959904394723754909363 46022939856592085632364045)
      ·
        refine ⟨17258602446222032112136517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46022939856592085632364045 17258602446222032112136517)
        ·
          refine ⟨3235987958666631021025597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17258602446222032112136517 3235987958666631021025597)
          ·
            refine ⟨1213495484499986632884599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3235987958666631021025597 1213495484499986632884599)
            ·
              refine ⟨1820243226749979949326899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213495484499986632884599 1820243226749979949326899)
              ·
                refine ⟨2730364840124969923990349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820243226749979949326899 2730364840124969923990349)
                ·
                  refine ⟨1023886815046863721496381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2730364840124969923990349 1023886815046863721496381)
                  ·
                    refine ⟨383957555642573895561143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1023886815046863721496381 383957555642573895561143)
                    ·
                      rfl

theorem cell22_1121632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 3, 3].length) (baseStart_1121632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121632 prefixEnd_1121632 := by exact prefixLift 1121632
  have htrace : WordTrace (prefixWord ++ tailWord_1121632) baseStart_1121632 baseEnd_1121632 := by
    simpa [prefixWord, tailWord_1121632, baseEnd_1121632] using wordTrace_append hprefix tailTrace_1121632
  have hstable : (prefixWord ++ tailWord_1121632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121632).length < 2 ^ (prefixWord ++ tailWord_1121632).sum := by decide
  have hdescent : baseEnd_1121632 < baseStart_1121632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121645 : List Nat := [1, 5, 1, 1, 1, 4, 1, 3, 5]
def baseStart_1121645 : Nat := 118140960795 + 1121645 * 2 ^ 59
def prefixEnd_1121645 : Nat := 4983230072969 + 3 ^ 40 * 1121645 * 2
def baseEnd_1121645 : Nat := 127987335269415398328701

theorem tailTrace_1121645 : CollatzResearch.WordTrace tailWord_1121645 prefixEnd_1121645 127987335269415398328701 := by
  unfold tailWord_1121645
  simp only [CollatzResearch.WordTrace]
  refine ⟨40909754021479201560102389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27273169347652801040068259 40909754021479201560102389)
  ·
    refine ⟨3835289439513675146259599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40909754021479201560102389 3835289439513675146259599)
    ·
      refine ⟨5752934159270512719389399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3835289439513675146259599 5752934159270512719389399)
      ·
        refine ⟨8629401238905769079084099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5752934159270512719389399 8629401238905769079084099)
        ·
          refine ⟨12944101858358653618626149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8629401238905769079084099 12944101858358653618626149)
          ·
            refine ⟨2427019098442247553492403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12944101858358653618626149 2427019098442247553492403)
            ·
              refine ⟨3640528647663371330238605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2427019098442247553492403 3640528647663371330238605)
              ·
                refine ⟨1365198242873764248839477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3640528647663371330238605 1365198242873764248839477)
                ·
                  refine ⟨127987335269415398328701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1365198242873764248839477 127987335269415398328701)
                  ·
                    rfl

theorem cell22_1121645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_1121645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121645 prefixEnd_1121645 := by exact prefixLift 1121645
  have htrace : WordTrace (prefixWord ++ tailWord_1121645) baseStart_1121645 baseEnd_1121645 := by
    simpa [prefixWord, tailWord_1121645, baseEnd_1121645] using wordTrace_append hprefix tailTrace_1121645
  have hstable : (prefixWord ++ tailWord_1121645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121645).length < 2 ^ (prefixWord ++ tailWord_1121645).sum := by decide
  have hdescent : baseEnd_1121645 < baseStart_1121645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121658 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_1121658 : Nat := 118140960795 + 1121658 * 2 ^ 59
def prefixEnd_1121658 : Nat := 4983230072969 + 3 ^ 40 * 1121658 * 2
def baseEnd_1121658 : Nat := 383966455973918494411063

theorem tailTrace_1121658 : CollatzResearch.WordTrace tailWord_1121658 prefixEnd_1121658 383966455973918494411063 := by
  unfold tailWord_1121658
  simp only [CollatzResearch.WordTrace]
  refine ⟨10227557042608026195081407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27273485446954736520217085 10227557042608026195081407)
  ·
    refine ⟨15341335563912039292622111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10227557042608026195081407 15341335563912039292622111)
    ·
      refine ⟨23012003345868058938933167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15341335563912039292622111 23012003345868058938933167)
      ·
        refine ⟨34518005018802088408399751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23012003345868058938933167 34518005018802088408399751)
        ·
          refine ⟨51777007528203132612599627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34518005018802088408399751 51777007528203132612599627)
          ·
            refine ⟨77665511292304698918899441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51777007528203132612599627 77665511292304698918899441)
            ·
              refine ⟨58249133469228524189174581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77665511292304698918899441 58249133469228524189174581)
              ·
                refine ⟨5460856262740174142735117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58249133469228524189174581 5460856262740174142735117)
                ·
                  refine ⟨2047821098527565303525669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5460856262740174142735117 2047821098527565303525669)
                  ·
                    refine ⟨383966455973918494411063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2047821098527565303525669 383966455973918494411063)
                    ·
                      rfl

theorem cell22_1121658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_1121658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121658 prefixEnd_1121658 := by exact prefixLift 1121658
  have htrace : WordTrace (prefixWord ++ tailWord_1121658) baseStart_1121658 baseEnd_1121658 := by
    simpa [prefixWord, tailWord_1121658, baseEnd_1121658] using wordTrace_append hprefix tailTrace_1121658
  have hstable : (prefixWord ++ tailWord_1121658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121658).length < 2 ^ (prefixWord ++ tailWord_1121658).sum := by decide
  have hdescent : baseEnd_1121658 < baseStart_1121658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121720 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 2, 4]
def baseStart_1121720 : Nat := 118140960795 + 1121720 * 2 ^ 59
def prefixEnd_1121720 : Nat := 4983230072969 + 3 ^ 40 * 1121720 * 2
def baseEnd_1121720 : Nat := 383987679840970999360873

theorem tailTrace_1121720 : CollatzResearch.WordTrace tailWord_1121720 prefixEnd_1121720 383987679840970999360873 := by
  unfold tailWord_1121720
  simp only [CollatzResearch.WordTrace]
  refine ⟨20456244748103744684541307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27274992997471659579388409 20456244748103744684541307)
  ·
    refine ⟨30684367122155617026811961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20456244748103744684541307 30684367122155617026811961)
    ·
      refine ⟨23013275341616712770108971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30684367122155617026811961 23013275341616712770108971)
      ·
        refine ⟨34519913012425069155163457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23013275341616712770108971 34519913012425069155163457)
        ·
          refine ⟨25889934759318801866372593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34519913012425069155163457 25889934759318801866372593)
          ·
            refine ⟨19417451069489101399779445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25889934759318801866372593 19417451069489101399779445)
            ·
              refine ⟨1820386037764603256229323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19417451069489101399779445 1820386037764603256229323)
              ·
                refine ⟨2730579056646904884343985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820386037764603256229323 2730579056646904884343985)
                ·
                  refine ⟨2047934292485178663257989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2730579056646904884343985 2047934292485178663257989)
                  ·
                    refine ⟨383987679840970999360873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2047934292485178663257989 383987679840970999360873)
                    ·
                      rfl

theorem cell22_1121720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_1121720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121720 prefixEnd_1121720 := by exact prefixLift 1121720
  have htrace : WordTrace (prefixWord ++ tailWord_1121720) baseStart_1121720 baseEnd_1121720 := by
    simpa [prefixWord, tailWord_1121720, baseEnd_1121720] using wordTrace_append hprefix tailTrace_1121720
  have hstable : (prefixWord ++ tailWord_1121720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121720).length < 2 ^ (prefixWord ++ tailWord_1121720).sum := by decide
  have hdescent : baseEnd_1121720 < baseStart_1121720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121724 : List Nat := [2, 2, 2, 4, 2, 1, 2, 3, 4]
def baseStart_1121724 : Nat := 118140960795 + 1121724 * 2 ^ 59
def prefixEnd_1121724 : Nat := 4983230072969 + 3 ^ 40 * 1121724 * 2
def baseEnd_1121724 : Nat := 127996349707572107420287

theorem tailTrace_1121724 : CollatzResearch.WordTrace tailWord_1121724 prefixEnd_1121724 127996349707572107420287 := by
  unfold tailWord_1121724
  simp only [CollatzResearch.WordTrace]
  refine ⟨20456317694096499026114113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27275090258795332034818817 20456317694096499026114113)
  ·
    refine ⟨15342238270572374269585585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20456317694096499026114113 15342238270572374269585585)
    ·
      refine ⟨11506678702929280702189189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15342238270572374269585585 11506678702929280702189189)
      ·
        refine ⟨2157502256799240131660473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11506678702929280702189189 2157502256799240131660473)
        ·
          refine ⟨1618126692599430098745355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2157502256799240131660473 1618126692599430098745355)
          ·
            refine ⟨2427190038899145148118033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1618126692599430098745355 2427190038899145148118033)
            ·
              refine ⟨1820392529174358861088525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2427190038899145148118033 1820392529174358861088525)
              ·
                refine ⟨682647198440384572908197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1820392529174358861088525 682647198440384572908197)
                ·
                  refine ⟨127996349707572107420287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 682647198440384572908197 127996349707572107420287)
                  ·
                    rfl

theorem cell22_1121724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_1121724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121724 prefixEnd_1121724 := by exact prefixLift 1121724
  have htrace : WordTrace (prefixWord ++ tailWord_1121724) baseStart_1121724 baseEnd_1121724 := by
    simpa [prefixWord, tailWord_1121724, baseEnd_1121724] using wordTrace_append hprefix tailTrace_1121724
  have hstable : (prefixWord ++ tailWord_1121724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121724).length < 2 ^ (prefixWord ++ tailWord_1121724).sum := by decide
  have hdescent : baseEnd_1121724 < baseStart_1121724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121730 : List Nat := [3, 5, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1121730 : Nat := 118140960795 + 1121730 * 2 ^ 59
def prefixEnd_1121730 : Nat := 4983230072969 + 3 ^ 40 * 1121730 * 2
def baseEnd_1121730 : Nat := 127997034348444768870281

theorem tailTrace_1121730 : CollatzResearch.WordTrace tailWord_1121730 prefixEnd_1121730 127997034348444768870281 := by
  unfold tailWord_1121730
  simp only [CollatzResearch.WordTrace]
  refine ⟨10228213556542815269236661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27275236150780840717964429 10228213556542815269236661)
  ·
    refine ⟨958895020925888931490937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10228213556542815269236661 958895020925888931490937)
    ·
      refine ⟨719171265694416698618203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 958895020925888931490937 719171265694416698618203)
      ·
        refine ⟨1078756898541625047927305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719171265694416698618203 1078756898541625047927305)
        ·
          refine ⟨809067673906218785945479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1078756898541625047927305 809067673906218785945479)
          ·
            refine ⟨1213601510859328178918219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809067673906218785945479 1213601510859328178918219)
            ·
              refine ⟨1820402266288992268377329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213601510859328178918219 1820402266288992268377329)
              ·
                refine ⟨1365301699716744201282997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1820402266288992268377329 1365301699716744201282997)
                ·
                  refine ⟨127997034348444768870281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1365301699716744201282997 127997034348444768870281)
                  ·
                    rfl

theorem cell22_1121730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1121730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121730 prefixEnd_1121730 := by exact prefixLift 1121730
  have htrace : WordTrace (prefixWord ++ tailWord_1121730) baseStart_1121730 baseEnd_1121730 := by
    simpa [prefixWord, tailWord_1121730, baseEnd_1121730] using wordTrace_append hprefix tailTrace_1121730
  have hstable : (prefixWord ++ tailWord_1121730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121730).length < 2 ^ (prefixWord ++ tailWord_1121730).sum := by decide
  have hdescent : baseEnd_1121730 < baseStart_1121730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121767 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 3, 3]
def baseStart_1121767 : Nat := 118140960795 + 1121767 * 2 ^ 59
def prefixEnd_1121767 : Nat := 4983230072969 + 3 ^ 40 * 1121767 * 2
def baseEnd_1121767 : Nat := 384003768901478543435729

theorem tailTrace_1121767 : CollatzResearch.WordTrace tailWord_1121767 prefixEnd_1121767 384003768901478543435729 := by
  unfold tailWord_1121767
  simp only [CollatzResearch.WordTrace]
  refine ⟨40914203727037216396043555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27276135818024810930695703 40914203727037216396043555)
  ·
    refine ⟨61371305590555824594065333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40914203727037216396043555 61371305590555824594065333)
    ·
      refine ⟨5753559899114608555693625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61371305590555824594065333 5753559899114608555693625)
      ·
        refine ⟨4315169924335956416770219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5753559899114608555693625 4315169924335956416770219)
        ·
          refine ⟨6472754886503934625155329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4315169924335956416770219 6472754886503934625155329)
          ·
            refine ⟨4854566164877950968866497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6472754886503934625155329 4854566164877950968866497)
            ·
              refine ⟨3640924623658463226649873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4854566164877950968866497 3640924623658463226649873)
              ·
                refine ⟨2730693467743847419987405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3640924623658463226649873 2730693467743847419987405)
                ·
                  refine ⟨1024010050403942782495277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2730693467743847419987405 1024010050403942782495277)
                  ·
                    refine ⟨384003768901478543435729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1024010050403942782495277 384003768901478543435729)
                    ·
                      rfl

theorem cell22_1121767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_1121767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121767 prefixEnd_1121767 := by exact prefixLift 1121767
  have htrace : WordTrace (prefixWord ++ tailWord_1121767) baseStart_1121767 baseEnd_1121767 := by
    simpa [prefixWord, tailWord_1121767, baseEnd_1121767] using wordTrace_append hprefix tailTrace_1121767
  have hstable : (prefixWord ++ tailWord_1121767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121767).length < 2 ^ (prefixWord ++ tailWord_1121767).sum := by decide
  have hdescent : baseEnd_1121767 < baseStart_1121767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121784 : List Nat := [2, 1, 2, 1, 1, 5, 3, 3, 1, 3]
def baseStart_1121784 : Nat := 118140960795 + 1121784 * 2 ^ 59
def prefixEnd_1121784 : Nat := 4983230072969 + 3 ^ 40 * 1121784 * 2
def baseEnd_1121784 : Nat := 384009588348896165760677

theorem tailTrace_1121784 : CollatzResearch.WordTrace tailWord_1121784 prefixEnd_1121784 384009588348896165760677 := by
  unfold tailWord_1121784
  simp only [CollatzResearch.WordTrace]
  refine ⟨20457411883987814149706203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27276549178650418866274937 20457411883987814149706203)
  ·
    refine ⟨30686117825981721224559305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20457411883987814149706203 30686117825981721224559305)
    ·
      refine ⟨23014588369486290918419479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30686117825981721224559305 23014588369486290918419479)
      ·
        refine ⟨34521882554229436377629219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23014588369486290918419479 34521882554229436377629219)
        ·
          refine ⟨51782823831344154566443829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34521882554229436377629219 51782823831344154566443829)
          ·
            refine ⟨4854639734188514490604109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51782823831344154566443829 4854639734188514490604109)
            ·
              refine ⟨1820489900320692933976541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4854639734188514490604109 1820489900320692933976541)
              ·
                refine ⟨682683712620259850241203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1820489900320692933976541 682683712620259850241203)
                ·
                  refine ⟨1024025568930389775361805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682683712620259850241203 1024025568930389775361805)
                  ·
                    refine ⟨384009588348896165760677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1024025568930389775361805 384009588348896165760677)
                    ·
                      rfl

theorem cell22_1121784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_1121784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121784 prefixEnd_1121784 := by exact prefixLift 1121784
  have htrace : WordTrace (prefixWord ++ tailWord_1121784) baseStart_1121784 baseEnd_1121784 := by
    simpa [prefixWord, tailWord_1121784, baseEnd_1121784] using wordTrace_append hprefix tailTrace_1121784
  have hstable : (prefixWord ++ tailWord_1121784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121784).length < 2 ^ (prefixWord ++ tailWord_1121784).sum := by decide
  have hdescent : baseEnd_1121784 < baseStart_1121784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121827 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 3, 4]
def baseStart_1121827 : Nat := 118140960795 + 1121827 * 2 ^ 59
def prefixEnd_1121827 : Nat := 4983230072969 + 3 ^ 40 * 1121827 * 2
def baseEnd_1121827 : Nat := 384024308127658386935545

theorem tailTrace_1121827 : CollatzResearch.WordTrace tailWord_1121827 prefixEnd_1121827 384024308127658386935545 := by
  unfold tailWord_1121827
  simp only [CollatzResearch.WordTrace]
  refine ⟨40916392106819846643227735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27277594737879897762151823 40916392106819846643227735)
  ·
    refine ⟨61374588160229769964841603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40916392106819846643227735 61374588160229769964841603)
    ·
      refine ⟨92061882240344654947262405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61374588160229769964841603 92061882240344654947262405)
      ·
        refine ⟨17261602920064622802611701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92061882240344654947262405 17261602920064622802611701)
        ·
          refine ⟨1618275273756058387744847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17261602920064622802611701 1618275273756058387744847)
          ·
            refine ⟨2427412910634087581617271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1618275273756058387744847 2427412910634087581617271)
            ·
              refine ⟨3641119365951131372425907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2427412910634087581617271 3641119365951131372425907)
              ·
                refine ⟨5461679048926697058638861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3641119365951131372425907 5461679048926697058638861)
                ·
                  refine ⟨2048129643347511396989573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5461679048926697058638861 2048129643347511396989573)
                  ·
                    refine ⟨384024308127658386935545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2048129643347511396989573 384024308127658386935545)
                    ·
                      rfl

theorem cell22_1121827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 4].length) (baseStart_1121827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121827 prefixEnd_1121827 := by exact prefixLift 1121827
  have htrace : WordTrace (prefixWord ++ tailWord_1121827) baseStart_1121827 baseEnd_1121827 := by
    simpa [prefixWord, tailWord_1121827, baseEnd_1121827] using wordTrace_append hprefix tailTrace_1121827
  have hstable : (prefixWord ++ tailWord_1121827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121827).length < 2 ^ (prefixWord ++ tailWord_1121827).sum := by decide
  have hdescent : baseEnd_1121827 < baseStart_1121827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121842 : List Nat := [3, 2, 1, 1, 2, 1, 1, 7, 4]
def baseStart_1121842 : Nat := 118140960795 + 1121842 * 2 ^ 59
def prefixEnd_1121842 : Nat := 4983230072969 + 3 ^ 40 * 1121842 * 2
def baseEnd_1121842 : Nat := 128009814311401115936833

theorem tailTrace_1121842 : CollatzResearch.WordTrace tailWord_1121842 prefixEnd_1121842 128009814311401115936833 := by
  unfold tailWord_1121842
  simp only [CollatzResearch.WordTrace]
  refine ⟨10229234800441376051255945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27277959467843669470015853 10229234800441376051255945)
  ·
    refine ⟨7671926100331032038441959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10229234800441376051255945 7671926100331032038441959)
    ·
      refine ⟨11507889150496548057662939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7671926100331032038441959 11507889150496548057662939)
      ·
        refine ⟨17261833725744822086494409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11507889150496548057662939 17261833725744822086494409)
        ·
          refine ⟨12946375294308616564870807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17261833725744822086494409 12946375294308616564870807)
          ·
            refine ⟨19419562941462924847306211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12946375294308616564870807 19419562941462924847306211)
            ·
              refine ⟨29129344412194387270959317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19419562941462924847306211 29129344412194387270959317)
              ·
                refine ⟨682719009660805951663109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29129344412194387270959317 682719009660805951663109)
                ·
                  refine ⟨128009814311401115936833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 682719009660805951663109 128009814311401115936833)
                  ·
                    rfl

theorem cell22_1121842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_1121842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121842 prefixEnd_1121842 := by exact prefixLift 1121842
  have htrace : WordTrace (prefixWord ++ tailWord_1121842) baseStart_1121842 baseEnd_1121842 := by
    simpa [prefixWord, tailWord_1121842, baseEnd_1121842] using wordTrace_append hprefix tailTrace_1121842
  have hstable : (prefixWord ++ tailWord_1121842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121842).length < 2 ^ (prefixWord ++ tailWord_1121842).sum := by decide
  have hdescent : baseEnd_1121842 < baseStart_1121842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121874 : List Nat := [3, 2, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_1121874 : Nat := 118140960795 + 1121874 * 2 ^ 59
def prefixEnd_1121874 : Nat := 4983230072969 + 3 ^ 40 * 1121874 * 2
def baseEnd_1121874 : Nat := 384040397188165931010401

theorem tailTrace_1121874 : CollatzResearch.WordTrace tailWord_1121874 prefixEnd_1121874 384040397188165931010401 := by
  unfold tailWord_1121874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10229526584412393417547169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27278737558433049113459117 10229526584412393417547169)
  ·
    refine ⟨7672144938309295063160377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10229526584412393417547169 7672144938309295063160377)
    ·
      refine ⟨5754108703731971297370283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7672144938309295063160377 5754108703731971297370283)
      ·
        refine ⟨8631163055597956946055425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5754108703731971297370283 8631163055597956946055425)
        ·
          refine ⟨6473372291698467709541569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8631163055597956946055425 6473372291698467709541569)
          ·
            refine ⟨4855029218773850782156177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6473372291698467709541569 4855029218773850782156177)
            ·
              refine ⟨3641271914080388086617133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4855029218773850782156177 3641271914080388086617133)
              ·
                refine ⟨1365476967780145532481425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3641271914080388086617133 1365476967780145532481425)
                ·
                  refine ⟨1024107725835109149361069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1365476967780145532481425 1024107725835109149361069)
                  ·
                    refine ⟨384040397188165931010401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1024107725835109149361069 384040397188165931010401)
                    ·
                      rfl

theorem cell22_1121874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_1121874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121874 prefixEnd_1121874 := by exact prefixLift 1121874
  have htrace : WordTrace (prefixWord ++ tailWord_1121874) baseStart_1121874 baseEnd_1121874 := by
    simpa [prefixWord, tailWord_1121874, baseEnd_1121874] using wordTrace_append hprefix tailTrace_1121874
  have hstable : (prefixWord ++ tailWord_1121874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121874).length < 2 ^ (prefixWord ++ tailWord_1121874).sum := by decide
  have hdescent : baseEnd_1121874 < baseStart_1121874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121915 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 7]
def baseStart_1121915 : Nat := 118140960795 + 1121915 * 2 ^ 59
def prefixEnd_1121915 : Nat := 4983230072969 + 3 ^ 40 * 1121915 * 2
def baseEnd_1121915 : Nat := 128018144108685163578425

theorem tailTrace_1121915 : CollatzResearch.WordTrace tailWord_1121915 prefixEnd_1121915 128018144108685163578425 := by
  unfold tailWord_1121915
  simp only [CollatzResearch.WordTrace]
  refine ⟨40919601730501037672431199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27279734487000691781620799 40919601730501037672431199)
  ·
    refine ⟨61379402595751556508646799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40919601730501037672431199 61379402595751556508646799)
    ·
      refine ⟨92069103893627334762970199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61379402595751556508646799 92069103893627334762970199)
      ·
        refine ⟨138103655840441002144455299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92069103893627334762970199 138103655840441002144455299)
        ·
          refine ⟨207155483760661503216682949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138103655840441002144455299 207155483760661503216682949)
          ·
            refine ⟨38841653205124031853128053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207155483760661503216682949 38841653205124031853128053)
            ·
              refine ⟨3641404987980377986230755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38841653205124031853128053 3641404987980377986230755)
              ·
                refine ⟨5462107481970566979346133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3641404987980377986230755 5462107481970566979346133)
                ·
                  refine ⟨128018144108685163578425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5462107481970566979346133 128018144108685163578425)
                  ·
                    rfl

theorem cell22_1121915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 7].length) (baseStart_1121915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121915 prefixEnd_1121915 := by exact prefixLift 1121915
  have htrace : WordTrace (prefixWord ++ tailWord_1121915) baseStart_1121915 baseEnd_1121915 := by
    simpa [prefixWord, tailWord_1121915, baseEnd_1121915] using wordTrace_append hprefix tailTrace_1121915
  have hstable : (prefixWord ++ tailWord_1121915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121915).length < 2 ^ (prefixWord ++ tailWord_1121915).sum := by decide
  have hdescent : baseEnd_1121915 < baseStart_1121915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121953 : List Nat := [1, 2, 3, 3, 2, 3, 1, 3, 1, 3]
def baseStart_1121953 : Nat := 118140960795 + 1121953 * 2 ^ 59
def prefixEnd_1121953 : Nat := 4983230072969 + 3 ^ 40 * 1121953 * 2
def baseEnd_1121953 : Nat := 384067440502636058285159

theorem tailTrace_1121953 : CollatzResearch.WordTrace tailWord_1121953 prefixEnd_1121953 384067440502636058285159 := by
  unfold tailWord_1121953
  simp only [CollatzResearch.WordTrace]
  refine ⟨40920987704363370162314513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27280658469575580108209675 40920987704363370162314513)
  ·
    refine ⟨30690740778272527621735885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40920987704363370162314513 30690740778272527621735885)
    ·
      refine ⟨11509027791852197858150957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30690740778272527621735885 11509027791852197858150957)
      ·
        refine ⟨4315885421944574196806609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11509027791852197858150957 4315885421944574196806609)
        ·
          refine ⟨3236914066458430647604957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4315885421944574196806609 3236914066458430647604957)
          ·
            refine ⟨1213842774921911492851859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3236914066458430647604957 1213842774921911492851859)
            ·
              refine ⟨1820764162382867239277789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213842774921911492851859 1820764162382867239277789)
              ·
                refine ⟨682786560893575214729171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1820764162382867239277789 682786560893575214729171)
                ·
                  refine ⟨1024179841340362822093757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682786560893575214729171 1024179841340362822093757)
                  ·
                    refine ⟨384067440502636058285159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1024179841340362822093757 384067440502636058285159)
                    ·
                      rfl

theorem cell22_1121953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_1121953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121953 prefixEnd_1121953 := by exact prefixLift 1121953
  have htrace : WordTrace (prefixWord ++ tailWord_1121953) baseStart_1121953 baseEnd_1121953 := by
    simpa [prefixWord, tailWord_1121953, baseEnd_1121953] using wordTrace_append hprefix tailTrace_1121953
  have hstable : (prefixWord ++ tailWord_1121953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121953).length < 2 ^ (prefixWord ++ tailWord_1121953).sum := by decide
  have hdescent : baseEnd_1121953 < baseStart_1121953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121977 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 6]
def baseStart_1121977 : Nat := 118140960795 + 1121977 * 2 ^ 59
def prefixEnd_1121977 : Nat := 4983230072969 + 3 ^ 40 * 1121977 * 2
def baseEnd_1121977 : Nat := 128025218731035998561695

theorem tailTrace_1121977 : CollatzResearch.WordTrace tailWord_1121977 prefixEnd_1121977 128025218731035998561695 := by
  unfold tailWord_1121977
  simp only [CollatzResearch.WordTrace]
  refine ⟨40921863056276422261188185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27281242037517614840792123 40921863056276422261188185)
  ·
    refine ⟨30691397292207316695891139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40921863056276422261188185 30691397292207316695891139)
    ·
      refine ⟨46037095938310975043836709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30691397292207316695891139 46037095938310975043836709)
      ·
        refine ⟨8631955488433307820719383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46037095938310975043836709 8631955488433307820719383)
        ·
          refine ⟨12947933232649961731079075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8631955488433307820719383 12947933232649961731079075)
          ·
            refine ⟨19421899848974942596618613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12947933232649961731079075 19421899848974942596618613)
            ·
              refine ⟨1820803110841400868432995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19421899848974942596618613 1820803110841400868432995)
              ·
                refine ⟨2731204666262101302649493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1820803110841400868432995 2731204666262101302649493)
                ·
                  refine ⟨128025218731035998561695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2731204666262101302649493 128025218731035998561695)
                  ·
                    rfl

theorem cell22_1121977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 6].length) (baseStart_1121977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121977 prefixEnd_1121977 := by exact prefixLift 1121977
  have htrace : WordTrace (prefixWord ++ tailWord_1121977) baseStart_1121977 baseEnd_1121977 := by
    simpa [prefixWord, tailWord_1121977, baseEnd_1121977] using wordTrace_append hprefix tailTrace_1121977
  have hstable : (prefixWord ++ tailWord_1121977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121977).length < 2 ^ (prefixWord ++ tailWord_1121977).sum := by decide
  have hdescent : baseEnd_1121977 < baseStart_1121977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1121992 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 1, 5]
def baseStart_1121992 : Nat := 118140960795 + 1121992 * 2 ^ 59
def prefixEnd_1121992 : Nat := 4983230072969 + 3 ^ 40 * 1121992 * 2
def baseEnd_1121992 : Nat := 384080790999652956560039

theorem tailTrace_1121992 : CollatzResearch.WordTrace tailWord_1121992 prefixEnd_1121992 384080790999652956560039 := by
  unfold tailWord_1121992
  simp only [CollatzResearch.WordTrace]
  refine ⟨20461205075611039911492115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27281606767481386548656153 20461205075611039911492115)
  ·
    refine ⟨30691807613416559867238173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20461205075611039911492115 30691807613416559867238173)
    ·
      refine ⟨11509427855031209950214315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30691807613416559867238173 11509427855031209950214315)
      ·
        refine ⟨17264141782546814925321473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11509427855031209950214315 17264141782546814925321473)
        ·
          refine ⟨12948106336910111193991105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17264141782546814925321473 12948106336910111193991105)
          ·
            refine ⟨9711079752682583395493329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12948106336910111193991105 9711079752682583395493329)
            ·
              refine ⟨7283309814511937546619997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9711079752682583395493329 7283309814511937546619997)
              ·
                refine ⟨2731241180441976579982499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7283309814511937546619997 2731241180441976579982499)
                ·
                  refine ⟨4096861770662964869973749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2731241180441976579982499 4096861770662964869973749)
                  ·
                    refine ⟨384080790999652956560039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4096861770662964869973749 384080790999652956560039)
                    ·
                      rfl

theorem cell22_1121992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_1121992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1121992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1121992 prefixEnd_1121992 := by exact prefixLift 1121992
  have htrace : WordTrace (prefixWord ++ tailWord_1121992) baseStart_1121992 baseEnd_1121992 := by
    simpa [prefixWord, tailWord_1121992, baseEnd_1121992] using wordTrace_append hprefix tailTrace_1121992
  have hstable : (prefixWord ++ tailWord_1121992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1121992).length < 2 ^ (prefixWord ++ tailWord_1121992).sum := by decide
  have hdescent : baseEnd_1121992 < baseStart_1121992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1121992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122024 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 2, 4]
def baseStart_1122024 : Nat := 118140960795 + 1122024 * 2 ^ 59
def prefixEnd_1122024 : Nat := 4983230072969 + 3 ^ 40 * 1122024 * 2
def baseEnd_1122024 : Nat := 384091745253615539759941

theorem tailTrace_1122024 : CollatzResearch.WordTrace tailWord_1122024 prefixEnd_1122024 384091745253615539759941 := by
  unfold tailWord_1122024
  simp only [CollatzResearch.WordTrace]
  refine ⟨20461788643553074644074563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27282384858070766192099417 20461788643553074644074563)
  ·
    refine ⟨30692682965329611966111845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20461788643553074644074563 30692682965329611966111845)
    ·
      refine ⟨5754878055999302243645971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30692682965329611966111845 5754878055999302243645971)
      ·
        refine ⟨8632317083998953365468957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5754878055999302243645971 8632317083998953365468957)
        ·
          refine ⟨3237118906499607512050859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8632317083998953365468957 3237118906499607512050859)
          ·
            refine ⟨4855678359749411268076289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3237118906499607512050859 4855678359749411268076289)
            ·
              refine ⟨3641758769812058451057217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4855678359749411268076289 3641758769812058451057217)
              ·
                refine ⟨2731319077359043838292913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3641758769812058451057217 2731319077359043838292913)
                ·
                  refine ⟨2048489308019282878719685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2731319077359043838292913 2048489308019282878719685)
                  ·
                    refine ⟨384091745253615539759941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2048489308019282878719685 384091745253615539759941)
                    ·
                      rfl

theorem cell22_1122024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_1122024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122024 prefixEnd_1122024 := by exact prefixLift 1122024
  have htrace : WordTrace (prefixWord ++ tailWord_1122024) baseStart_1122024 baseEnd_1122024 := by
    simpa [prefixWord, tailWord_1122024, baseEnd_1122024] using wordTrace_append hprefix tailTrace_1122024
  have hstable : (prefixWord ++ tailWord_1122024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122024).length < 2 ^ (prefixWord ++ tailWord_1122024).sum := by decide
  have hdescent : baseEnd_1122024 < baseStart_1122024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122084 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 7]
def baseStart_1122084 : Nat := 118140960795 + 1122084 * 2 ^ 59
def prefixEnd_1122084 : Nat := 4983230072969 + 3 ^ 40 * 1122084 * 2
def baseEnd_1122084 : Nat := 128037428159931794419919

theorem tailTrace_1122084 : CollatzResearch.WordTrace tailWord_1122084 prefixEnd_1122084 128037428159931794419919 := by
  unfold tailWord_1122084
  simp only [CollatzResearch.WordTrace]
  refine ⟨20462882833444389767666653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27283843777925853023555537 20462882833444389767666653)
  ·
    refine ⟨7673581062541646162874995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20462882833444389767666653 7673581062541646162874995)
    ·
      refine ⟨11510371593812469244312493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7673581062541646162874995 11510371593812469244312493)
      ·
        refine ⟨4316389347679675966617185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11510371593812469244312493 4316389347679675966617185)
        ·
          refine ⟨3237292010759756974962889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4316389347679675966617185 3237292010759756974962889)
          ·
            refine ⟨2427969008069817731222167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3237292010759756974962889 2427969008069817731222167)
            ·
              refine ⟨3641953512104726596833251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2427969008069817731222167 3641953512104726596833251)
              ·
                refine ⟨5462930268157089895249877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3641953512104726596833251 5462930268157089895249877)
                ·
                  refine ⟨128037428159931794419919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5462930268157089895249877 128037428159931794419919)
                  ·
                    rfl

theorem cell22_1122084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_1122084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122084 prefixEnd_1122084 := by exact prefixLift 1122084
  have htrace : WordTrace (prefixWord ++ tailWord_1122084) baseStart_1122084 baseEnd_1122084 := by
    simpa [prefixWord, tailWord_1122084, baseEnd_1122084] using wordTrace_append hprefix tailTrace_1122084
  have hstable : (prefixWord ++ tailWord_1122084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122084).length < 2 ^ (prefixWord ++ tailWord_1122084).sum := by decide
  have hdescent : baseEnd_1122084 < baseStart_1122084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122088 : List Nat := [2, 1, 5, 1, 1, 2, 2, 4, 1, 3]
def baseStart_1122088 : Nat := 118140960795 + 1122088 * 2 ^ 59
def prefixEnd_1122088 : Nat := 4983230072969 + 3 ^ 40 * 1122088 * 2
def baseEnd_1122088 : Nat := 384113653761540706159745

theorem tailTrace_1122088 : CollatzResearch.WordTrace tailWord_1122088 prefixEnd_1122088 384113653761540706159745 := by
  unfold tailWord_1122088
  simp only [CollatzResearch.WordTrace]
  refine ⟨20462955779437144109239459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27283941039249525478985945 20462955779437144109239459)
  ·
    refine ⟨30694433669155716163859189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20462955779437144109239459 30694433669155716163859189)
    ·
      refine ⟨2877603156483348390361799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30694433669155716163859189 2877603156483348390361799)
      ·
        refine ⟨4316404734725022585542699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2877603156483348390361799 4316404734725022585542699)
        ·
          refine ⟨6474607102087533878314049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4316404734725022585542699 6474607102087533878314049)
          ·
            refine ⟨4855955326565650408735537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6474607102087533878314049 4855955326565650408735537)
            ·
              refine ⟨3641966494924237806551653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4855955326565650408735537 3641966494924237806551653)
              ·
                refine ⟨682868717798294588728435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3641966494924237806551653 682868717798294588728435)
                ·
                  refine ⟨1024303076697441883092653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682868717798294588728435 1024303076697441883092653)
                  ·
                    refine ⟨384113653761540706159745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1024303076697441883092653 384113653761540706159745)
                    ·
                      rfl

theorem cell22_1122088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_1122088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122088 prefixEnd_1122088 := by exact prefixLift 1122088
  have htrace : WordTrace (prefixWord ++ tailWord_1122088) baseStart_1122088 baseEnd_1122088 := by
    simpa [prefixWord, tailWord_1122088, baseEnd_1122088] using wordTrace_append hprefix tailTrace_1122088
  have hstable : (prefixWord ++ tailWord_1122088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122088).length < 2 ^ (prefixWord ++ tailWord_1122088).sum := by decide
  have hdescent : baseEnd_1122088 < baseStart_1122088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122146 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1122146 : Nat := 118140960795 + 1122146 * 2 ^ 59
def prefixEnd_1122146 : Nat := 4983230072969 + 3 ^ 40 * 1122146 * 2
def baseEnd_1122146 : Nat := 128044502782282629403189

theorem tailTrace_1122146 : CollatzResearch.WordTrace tailWord_1122146 prefixEnd_1122146 128044502782282629403189 := by
  unfold tailWord_1122146
  simp only [CollatzResearch.WordTrace]
  refine ⟨10232006748166041031022573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27285351328442776082726861 10232006748166041031022573)
  ·
    refine ⟨3837002530562265386633465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10232006748166041031022573 3837002530562265386633465)
    ·
      refine ⟨2877751897921699039975099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3837002530562265386633465 2877751897921699039975099)
      ·
        refine ⟨4316627846882548559962649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2877751897921699039975099 4316627846882548559962649)
        ·
          refine ⟨3237470885161911419971987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4316627846882548559962649 3237470885161911419971987)
          ·
            refine ⟨4856206327742867129957981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3237470885161911419971987 4856206327742867129957981)
            ·
              refine ⟨1821077372903575173734243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4856206327742867129957981 1821077372903575173734243)
              ·
                refine ⟨2731616059355362760601365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1821077372903575173734243 2731616059355362760601365)
                ·
                  refine ⟨128044502782282629403189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2731616059355362760601365 128044502782282629403189)
                  ·
                    rfl

theorem cell22_1122146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1122146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122146 prefixEnd_1122146 := by exact prefixLift 1122146
  have htrace : WordTrace (prefixWord ++ tailWord_1122146) baseStart_1122146 baseEnd_1122146 := by
    simpa [prefixWord, tailWord_1122146, baseEnd_1122146] using wordTrace_append hprefix tailTrace_1122146
  have hstable : (prefixWord ++ tailWord_1122146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122146).length < 2 ^ (prefixWord ++ tailWord_1122146).sum := by decide
  have hdescent : baseEnd_1122146 < baseStart_1122146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122161 : List Nat := [1, 2, 2, 2, 1, 3, 3, 3, 2, 3]
def baseStart_1122161 : Nat := 118140960795 + 1122161 * 2 ^ 59
def prefixEnd_1122161 : Nat := 4983230072969 + 3 ^ 40 * 1122161 * 2
def baseEnd_1122161 : Nat := 384138643153392849084521

theorem tailTrace_1122161 : CollatzResearch.WordTrace tailWord_1122161 prefixEnd_1122161 384138643153392849084521 := by
  unfold tailWord_1122161
  simp only [CollatzResearch.WordTrace]
  refine ⟨40928574087609821685886337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27285716058406547790590891 40928574087609821685886337)
  ·
    refine ⟨30696430565707366264414753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40928574087609821685886337 30696430565707366264414753)
    ·
      refine ⟨23022322924280524698311065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30696430565707366264414753 23022322924280524698311065)
      ·
        refine ⟨17266742193210393523733299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23022322924280524698311065 17266742193210393523733299)
        ·
          refine ⟨25900113289815590285599949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17266742193210393523733299 25900113289815590285599949)
          ·
            refine ⟨9712542483680846357099981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25900113289815590285599949 9712542483680846357099981)
            ·
              refine ⟨3642203431380317383912493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9712542483680846357099981 3642203431380317383912493)
              ·
                refine ⟨1365826286767619018967185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3642203431380317383912493 1365826286767619018967185)
                ·
                  refine ⟨1024369715075714264225389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1365826286767619018967185 1024369715075714264225389)
                  ·
                    refine ⟨384138643153392849084521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1024369715075714264225389 384138643153392849084521)
                    ·
                      rfl

theorem cell22_1122161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_1122161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122161 prefixEnd_1122161 := by exact prefixLift 1122161
  have htrace : WordTrace (prefixWord ++ tailWord_1122161) baseStart_1122161 baseEnd_1122161 := by
    simpa [prefixWord, tailWord_1122161, baseEnd_1122161] using wordTrace_append hprefix tailTrace_1122161
  have hstable : (prefixWord ++ tailWord_1122161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122161).length < 2 ^ (prefixWord ++ tailWord_1122161).sum := by decide
  have hdescent : baseEnd_1122161 < baseStart_1122161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122296 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 4, 3]
def baseStart_1122296 : Nat := 118140960795 + 1122296 * 2 ^ 59
def prefixEnd_1122296 : Nat := 4983230072969 + 3 ^ 40 * 1122296 * 2
def baseEnd_1122296 : Nat := 384184856412297496959107

theorem tailTrace_1122296 : CollatzResearch.WordTrace tailWord_1122296 prefixEnd_1122296 384184856412297496959107 := by
  unfold tailWord_1122296
  simp only [CollatzResearch.WordTrace]
  refine ⟨20466748971060369871025371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27288998628080493161367161 20466748971060369871025371)
  ·
    refine ⟨30700123456590554806538057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20466748971060369871025371 30700123456590554806538057)
    ·
      refine ⟨23025092592442916104903543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30700123456590554806538057 23025092592442916104903543)
      ·
        refine ⟨34537638888664374157355315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23025092592442916104903543 34537638888664374157355315)
        ·
          refine ⟨51806458332996561236032973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34537638888664374157355315 51806458332996561236032973)
          ·
            refine ⟨19427421874873710463512365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51806458332996561236032973 19427421874873710463512365)
            ·
              refine ⟨7285283203077641423817137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19427421874873710463512365 7285283203077641423817137)
              ·
                refine ⟨5463962402308231067862853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7285283203077641423817137 5463962402308231067862853)
                ·
                  refine ⟨1024492950432793325224285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5463962402308231067862853 1024492950432793325224285)
                  ·
                    refine ⟨384184856412297496959107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1024492950432793325224285 384184856412297496959107)
                    ·
                      rfl

theorem cell22_1122296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_1122296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122296 prefixEnd_1122296 := by exact prefixLift 1122296
  have htrace : WordTrace (prefixWord ++ tailWord_1122296) baseStart_1122296 baseEnd_1122296 := by
    simpa [prefixWord, tailWord_1122296, baseEnd_1122296] using wordTrace_append hprefix tailTrace_1122296
  have hstable : (prefixWord ++ tailWord_1122296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122296).length < 2 ^ (prefixWord ++ tailWord_1122296).sum := by decide
  have hdescent : baseEnd_1122296 < baseStart_1122296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122309 : List Nat := [1, 3, 1, 1, 2, 4, 10]
def baseStart_1122309 : Nat := 118140960795 + 1122309 * 2 ^ 59
def prefixEnd_1122309 : Nat := 4983230072969 + 3 ^ 40 * 1122309 * 2
def baseEnd_1122309 : Nat := 14229233576961844310521

theorem tailTrace_1122309 : CollatzResearch.WordTrace tailWord_1122309 prefixEnd_1122309 14229233576961844310521 := by
  unfold tailWord_1122309
  simp only [CollatzResearch.WordTrace]
  refine ⟨40933972091073642962273981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27289314727382428641515987 40933972091073642962273981)
  ·
    refine ⟨15350239534152616110852743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40933972091073642962273981 15350239534152616110852743)
    ·
      refine ⟨23025359301228924166279115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15350239534152616110852743 23025359301228924166279115)
      ·
        refine ⟨34538038951843386249418673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23025359301228924166279115 34538038951843386249418673)
        ·
          refine ⟨25903529213882539687064005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34538038951843386249418673 25903529213882539687064005)
          ·
            refine ⟨4856911727602976191324501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25903529213882539687064005 4856911727602976191324501)
            ·
              refine ⟨14229233576961844310521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4856911727602976191324501 14229233576961844310521)
              ·
                rfl

theorem cell22_1122309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 10].length) (baseStart_1122309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122309 prefixEnd_1122309 := by exact prefixLift 1122309
  have htrace : WordTrace (prefixWord ++ tailWord_1122309) baseStart_1122309 baseEnd_1122309 := by
    simpa [prefixWord, tailWord_1122309, baseEnd_1122309] using wordTrace_append hprefix tailTrace_1122309
  have hstable : (prefixWord ++ tailWord_1122309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122309).length < 2 ^ (prefixWord ++ tailWord_1122309).sum := by decide
  have hdescent : baseEnd_1122309 < baseStart_1122309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122311 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 4, 4]
def baseStart_1122311 : Nat := 118140960795 + 1122311 * 2 ^ 59
def prefixEnd_1122311 : Nat := 4983230072969 + 3 ^ 40 * 1122311 * 2
def baseEnd_1122311 : Nat := 384189991218842457834061

theorem tailTrace_1122311 : CollatzResearch.WordTrace tailWord_1122311 prefixEnd_1122311 384189991218842457834061 := by
  unfold tailWord_1122311
  simp only [CollatzResearch.WordTrace]
  refine ⟨40934045037066397303846787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27289363358044264869231191 40934045037066397303846787)
  ·
    refine ⟨61401067555599595955770181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40934045037066397303846787 61401067555599595955770181)
    ·
      refine ⟨11512700166674924241706909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61401067555599595955770181 11512700166674924241706909)
      ·
        refine ⟨4317262562503096590640091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11512700166674924241706909 4317262562503096590640091)
        ·
          refine ⟨6475893843754644885960137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4317262562503096590640091 6475893843754644885960137)
          ·
            refine ⟨4856920382815983664470103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6475893843754644885960137 4856920382815983664470103)
            ·
              refine ⟨7285380574223975496705155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4856920382815983664470103 7285380574223975496705155)
              ·
                refine ⟨10928070861335963245057733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7285380574223975496705155 10928070861335963245057733)
                ·
                  refine ⟨2049013286500493108448325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10928070861335963245057733 2049013286500493108448325)
                  ·
                    refine ⟨384189991218842457834061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2049013286500493108448325 384189991218842457834061)
                    ·
                      rfl

theorem cell22_1122311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_1122311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122311 prefixEnd_1122311 := by exact prefixLift 1122311
  have htrace : WordTrace (prefixWord ++ tailWord_1122311) baseStart_1122311 baseEnd_1122311 := by
    simpa [prefixWord, tailWord_1122311, baseEnd_1122311] using wordTrace_append hprefix tailTrace_1122311
  have hstable : (prefixWord ++ tailWord_1122311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122311).length < 2 ^ (prefixWord ++ tailWord_1122311).sum := by decide
  have hdescent : baseEnd_1122311 < baseStart_1122311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122330 : List Nat := [3, 1, 1, 3, 1, 3, 4, 1, 2, 3]
def baseStart_1122330 : Nat := 118140960795 + 1122330 * 2 ^ 59
def prefixEnd_1122330 : Nat := 4983230072969 + 3 ^ 40 * 1122330 * 2
def baseEnd_1122330 : Nat := 384196495307132741609003

theorem tailTrace_1122330 : CollatzResearch.WordTrace tailWord_1122330 prefixEnd_1122330 384196495307132741609003 := by
  unfold tailWord_1122330
  simp only [CollatzResearch.WordTrace]
  refine ⟨10233684505999390887197111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27289825349331709032525629 10233684505999390887197111)
  ·
    refine ⟨15350526758999086330795667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10233684505999390887197111 15350526758999086330795667)
    ·
      refine ⟨23025790138498629496193501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15350526758999086330795667 23025790138498629496193501)
      ·
        refine ⟨8634671301936986061072563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23025790138498629496193501 8634671301936986061072563)
        ·
          refine ⟨12952006952905479091608845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8634671301936986061072563 12952006952905479091608845)
          ·
            refine ⟨4857002607339554659353317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12952006952905479091608845 4857002607339554659353317)
            ·
              refine ⟨910687988876166498628747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4857002607339554659353317 910687988876166498628747)
              ·
                refine ⟨1366031983314249747943121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910687988876166498628747 1366031983314249747943121)
                ·
                  refine ⟨1024523987485687310957341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1366031983314249747943121 1024523987485687310957341)
                  ·
                    refine ⟨384196495307132741609003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1024523987485687310957341 384196495307132741609003)
                    ·
                      rfl

theorem cell22_1122330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_1122330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122330 prefixEnd_1122330 := by exact prefixLift 1122330
  have htrace : WordTrace (prefixWord ++ tailWord_1122330) baseStart_1122330 baseEnd_1122330 := by
    simpa [prefixWord, tailWord_1122330, baseEnd_1122330] using wordTrace_append hprefix tailTrace_1122330
  have hstable : (prefixWord ++ tailWord_1122330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122330).length < 2 ^ (prefixWord ++ tailWord_1122330).sum := by decide
  have hdescent : baseEnd_1122330 < baseStart_1122330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122375 : List Nat := [1, 1, 4, 1, 3, 1, 3, 4, 1, 3]
def baseStart_1122375 : Nat := 118140960795 + 1122375 * 2 ^ 59
def prefixEnd_1122375 : Nat := 4983230072969 + 3 ^ 40 * 1122375 * 2
def baseEnd_1122375 : Nat := 384211899726767624233865

theorem tailTrace_1122375 : CollatzResearch.WordTrace tailWord_1122375 prefixEnd_1122375 384211899726767624233865 := by
  unfold tailWord_1122375
  simp only [CollatzResearch.WordTrace]
  refine ⟨40936379308834536234176579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27290919539223024156117719 40936379308834536234176579)
  ·
    refine ⟨61404568963251804351264869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40936379308834536234176579 61404568963251804351264869)
    ·
      refine ⟨11513356680609713315862163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61404568963251804351264869 11513356680609713315862163)
      ·
        refine ⟨17270035020914569973793245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11513356680609713315862163 17270035020914569973793245)
        ·
          refine ⟨6476263132842963740172467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17270035020914569973793245 6476263132842963740172467)
          ·
            refine ⟨9714394699264445610258701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6476263132842963740172467 9714394699264445610258701)
            ·
              refine ⟨3642898012224167103847013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9714394699264445610258701 3642898012224167103847013)
              ·
                refine ⟨683043377292031331971315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3642898012224167103847013 683043377292031331971315)
                ·
                  refine ⟨1024565065938046997956973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683043377292031331971315 1024565065938046997956973)
                  ·
                    refine ⟨384211899726767624233865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1024565065938046997956973 384211899726767624233865)
                    ·
                      rfl

theorem cell22_1122375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_1122375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122375 prefixEnd_1122375 := by exact prefixLift 1122375
  have htrace : WordTrace (prefixWord ++ tailWord_1122375) baseStart_1122375 baseEnd_1122375 := by
    simpa [prefixWord, tailWord_1122375, baseEnd_1122375] using wordTrace_append hprefix tailTrace_1122375
  have hstable : (prefixWord ++ tailWord_1122375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122375).length < 2 ^ (prefixWord ++ tailWord_1122375).sum := by decide
  have hdescent : baseEnd_1122375 < baseStart_1122375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122463 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 1, 6]
def baseStart_1122463 : Nat := 118140960795 + 1122463 * 2 ^ 59
def prefixEnd_1122463 : Nat := 4983230072969 + 3 ^ 40 * 1122463 * 2
def baseEnd_1122463 : Nat := 384242023925164728033595

theorem tailTrace_1122463 : CollatzResearch.WordTrace tailWord_1122463 prefixEnd_1122463 384242023925164728033595 := by
  unfold tailWord_1122463
  simp only [CollatzResearch.WordTrace]
  refine ⟨40939588932515727263380043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27293059288343818175586695 40939588932515727263380043)
  ·
    refine ⟨61409383398773590895070065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40939588932515727263380043 61409383398773590895070065)
    ·
      refine ⟨46057037549080193171302549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61409383398773590895070065 46057037549080193171302549)
      ·
        refine ⟨2158923635113134054904807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46057037549080193171302549 2158923635113134054904807)
        ·
          refine ⟨3238385452669701082357211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2158923635113134054904807 3238385452669701082357211)
          ·
            refine ⟨4857578179004551623535817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3238385452669701082357211 4857578179004551623535817)
            ·
              refine ⟨3643183634253413717651863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4857578179004551623535817 3643183634253413717651863)
              ·
                refine ⟨5464775451380120576477795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3643183634253413717651863 5464775451380120576477795)
                ·
                  refine ⟨8197163177070180864716693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5464775451380120576477795 8197163177070180864716693)
                  ·
                    refine ⟨384242023925164728033595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8197163177070180864716693 384242023925164728033595)
                    ·
                      rfl

theorem cell22_1122463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_1122463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122463 prefixEnd_1122463 := by exact prefixLift 1122463
  have htrace : WordTrace (prefixWord ++ tailWord_1122463) baseStart_1122463 baseEnd_1122463 := by
    simpa [prefixWord, tailWord_1122463, baseEnd_1122463] using wordTrace_append hprefix tailTrace_1122463
  have hstable : (prefixWord ++ tailWord_1122463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122463).length < 2 ^ (prefixWord ++ tailWord_1122463).sum := by decide
  have hdescent : baseEnd_1122463 < baseStart_1122463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122491 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 2, 6]
def baseStart_1122491 : Nat := 118140960795 + 1122491 * 2 ^ 59
def prefixEnd_1122491 : Nat := 4983230072969 + 3 ^ 40 * 1122491 * 2
def baseEnd_1122491 : Nat := 384251608897381988333509

theorem tailTrace_1122491 : CollatzResearch.WordTrace tailWord_1122491 prefixEnd_1122491 384251608897381988333509 := by
  unfold tailWord_1122491
  simp only [CollatzResearch.WordTrace]
  refine ⟨40940610176414288045399327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27293740117609525363599551 40940610176414288045399327)
  ·
    refine ⟨61410915264621432068098991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40940610176414288045399327 61410915264621432068098991)
    ·
      refine ⟨92116372896932148102148487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61410915264621432068098991 92116372896932148102148487)
      ·
        refine ⟨138174559345398222153222731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92116372896932148102148487 138174559345398222153222731)
        ·
          refine ⟨207261839018097333229834097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138174559345398222153222731 207261839018097333229834097)
          ·
            refine ⟨155446379263572999922375573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207261839018097333229834097 155446379263572999922375573)
            ·
              refine ⟨7286549027979984371361355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 155446379263572999922375573 7286549027979984371361355)
              ·
                refine ⟨10929823541969976557042033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7286549027979984371361355 10929823541969976557042033)
                ·
                  refine ⟨8197367656477482417781525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10929823541969976557042033 8197367656477482417781525)
                  ·
                    refine ⟨384251608897381988333509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8197367656477482417781525 384251608897381988333509)
                    ·
                      rfl

theorem cell22_1122491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 6].length) (baseStart_1122491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122491 prefixEnd_1122491 := by exact prefixLift 1122491
  have htrace : WordTrace (prefixWord ++ tailWord_1122491) baseStart_1122491 baseEnd_1122491 := by
    simpa [prefixWord, tailWord_1122491, baseEnd_1122491] using wordTrace_append hprefix tailTrace_1122491
  have hstable : (prefixWord ++ tailWord_1122491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122491).length < 2 ^ (prefixWord ++ tailWord_1122491).sum := by decide
  have hdescent : baseEnd_1122491 < baseStart_1122491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122538 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_1122538 : Nat := 118140960795 + 1122538 * 2 ^ 59
def prefixEnd_1122538 : Nat := 4983230072969 + 3 ^ 40 * 1122538 * 2
def baseEnd_1122538 : Nat := 384267697957889532408365

theorem tailTrace_1122538 : CollatzResearch.WordTrace tailWord_1122538 prefixEnd_1122538 384267697957889532408365 := by
  unfold tailWord_1122538
  simp only [CollatzResearch.WordTrace]
  refine ⟨10235581101811003768090067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27294882938162676714906845 10235581101811003768090067)
  ·
    refine ⟨15353371652716505652135101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10235581101811003768090067 15353371652716505652135101)
    ·
      refine ⟨5757514369768689619550663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15353371652716505652135101 5757514369768689619550663)
      ·
        refine ⟨8636271554653034429325995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5757514369768689619550663 8636271554653034429325995)
        ·
          refine ⟨12954407331979551643988993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8636271554653034429325995 12954407331979551643988993)
          ·
            refine ⟨9715805498984663732991745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12954407331979551643988993 9715805498984663732991745)
            ·
              refine ⟨7286854124238497799743809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9715805498984663732991745 7286854124238497799743809)
              ·
                refine ⟨5465140593178873349807857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7286854124238497799743809 5465140593178873349807857)
                ·
                  refine ⟨4098855444884155012355893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5465140593178873349807857 4098855444884155012355893)
                  ·
                    refine ⟨384267697957889532408365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4098855444884155012355893 384267697957889532408365)
                    ·
                      rfl

theorem cell22_1122538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_1122538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122538 prefixEnd_1122538 := by exact prefixLift 1122538
  have htrace : WordTrace (prefixWord ++ tailWord_1122538) baseStart_1122538 baseEnd_1122538 := by
    simpa [prefixWord, tailWord_1122538, baseEnd_1122538] using wordTrace_append hprefix tailTrace_1122538
  have hstable : (prefixWord ++ tailWord_1122538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122538).length < 2 ^ (prefixWord ++ tailWord_1122538).sum := by decide
  have hdescent : baseEnd_1122538 < baseStart_1122538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122568 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 8]
def baseStart_1122568 : Nat := 118140960795 + 1122568 * 2 ^ 59
def prefixEnd_1122568 : Nat := 4983230072969 + 3 ^ 40 * 1122568 * 2
def baseEnd_1122568 : Nat := 128092655856993151386091

theorem tailTrace_1122568 : CollatzResearch.WordTrace tailWord_1122568 prefixEnd_1122568 128092655856993151386091 := by
  unfold tailWord_1122568
  simp only [CollatzResearch.WordTrace]
  refine ⟨20471709298567665097976179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27295612398090220130634905 20471709298567665097976179)
  ·
    refine ⟨30707563947851497646964269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20471709298567665097976179 30707563947851497646964269)
    ·
      refine ⟨11515336480444311617611601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30707563947851497646964269 11515336480444311617611601)
      ·
        refine ⟨8636502360333233713208701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11515336480444311617611601 8636502360333233713208701)
        ·
          refine ⟨3238688385124962642453263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8636502360333233713208701 3238688385124962642453263)
          ·
            refine ⟨4858032577687443963679895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3238688385124962642453263 4858032577687443963679895)
            ·
              refine ⟨7287048866531165945519843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4858032577687443963679895 7287048866531165945519843)
              ·
                refine ⟨10930573299796748918279765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7287048866531165945519843 10930573299796748918279765)
                ·
                  refine ⟨128092655856993151386091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10930573299796748918279765 128092655856993151386091)
                  ·
                    rfl

theorem cell22_1122568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 8].length) (baseStart_1122568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122568 prefixEnd_1122568 := by exact prefixLift 1122568
  have htrace : WordTrace (prefixWord ++ tailWord_1122568) baseStart_1122568 baseEnd_1122568 := by
    simpa [prefixWord, tailWord_1122568, baseEnd_1122568] using wordTrace_append hprefix tailTrace_1122568
  have hstable : (prefixWord ++ tailWord_1122568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122568).length < 2 ^ (prefixWord ++ tailWord_1122568).sum := by decide
  have hdescent : baseEnd_1122568 < baseStart_1122568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122602 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 6]
def baseStart_1122602 : Nat := 118140960795 + 1122602 * 2 ^ 59
def prefixEnd_1122602 : Nat := 4983230072969 + 3 ^ 40 * 1122602 * 2
def baseEnd_1122602 : Nat := 128096535488604899602723

theorem tailTrace_1122602 : CollatzResearch.WordTrace tailWord_1122602 prefixEnd_1122602 128096535488604899602723 := by
  unfold tailWord_1122602
  simp only [CollatzResearch.WordTrace]
  refine ⟨10236164669753038500672515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27296439119341436001793373 10236164669753038500672515)
  ·
    refine ⟨15354247004629557751008773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10236164669753038500672515 15354247004629557751008773)
    ·
      refine ⟨2878921313368042078314145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15354247004629557751008773 2878921313368042078314145)
      ·
        refine ⟨2159190985026031558735609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2878921313368042078314145 2159190985026031558735609)
        ·
          refine ⟨1619393238769523669051707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2159190985026031558735609 1619393238769523669051707)
          ·
            refine ⟨2429089858154285503577561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619393238769523669051707 2429089858154285503577561)
            ·
              refine ⟨1821817393615714127683171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2429089858154285503577561 1821817393615714127683171)
              ·
                refine ⟨2732726090423571191524757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1821817393615714127683171 2732726090423571191524757)
                ·
                  refine ⟨128096535488604899602723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2732726090423571191524757 128096535488604899602723)
                  ·
                    rfl

theorem cell22_1122602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_1122602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122602 prefixEnd_1122602 := by exact prefixLift 1122602
  have htrace : WordTrace (prefixWord ++ tailWord_1122602) baseStart_1122602 baseEnd_1122602 := by
    simpa [prefixWord, tailWord_1122602, baseEnd_1122602] using wordTrace_append hprefix tailTrace_1122602
  have hstable : (prefixWord ++ tailWord_1122602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122602).length < 2 ^ (prefixWord ++ tailWord_1122602).sum := by decide
  have hdescent : baseEnd_1122602 < baseStart_1122602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122613 : List Nat := [1, 3, 3, 1, 2, 1, 2, 9]
def baseStart_1122613 : Nat := 118140960795 + 1122613 * 2 ^ 59
def prefixEnd_1122613 : Nat := 4983230072969 + 3 ^ 40 * 1122613 * 2
def baseEnd_1122613 : Nat := 42699263554512704087015

theorem tailTrace_1122613 : CollatzResearch.WordTrace tailWord_1122613 prefixEnd_1122613 42699263554512704087015 := by
  unfold tailWord_1122613
  simp only [CollatzResearch.WordTrace]
  refine ⟨40945059881972302881340493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27296706587981535254226995 40945059881972302881340493)
  ·
    refine ⟨15354397455739613580502685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40945059881972302881340493 15354397455739613580502685)
    ·
      refine ⟨5757899045902355092688507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15354397455739613580502685 5757899045902355092688507)
      ·
        refine ⟨8636848568853532639032761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5757899045902355092688507 8636848568853532639032761)
        ·
          refine ⟨6477636426640149479274571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8636848568853532639032761 6477636426640149479274571)
          ·
            refine ⟨9716454639960224218911857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6477636426640149479274571 9716454639960224218911857)
            ·
              refine ⟨7287340979970168164183893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9716454639960224218911857 7287340979970168164183893)
              ·
                refine ⟨42699263554512704087015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7287340979970168164183893 42699263554512704087015)
                ·
                  rfl

theorem cell22_1122613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 9].length) (baseStart_1122613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122613 prefixEnd_1122613 := by exact prefixLift 1122613
  have htrace : WordTrace (prefixWord ++ tailWord_1122613) baseStart_1122613 baseEnd_1122613 := by
    simpa [prefixWord, tailWord_1122613, baseEnd_1122613] using wordTrace_append hprefix tailTrace_1122613
  have hstable : (prefixWord ++ tailWord_1122613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122613).length < 2 ^ (prefixWord ++ tailWord_1122613).sum := by decide
  have hdescent : baseEnd_1122613 < baseStart_1122613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122617 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 1, 5]
def baseStart_1122617 : Nat := 118140960795 + 1122617 * 2 ^ 59
def prefixEnd_1122617 : Nat := 4983230072969 + 3 ^ 40 * 1122617 * 2
def baseEnd_1122617 : Nat := 384294741272359659683123

theorem tailTrace_1122617 : CollatzResearch.WordTrace tailWord_1122617 prefixEnd_1122617 384294741272359659683123 := by
  unfold tailWord_1122617
  simp only [CollatzResearch.WordTrace]
  refine ⟨40945205773957811564486105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27296803849305207709657403 40945205773957811564486105)
  ·
    refine ⟨30708904330468358673364579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40945205773957811564486105 30708904330468358673364579)
    ·
      refine ⟨46063356495702538010046869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30708904330468358673364579 46063356495702538010046869)
      ·
        refine ⟨2159219835736056469220947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46063356495702538010046869 2159219835736056469220947)
        ·
          refine ⟨3238829753604084703831421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2159219835736056469220947 3238829753604084703831421)
          ·
            refine ⟨1214561157601531763936783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3238829753604084703831421 1214561157601531763936783)
            ·
              refine ⟨1821841736402297645905175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214561157601531763936783 1821841736402297645905175)
              ·
                refine ⟨2732762604603446468857763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1821841736402297645905175 2732762604603446468857763)
                ·
                  refine ⟨4099143906905169703286645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2732762604603446468857763 4099143906905169703286645)
                  ·
                    refine ⟨384294741272359659683123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4099143906905169703286645 384294741272359659683123)
                    ·
                      rfl

theorem cell22_1122617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 5].length) (baseStart_1122617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122617 prefixEnd_1122617 := by exact prefixLift 1122617
  have htrace : WordTrace (prefixWord ++ tailWord_1122617) baseStart_1122617 baseEnd_1122617 := by
    simpa [prefixWord, tailWord_1122617, baseEnd_1122617] using wordTrace_append hprefix tailTrace_1122617
  have hstable : (prefixWord ++ tailWord_1122617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122617).length < 2 ^ (prefixWord ++ tailWord_1122617).sum := by decide
  have hdescent : baseEnd_1122617 < baseStart_1122617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122673 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 1, 7]
def baseStart_1122673 : Nat := 118140960795 + 1122673 * 2 ^ 59
def prefixEnd_1122673 : Nat := 4983230072969 + 3 ^ 40 * 1122673 * 2
def baseEnd_1122673 : Nat := 384313911216794180282951

theorem tailTrace_1122673 : CollatzResearch.WordTrace tailWord_1122673 prefixEnd_1122673 384313911216794180282951 := by
  unfold tailWord_1122673
  simp only [CollatzResearch.WordTrace]
  refine ⟨40947248261754933128524673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27298165507836622085683115 40947248261754933128524673)
  ·
    refine ⟨30710436196316199846393505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40947248261754933128524673 30710436196316199846393505)
    ·
      refine ⟨23032827147237149884795129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30710436196316199846393505 23032827147237149884795129)
      ·
        refine ⟨17274620360427862413596347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23032827147237149884795129 17274620360427862413596347)
        ·
          refine ⟨25911930540641793620394521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17274620360427862413596347 25911930540641793620394521)
          ·
            refine ⟨19433947905481345215295891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25911930540641793620394521 19433947905481345215295891)
            ·
              refine ⟨29150921858222017822943837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19433947905481345215295891 29150921858222017822943837)
              ·
                refine ⟨10931595696833256683603939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29150921858222017822943837 10931595696833256683603939)
                ·
                  refine ⟨16397393545249885025405909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10931595696833256683603939 16397393545249885025405909)
                  ·
                    refine ⟨384313911216794180282951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16397393545249885025405909 384313911216794180282951)
                    ·
                      rfl

theorem cell22_1122673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_1122673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122673 prefixEnd_1122673 := by exact prefixLift 1122673
  have htrace : WordTrace (prefixWord ++ tailWord_1122673) baseStart_1122673 baseEnd_1122673 := by
    simpa [prefixWord, tailWord_1122673, baseEnd_1122673] using wordTrace_append hprefix tailTrace_1122673
  have hstable : (prefixWord ++ tailWord_1122673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122673).length < 2 ^ (prefixWord ++ tailWord_1122673).sum := by decide
  have hdescent : baseEnd_1122673 < baseStart_1122673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122735 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 8, 3]
def baseStart_1122735 : Nat := 118140960795 + 1122735 * 2 ^ 59
def prefixEnd_1122735 : Nat := 4983230072969 + 3 ^ 40 * 1122735 * 2
def baseEnd_1122735 : Nat := 384335135083846685232761

theorem tailTrace_1122735 : CollatzResearch.WordTrace tailWord_1122735 prefixEnd_1122735 384335135083846685232761 := by
  unfold tailWord_1122735
  simp only [CollatzResearch.WordTrace]
  refine ⟨40949509587530317717281659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27299673058353545144854439 40949509587530317717281659)
  ·
    refine ⟨61424264381295476575922489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40949509587530317717281659 61424264381295476575922489)
    ·
      refine ⟨46068198285971607431941867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61424264381295476575922489 46068198285971607431941867)
      ·
        refine ⟨69102297428957411147912801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46068198285971607431941867 69102297428957411147912801)
        ·
          refine ⟨51826723071718058360934601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69102297428957411147912801 51826723071718058360934601)
          ·
            refine ⟨38870042303788543770700951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51826723071718058360934601 38870042303788543770700951)
            ·
              refine ⟨58305063455682815656051427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38870042303788543770700951 58305063455682815656051427)
              ·
                refine ⟨87457595183524223484077141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58305063455682815656051427 87457595183524223484077141)
                ·
                  refine ⟨1024893693556924493954029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 87457595183524223484077141 1024893693556924493954029)
                  ·
                    refine ⟨384335135083846685232761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1024893693556924493954029 384335135083846685232761)
                    ·
                      rfl

theorem cell22_1122735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 3].length) (baseStart_1122735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122735 prefixEnd_1122735 := by exact prefixLift 1122735
  have htrace : WordTrace (prefixWord ++ tailWord_1122735) baseStart_1122735 baseEnd_1122735 := by
    simpa [prefixWord, tailWord_1122735, baseEnd_1122735] using wordTrace_append hprefix tailTrace_1122735
  have hstable : (prefixWord ++ tailWord_1122735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122735).length < 2 ^ (prefixWord ++ tailWord_1122735).sum := by decide
  have hdescent : baseEnd_1122735 < baseStart_1122735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122825 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 2, 5]
def baseStart_1122825 : Nat := 118140960795 + 1122825 * 2 ^ 59
def prefixEnd_1122825 : Nat := 4983230072969 + 3 ^ 40 * 1122825 * 2
def baseEnd_1122825 : Nat := 384365943923116450482485

theorem tailTrace_1122825 : CollatzResearch.WordTrace tailWord_1122825 prefixEnd_1122825 384365943923116450482485 := by
  unfold tailWord_1122825
  simp only [CollatzResearch.WordTrace]
  refine ⟨40952792157204263088057929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27301861438136175392038619 40952792157204263088057929)
  ·
    refine ⟨30714594117903197316043447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40952792157204263088057929 30714594117903197316043447)
    ·
      refine ⟨46071891176854795974065171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30714594117903197316043447 46071891176854795974065171)
      ·
        refine ⟨69107836765282193961097757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46071891176854795974065171 69107836765282193961097757)
        ·
          refine ⟨25915438786980822735411659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69107836765282193961097757 25915438786980822735411659)
          ·
            refine ⟨38873158180471234103117489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25915438786980822735411659 38873158180471234103117489)
            ·
              refine ⟨29154868635353425577338117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38873158180471234103117489 29154868635353425577338117)
              ·
                refine ⟨5466537869128767295750897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29154868635353425577338117 5466537869128767295750897)
                ·
                  refine ⟨4099903401846575471813173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5466537869128767295750897 4099903401846575471813173)
                  ·
                    refine ⟨384365943923116450482485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4099903401846575471813173 384365943923116450482485)
                    ·
                      rfl

theorem cell22_1122825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_1122825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122825 prefixEnd_1122825 := by exact prefixLift 1122825
  have htrace : WordTrace (prefixWord ++ tailWord_1122825) baseStart_1122825 baseEnd_1122825 := by
    simpa [prefixWord, tailWord_1122825, baseEnd_1122825] using wordTrace_append hprefix tailTrace_1122825
  have hstable : (prefixWord ++ tailWord_1122825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122825).length < 2 ^ (prefixWord ++ tailWord_1122825).sum := by decide
  have hdescent : baseEnd_1122825 < baseStart_1122825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122844 : List Nat := [2, 2, 3, 1, 2, 2, 4, 1, 5]
def baseStart_1122844 : Nat := 118140960795 + 1122844 * 2 ^ 59
def prefixEnd_1122844 : Nat := 4983230072969 + 3 ^ 40 * 1122844 * 2
def baseEnd_1122844 : Nat := 128124149337135578085809

theorem tailTrace_1122844 : CollatzResearch.WordTrace tailWord_1122844 prefixEnd_1122844 128124149337135578085809 := by
  unfold tailWord_1122844
  simp only [CollatzResearch.WordTrace]
  refine ⟨20476742572067714666499793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27302323429423619555333057 20476742572067714666499793)
  ·
    refine ⟨15357556929050785999874845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20476742572067714666499793 15357556929050785999874845)
    ·
      refine ⟨5759083848394044749953067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15357556929050785999874845 5759083848394044749953067)
      ·
        refine ⟨8638625772591067124929601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5759083848394044749953067 8638625772591067124929601)
        ·
          refine ⟨6478969329443300343697201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8638625772591067124929601 6478969329443300343697201)
          ·
            refine ⟨4859226997082475257772901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6478969329443300343697201 4859226997082475257772901)
            ·
              refine ⟨911105061952964110832419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4859226997082475257772901 911105061952964110832419)
              ·
                refine ⟨1366657592929446166248629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911105061952964110832419 1366657592929446166248629)
                ·
                  refine ⟨128124149337135578085809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1366657592929446166248629 128124149337135578085809)
                  ·
                    rfl

theorem cell22_1122844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_1122844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122844 prefixEnd_1122844 := by exact prefixLift 1122844
  have htrace : WordTrace (prefixWord ++ tailWord_1122844) baseStart_1122844 baseEnd_1122844 := by
    simpa [prefixWord, tailWord_1122844, baseEnd_1122844] using wordTrace_append hprefix tailTrace_1122844
  have hstable : (prefixWord ++ tailWord_1122844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122844).length < 2 ^ (prefixWord ++ tailWord_1122844).sum := by decide
  have hdescent : baseEnd_1122844 < baseStart_1122844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122904 : List Nat := [2, 1, 2, 2, 1, 2, 4, 3, 2, 3]
def baseStart_1122904 : Nat := 118140960795 + 1122904 * 2 ^ 59
def prefixEnd_1122904 : Nat := 4983230072969 + 3 ^ 40 * 1122904 * 2
def baseEnd_1122904 : Nat := 384392987237586577757243

theorem tailTrace_1122904 : CollatzResearch.WordTrace tailWord_1122904 prefixEnd_1122904 384392987237586577757243 := by
  unfold tailWord_1122904
  simp only [CollatzResearch.WordTrace]
  refine ⟨20477836761959029790091883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27303782349278706386789177 20477836761959029790091883)
  ·
    refine ⟨30716755142938544685137825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20477836761959029790091883 30716755142938544685137825)
    ·
      refine ⟨23037566357203908513853369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30716755142938544685137825 23037566357203908513853369)
      ·
        refine ⟨17278174767902931385390027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23037566357203908513853369 17278174767902931385390027)
        ·
          refine ⟨25917262151854397078085041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17278174767902931385390027 25917262151854397078085041)
          ·
            refine ⟨19437946613890797808563781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25917262151854397078085041 19437946613890797808563781)
            ·
              refine ⟨3644614990104524589105709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19437946613890797808563781 3644614990104524589105709)
              ·
                refine ⟨1366730621289196720914641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3644614990104524589105709 1366730621289196720914641)
                ·
                  refine ⟨1025047965966897540685981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1366730621289196720914641 1025047965966897540685981)
                  ·
                    refine ⟨384392987237586577757243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1025047965966897540685981 384392987237586577757243)
                    ·
                      rfl

theorem cell22_1122904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_1122904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122904 prefixEnd_1122904 := by exact prefixLift 1122904
  have htrace : WordTrace (prefixWord ++ tailWord_1122904) baseStart_1122904 baseEnd_1122904 := by
    simpa [prefixWord, tailWord_1122904, baseEnd_1122904] using wordTrace_append hprefix tailTrace_1122904
  have hstable : (prefixWord ++ tailWord_1122904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122904).length < 2 ^ (prefixWord ++ tailWord_1122904).sum := by decide
  have hdescent : baseEnd_1122904 < baseStart_1122904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122934 : List Nat := [5, 1, 1, 2, 3, 1, 9]
def baseStart_1122934 : Nat := 118140960795 + 1122934 * 2 ^ 59
def prefixEnd_1122934 : Nat := 4983230072969 + 3 ^ 40 * 1122934 * 2
def baseEnd_1122934 : Nat := 14237157661136166648413

theorem tailTrace_1122934 : CollatzResearch.WordTrace tailWord_1122934 prefixEnd_1122934 14237157661136166648413 := by
  unfold tailWord_1122934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2559797982113085918985991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27304511809206249802517237 2559797982113085918985991)
  ·
    refine ⟨3839696973169628878478987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2559797982113085918985991 3839696973169628878478987)
    ·
      refine ⟨5759545459754443317718481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3839696973169628878478987 5759545459754443317718481)
      ·
        refine ⟨4319659094815832488288861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5759545459754443317718481 4319659094815832488288861)
        ·
          refine ⟨1619872160555937183108323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4319659094815832488288861 1619872160555937183108323)
          ·
            refine ⟨2429808240833905774662485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1619872160555937183108323 2429808240833905774662485)
            ·
              refine ⟨14237157661136166648413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2429808240833905774662485 14237157661136166648413)
              ·
                rfl

theorem cell22_1122934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 9].length) (baseStart_1122934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122934 prefixEnd_1122934 := by exact prefixLift 1122934
  have htrace : WordTrace (prefixWord ++ tailWord_1122934) baseStart_1122934 baseEnd_1122934 := by
    simpa [prefixWord, tailWord_1122934, baseEnd_1122934] using wordTrace_append hprefix tailTrace_1122934
  have hstable : (prefixWord ++ tailWord_1122934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122934).length < 2 ^ (prefixWord ++ tailWord_1122934).sum := by decide
  have hdescent : baseEnd_1122934 < baseStart_1122934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122949 : List Nat := [1, 3, 1, 1, 4, 2, 1, 3, 3, 3]
def baseStart_1122949 : Nat := 118140960795 + 1122949 * 2 ^ 59
def prefixEnd_1122949 : Nat := 4983230072969 + 3 ^ 40 * 1122949 * 2
def baseEnd_1122949 : Nat := 384408391657221460382105

theorem tailTrace_1122949 : CollatzResearch.WordTrace tailWord_1122949 prefixEnd_1122949 384408391657221460382105 := by
  unfold tailWord_1122949
  simp only [CollatzResearch.WordTrace]
  refine ⟨40957314808755032265571901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27304876539170021510381267 40957314808755032265571901)
  ·
    refine ⟨15358993053283137099589463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40957314808755032265571901 15358993053283137099589463)
    ·
      refine ⟨23038489579924705649384195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15358993053283137099589463 23038489579924705649384195)
      ·
        refine ⟨34557734369887058474076293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23038489579924705649384195 34557734369887058474076293)
        ·
          refine ⟨6479575194353823463889305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34557734369887058474076293 6479575194353823463889305)
          ·
            refine ⟨4859681395765367597916979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6479575194353823463889305 4859681395765367597916979)
            ·
              refine ⟨7289522093648051396875469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4859681395765367597916979 7289522093648051396875469)
              ·
                refine ⟨2733570785118019273828301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7289522093648051396875469 2733570785118019273828301)
                ·
                  refine ⟨1025089044419257227685613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2733570785118019273828301 1025089044419257227685613)
                  ·
                    refine ⟨384408391657221460382105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1025089044419257227685613 384408391657221460382105)
                    ·
                      rfl

theorem cell22_1122949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_1122949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122949 prefixEnd_1122949 := by exact prefixLift 1122949
  have htrace : WordTrace (prefixWord ++ tailWord_1122949) baseStart_1122949 baseEnd_1122949 := by
    simpa [prefixWord, tailWord_1122949, baseEnd_1122949] using wordTrace_append hprefix tailTrace_1122949
  have hstable : (prefixWord ++ tailWord_1122949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122949).length < 2 ^ (prefixWord ++ tailWord_1122949).sum := by decide
  have hdescent : baseEnd_1122949 < baseStart_1122949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1122992 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 5, 4]
def baseStart_1122992 : Nat := 118140960795 + 1122992 * 2 ^ 59
def prefixEnd_1122992 : Nat := 4983230072969 + 3 ^ 40 * 1122992 * 2
def baseEnd_1122992 : Nat := 384423111435983681556973

theorem tailTrace_1122992 : CollatzResearch.WordTrace tailWord_1122992 prefixEnd_1122992 384423111435983681556973 := by
  unfold tailWord_1122992
  simp only [CollatzResearch.WordTrace]
  refine ⟨20479441573799625304693615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27305922098399500406258153 20479441573799625304693615)
  ·
    refine ⟨30719162360699437957040423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20479441573799625304693615 30719162360699437957040423)
    ·
      refine ⟨46078743541049156935560635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30719162360699437957040423 46078743541049156935560635)
      ·
        refine ⟨69118115311573735403340953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46078743541049156935560635 69118115311573735403340953)
        ·
          refine ⟨51838586483680301552505715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69118115311573735403340953 51838586483680301552505715)
          ·
            refine ⟨77757879725520452328758573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51838586483680301552505715 77757879725520452328758573)
            ·
              refine ⟨29159204897070169623284465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77757879725520452328758573 29159204897070169623284465)
              ·
                refine ⟨21869403672802627217463349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29159204897070169623284465 21869403672802627217463349)
                ·
                  refine ⟨2050256594325246301637189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21869403672802627217463349 2050256594325246301637189)
                  ·
                    refine ⟨384423111435983681556973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2050256594325246301637189 384423111435983681556973)
                    ·
                      rfl

theorem cell22_1122992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_1122992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1122992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1122992 prefixEnd_1122992 := by exact prefixLift 1122992
  have htrace : WordTrace (prefixWord ++ tailWord_1122992) baseStart_1122992 baseEnd_1122992 := by
    simpa [prefixWord, tailWord_1122992, baseEnd_1122992] using wordTrace_append hprefix tailTrace_1122992
  have hstable : (prefixWord ++ tailWord_1122992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1122992).length < 2 ^ (prefixWord ++ tailWord_1122992).sum := by decide
  have hdescent : baseEnd_1122992 < baseStart_1122992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1122992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123026 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1123026 : Nat := 118140960795 + 1123026 * 2 ^ 59
def prefixEnd_1123026 : Nat := 4983230072969 + 3 ^ 40 * 1123026 * 2
def baseEnd_1123026 : Nat := 384434750330818926206869

theorem tailTrace_1123026 : CollatzResearch.WordTrace tailWord_1123026 prefixEnd_1123026 384434750330818926206869 := by
  unfold tailWord_1123026
  simp only [CollatzResearch.WordTrace]
  refine ⟨10240030807369018604031233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27306748819650716277416621 10240030807369018604031233)
  ·
    refine ⟨7680023105526763953023425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10240030807369018604031233 7680023105526763953023425)
    ·
      refine ⟨5760017329145072964767569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7680023105526763953023425 5760017329145072964767569)
      ·
        refine ⟨4320012996858804723575677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5760017329145072964767569 4320012996858804723575677)
        ·
          refine ⟨1620004873822051771340879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4320012996858804723575677 1620004873822051771340879)
          ·
            refine ⟨2430007310733077657011319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620004873822051771340879 2430007310733077657011319)
            ·
              refine ⟨3645010966099616485516979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430007310733077657011319 3645010966099616485516979)
              ·
                refine ⟨5467516449149424728275469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3645010966099616485516979 5467516449149424728275469)
                ·
                  refine ⟨2050318668431034273103301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5467516449149424728275469 2050318668431034273103301)
                  ·
                    refine ⟨384434750330818926206869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2050318668431034273103301 384434750330818926206869)
                    ·
                      rfl

theorem cell22_1123026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1123026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123026 prefixEnd_1123026 := by exact prefixLift 1123026
  have htrace : WordTrace (prefixWord ++ tailWord_1123026) baseStart_1123026 baseEnd_1123026 := by
    simpa [prefixWord, tailWord_1123026, baseEnd_1123026] using wordTrace_append hprefix tailTrace_1123026
  have hstable : (prefixWord ++ tailWord_1123026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123026).length < 2 ^ (prefixWord ++ tailWord_1123026).sum := by decide
  have hdescent : baseEnd_1123026 < baseStart_1123026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123039 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 1, 5]
def baseStart_1123039 : Nat := 118140960795 + 1123039 * 2 ^ 59
def prefixEnd_1123039 : Nat := 4983230072969 + 3 ^ 40 * 1123039 * 2
def baseEnd_1123039 : Nat := 384439200496491225631829

theorem tailTrace_1123039 : CollatzResearch.WordTrace tailWord_1123039 prefixEnd_1123039 384439200496491225631829 := by
  unfold tailWord_1123039
  simp only [CollatzResearch.WordTrace]
  refine ⟨40960597378428977636348171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27307064918952651757565447 40960597378428977636348171)
  ·
    refine ⟨61440896067643466454522257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40960597378428977636348171 61440896067643466454522257)
    ·
      refine ⟨46080672050732599840891693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61440896067643466454522257 46080672050732599840891693)
      ·
        refine ⟨17280252019024724940334385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46080672050732599840891693 17280252019024724940334385)
        ·
          refine ⟨12960189014268543705250789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17280252019024724940334385 12960189014268543705250789)
          ·
            refine ⟨2430035440175351944734523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12960189014268543705250789 2430035440175351944734523)
            ·
              refine ⟨3645053160263027917101785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430035440175351944734523 3645053160263027917101785)
              ·
                refine ⟨2733789870197270937826339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3645053160263027917101785 2733789870197270937826339)
                ·
                  refine ⟨4100684805295906406739509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2733789870197270937826339 4100684805295906406739509)
                  ·
                    refine ⟨384439200496491225631829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4100684805295906406739509 384439200496491225631829)
                    ·
                      rfl

theorem cell22_1123039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_1123039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123039 prefixEnd_1123039 := by exact prefixLift 1123039
  have htrace : WordTrace (prefixWord ++ tailWord_1123039) baseStart_1123039 baseEnd_1123039 := by
    simpa [prefixWord, tailWord_1123039, baseEnd_1123039] using wordTrace_append hprefix tailTrace_1123039
  have hstable : (prefixWord ++ tailWord_1123039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123039).length < 2 ^ (prefixWord ++ tailWord_1123039).sum := by decide
  have hdescent : baseEnd_1123039 < baseStart_1123039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123043 : List Nat := [1, 1, 1, 7, 1, 2, 3, 1, 1, 4]
def baseStart_1123043 : Nat := 118140960795 + 1123043 * 2 ^ 59
def prefixEnd_1123043 : Nat := 4983230072969 + 3 ^ 40 * 1123043 * 2
def baseEnd_1123043 : Nat := 384440569778236548531817

theorem tailTrace_1123043 : CollatzResearch.WordTrace tailWord_1123043 prefixEnd_1123043 384440569778236548531817 := by
  unfold tailWord_1123043
  simp only [CollatzResearch.WordTrace]
  refine ⟨40960743270414486319493783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27307162180276324212995855 40960743270414486319493783)
  ·
    refine ⟨61441114905621729479240675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40960743270414486319493783 61441114905621729479240675)
    ·
      refine ⟨92161672358432594218861013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61441114905621729479240675 92161672358432594218861013)
      ·
        refine ⟨2160039195900763927004555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 92161672358432594218861013 2160039195900763927004555)
        ·
          refine ⟨3240058793851145890506833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2160039195900763927004555 3240058793851145890506833)
          ·
            refine ⟨2430044095388359417880125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3240058793851145890506833 2430044095388359417880125)
            ·
              refine ⟨911266535770634781705047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2430044095388359417880125 911266535770634781705047)
              ·
                refine ⟨1366899803655952172557571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911266535770634781705047 1366899803655952172557571)
                ·
                  refine ⟨2050349705483928258836357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1366899803655952172557571 2050349705483928258836357)
                  ·
                    refine ⟨384440569778236548531817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2050349705483928258836357 384440569778236548531817)
                    ·
                      rfl

theorem cell22_1123043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 1, 4].length) (baseStart_1123043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123043 prefixEnd_1123043 := by exact prefixLift 1123043
  have htrace : WordTrace (prefixWord ++ tailWord_1123043) baseStart_1123043 baseEnd_1123043 := by
    simpa [prefixWord, tailWord_1123043, baseEnd_1123043] using wordTrace_append hprefix tailTrace_1123043
  have hstable : (prefixWord ++ tailWord_1123043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123043).length < 2 ^ (prefixWord ++ tailWord_1123043).sum := by decide
  have hdescent : baseEnd_1123043 < baseStart_1123043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123056 : List Nat := [2, 1, 1, 1, 3, 1, 6, 2, 2, 3]
def baseStart_1123056 : Nat := 118140960795 + 1123056 * 2 ^ 59
def prefixEnd_1123056 : Nat := 4983230072969 + 3 ^ 40 * 1123056 * 2
def baseEnd_1123056 : Nat := 384445019943908847956777

theorem tailTrace_1123056 : CollatzResearch.WordTrace tailWord_1123056 prefixEnd_1123056 384445019943908847956777 := by
  unfold tailWord_1123056
  simp only [CollatzResearch.WordTrace]
  refine ⟨20480608709683694769858511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27307478279578259693144681 20480608709683694769858511)
  ·
    refine ⟨30720913064525542154787767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20480608709683694769858511 30720913064525542154787767)
    ·
      refine ⟨46081369596788313232181651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30720913064525542154787767 46081369596788313232181651)
      ·
        refine ⟨69122054395182469848272477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46081369596788313232181651 69122054395182469848272477)
        ·
          refine ⟨25920770398193426193102179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69122054395182469848272477 25920770398193426193102179)
          ·
            refine ⟨38881155597290139289653269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25920770398193426193102179 38881155597290139289653269)
            ·
              refine ⟨1822554168622975279202497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38881155597290139289653269 1822554168622975279202497)
              ·
                refine ⟨1366915626467231459401873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1822554168622975279202497 1366915626467231459401873)
                ·
                  refine ⟨1025186719850423594551405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1366915626467231459401873 1025186719850423594551405)
                  ·
                    refine ⟨384445019943908847956777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1025186719850423594551405 384445019943908847956777)
                    ·
                      rfl

theorem cell22_1123056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 2, 3].length) (baseStart_1123056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123056 prefixEnd_1123056 := by exact prefixLift 1123056
  have htrace : WordTrace (prefixWord ++ tailWord_1123056) baseStart_1123056 baseEnd_1123056 := by
    simpa [prefixWord, tailWord_1123056, baseEnd_1123056] using wordTrace_append hprefix tailTrace_1123056
  have hstable : (prefixWord ++ tailWord_1123056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123056).length < 2 ^ (prefixWord ++ tailWord_1123056).sum := by decide
  have hdescent : baseEnd_1123056 < baseStart_1123056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123058 : List Nat := [3, 2, 1, 3, 1, 2, 4, 2, 4]
def baseStart_1123058 : Nat := 118140960795 + 1123058 * 2 ^ 59
def prefixEnd_1123058 : Nat := 4983230072969 + 3 ^ 40 * 1123058 * 2
def baseEnd_1123058 : Nat := 128148568194927169802257

theorem tailTrace_1123058 : CollatzResearch.WordTrace tailWord_1123058 prefixEnd_1123058 128148568194927169802257 := by
  unfold tailWord_1123058
  simp only [CollatzResearch.WordTrace]
  refine ⟨10240322591340035970322457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27307526910240095920859885 10240322591340035970322457)
  ·
    refine ⟨7680241943505026977741843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10240322591340035970322457 7680241943505026977741843)
    ·
      refine ⟨11520362915257540466612765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7680241943505026977741843 11520362915257540466612765)
      ·
        refine ⟨4320136093221577674979787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11520362915257540466612765 4320136093221577674979787)
        ·
          refine ⟨6480204139832366512469681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4320136093221577674979787 6480204139832366512469681)
          ·
            refine ⟨4860153104874274884352261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6480204139832366512469681 4860153104874274884352261)
            ·
              refine ⟨911278707163926540816049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4860153104874274884352261 911278707163926540816049)
              ·
                refine ⟨683459030372944905612037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911278707163926540816049 683459030372944905612037)
                ·
                  refine ⟨128148568194927169802257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 683459030372944905612037 128148568194927169802257)
                  ·
                    rfl

theorem cell22_1123058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_1123058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123058 prefixEnd_1123058 := by exact prefixLift 1123058
  have htrace : WordTrace (prefixWord ++ tailWord_1123058) baseStart_1123058 baseEnd_1123058 := by
    simpa [prefixWord, tailWord_1123058, baseEnd_1123058] using wordTrace_append hprefix tailTrace_1123058
  have hstable : (prefixWord ++ tailWord_1123058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123058).length < 2 ^ (prefixWord ++ tailWord_1123058).sum := by decide
  have hdescent : baseEnd_1123058 < baseStart_1123058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123118 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1123118 : Nat := 118140960795 + 1123118 * 2 ^ 59
def prefixEnd_1123118 : Nat := 4983230072969 + 3 ^ 40 * 1123118 * 2
def baseEnd_1123118 : Nat := 384466243810961352906587

theorem tailTrace_1123118 : CollatzResearch.WordTrace tailWord_1123118 prefixEnd_1123118 384466243810961352906587 := by
  unfold tailWord_1123118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120434843142846766059251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27308985830095182752316005 5120434843142846766059251)
  ·
    refine ⟨7680652264714270149088877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5120434843142846766059251 7680652264714270149088877)
    ·
      refine ⟨2880244599267851305908329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7680652264714270149088877 2880244599267851305908329)
      ·
        refine ⟨2160183449450888479431247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2880244599267851305908329 2160183449450888479431247)
        ·
          refine ⟨3240275174176332719146871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2160183449450888479431247 3240275174176332719146871)
          ·
            refine ⟨4860412761264499078720307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3240275174176332719146871 4860412761264499078720307)
            ·
              refine ⟨7290619141896748618080461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4860412761264499078720307 7290619141896748618080461)
              ·
                refine ⟨2733982178211280731780173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7290619141896748618080461 2733982178211280731780173)
                ·
                  refine ⟨1025243316829230274417565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2733982178211280731780173 1025243316829230274417565)
                  ·
                    refine ⟨384466243810961352906587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1025243316829230274417565 384466243810961352906587)
                    ·
                      rfl

theorem cell22_1123118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1123118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123118 prefixEnd_1123118 := by exact prefixLift 1123118
  have htrace : WordTrace (prefixWord ++ tailWord_1123118) baseStart_1123118 baseEnd_1123118 := by
    simpa [prefixWord, tailWord_1123118, baseEnd_1123118] using wordTrace_append hprefix tailTrace_1123118
  have hstable : (prefixWord ++ tailWord_1123118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123118).length < 2 ^ (prefixWord ++ tailWord_1123118).sum := by decide
  have hdescent : baseEnd_1123118 < baseStart_1123118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123161 : List Nat := [1, 2, 1, 2, 2, 4, 2, 3, 1, 4]
def baseStart_1123161 : Nat := 118140960795 + 1123161 * 2 ^ 59
def prefixEnd_1123161 : Nat := 4983230072969 + 3 ^ 40 * 1123161 * 2
def baseEnd_1123161 : Nat := 384480963589723574081455

theorem tailTrace_1123161 : CollatzResearch.WordTrace tailWord_1123161 prefixEnd_1123161 384480963589723574081455 := by
  unfold tailWord_1123161
  simp only [CollatzResearch.WordTrace]
  refine ⟨40965047083986992472289337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27310031389324661648192891 40965047083986992472289337)
  ·
    refine ⟨30723785312990244354217003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40965047083986992472289337 30723785312990244354217003)
    ·
      refine ⟨46085677969485366531325505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30723785312990244354217003 46085677969485366531325505)
      ·
        refine ⟨34564258477114024898494129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46085677969485366531325505 34564258477114024898494129)
        ·
          refine ⟨25923193857835518673870597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34564258477114024898494129 25923193857835518673870597)
          ·
            refine ⟨4860598848344159751350737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25923193857835518673870597 4860598848344159751350737)
            ·
              refine ⟨3645449136258119813513053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4860598848344159751350737 3645449136258119813513053)
              ·
                refine ⟨1367043426096794930067395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3645449136258119813513053 1367043426096794930067395)
                ·
                  refine ⟨2050565139145192395101093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367043426096794930067395 2050565139145192395101093)
                  ·
                    refine ⟨384480963589723574081455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2050565139145192395101093 384480963589723574081455)
                    ·
                      rfl

theorem cell22_1123161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_1123161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123161 prefixEnd_1123161 := by exact prefixLift 1123161
  have htrace : WordTrace (prefixWord ++ tailWord_1123161) baseStart_1123161 baseEnd_1123161 := by
    simpa [prefixWord, tailWord_1123161, baseEnd_1123161] using wordTrace_append hprefix tailTrace_1123161
  have hstable : (prefixWord ++ tailWord_1123161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123161).length < 2 ^ (prefixWord ++ tailWord_1123161).sum := by decide
  have hdescent : baseEnd_1123161 < baseStart_1123161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123176 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 6]
def baseStart_1123176 : Nat := 118140960795 + 1123176 * 2 ^ 59
def prefixEnd_1123176 : Nat := 4983230072969 + 3 ^ 40 * 1123176 * 2
def baseEnd_1123176 : Nat := 128162032798756178318803

theorem tailTrace_1123176 : CollatzResearch.WordTrace tailWord_1123176 prefixEnd_1123176 128162032798756178318803 := by
  unfold tailWord_1123176
  simp only [CollatzResearch.WordTrace]
  refine ⟨20482797089466325017042691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27310396119288433356056921 20482797089466325017042691)
  ·
    refine ⟨30724195634199487525564037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20482797089466325017042691 30724195634199487525564037)
    ·
      refine ⟨5760786681412403911043257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30724195634199487525564037 5760786681412403911043257)
      ·
        refine ⟨4320590011059302933282443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5760786681412403911043257 4320590011059302933282443)
        ·
          refine ⟨6480885016588954399923665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4320590011059302933282443 6480885016588954399923665)
          ·
            refine ⟨4860663762441715799942749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6480885016588954399923665 4860663762441715799942749)
            ·
              refine ⟨1822748910915643424978531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4860663762441715799942749 1822748910915643424978531)
              ·
                refine ⟨2734123366373465137467797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822748910915643424978531 2734123366373465137467797)
                ·
                  refine ⟨128162032798756178318803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2734123366373465137467797 128162032798756178318803)
                  ·
                    rfl

theorem cell22_1123176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 6].length) (baseStart_1123176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123176 prefixEnd_1123176 := by exact prefixLift 1123176
  have htrace : WordTrace (prefixWord ++ tailWord_1123176) baseStart_1123176 baseEnd_1123176 := by
    simpa [prefixWord, tailWord_1123176, baseEnd_1123176] using wordTrace_append hprefix tailTrace_1123176
  have hstable : (prefixWord ++ tailWord_1123176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123176).length < 2 ^ (prefixWord ++ tailWord_1123176).sum := by decide
  have hdescent : baseEnd_1123176 < baseStart_1123176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123182 : List Nat := [4, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_1123182 : Nat := 118140960795 + 1123182 * 2 ^ 59
def prefixEnd_1123182 : Nat := 4983230072969 + 3 ^ 40 * 1123182 * 2
def baseEnd_1123182 : Nat := 128162717439628839768797

theorem tailTrace_1123182 : CollatzResearch.WordTrace tailWord_1123182 prefixEnd_1123182 128162717439628839768797 := by
  unfold tailWord_1123182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120726627113864132350475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27310542011273942039202533 5120726627113864132350475)
  ·
    refine ⟨7681089940670796198525713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5120726627113864132350475 7681089940670796198525713)
    ·
      refine ⟨5760817455503097148894285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7681089940670796198525713 5760817455503097148894285)
      ·
        refine ⟨2160306545813661430835357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5760817455503097148894285 2160306545813661430835357)
        ·
          refine ⟨810114954680123036563259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2160306545813661430835357 810114954680123036563259)
          ·
            refine ⟨1215172432020184554844889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810114954680123036563259 1215172432020184554844889)
            ·
              refine ⟨911379324015138416133667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1215172432020184554844889 911379324015138416133667)
              ·
                refine ⟨1367068986022707624200501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911379324015138416133667 1367068986022707624200501)
                ·
                  refine ⟨128162717439628839768797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1367068986022707624200501 128162717439628839768797)
                  ·
                    rfl

theorem cell22_1123182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_1123182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123182 prefixEnd_1123182 := by exact prefixLift 1123182
  have htrace : WordTrace (prefixWord ++ tailWord_1123182) baseStart_1123182 baseEnd_1123182 := by
    simpa [prefixWord, tailWord_1123182, baseEnd_1123182] using wordTrace_append hprefix tailTrace_1123182
  have hstable : (prefixWord ++ tailWord_1123182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123182).length < 2 ^ (prefixWord ++ tailWord_1123182).sum := by decide
  have hdescent : baseEnd_1123182 < baseStart_1123182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123253 : List Nat := [1, 3, 3, 2, 1, 1, 3, 2, 3, 3]
def baseStart_1123253 : Nat := 118140960795 + 1123253 * 2 ^ 59
def prefixEnd_1123253 : Nat := 4983230072969 + 3 ^ 40 * 1123253 * 2
def baseEnd_1123253 : Nat := 384512457069866000781173

theorem tailTrace_1123253 : CollatzResearch.WordTrace tailWord_1123253 prefixEnd_1123253 384512457069866000781173 := by
  unfold tailWord_1123253
  simp only [CollatzResearch.WordTrace]
  refine ⟨40968402599653692184638413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27312268399769128123092275 40968402599653692184638413)
  ·
    refine ⟨15363150974870134569239405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40968402599653692184638413 15363150974870134569239405)
    ·
      refine ⟨5761181615576300463464777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15363150974870134569239405 5761181615576300463464777)
      ·
        refine ⟨4320886211682225347598583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5761181615576300463464777 4320886211682225347598583)
        ·
          refine ⟨6481329317523338021397875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4320886211682225347598583 6481329317523338021397875)
          ·
            refine ⟨9721993976285007032096813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6481329317523338021397875 9721993976285007032096813)
            ·
              refine ⟨3645747741106877637036305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9721993976285007032096813 3645747741106877637036305)
              ·
                refine ⟨2734310805830158227777229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3645747741106877637036305 2734310805830158227777229)
                ·
                  refine ⟨1025366552186309335416461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2734310805830158227777229 1025366552186309335416461)
                  ·
                    refine ⟨384512457069866000781173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1025366552186309335416461 384512457069866000781173)
                    ·
                      rfl

theorem cell22_1123253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_1123253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123253 prefixEnd_1123253 := by exact prefixLift 1123253
  have htrace : WordTrace (prefixWord ++ tailWord_1123253) baseStart_1123253 baseEnd_1123253 := by
    simpa [prefixWord, tailWord_1123253, baseEnd_1123253] using wordTrace_append hprefix tailTrace_1123253
  have hstable : (prefixWord ++ tailWord_1123253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123253).length < 2 ^ (prefixWord ++ tailWord_1123253).sum := by decide
  have hdescent : baseEnd_1123253 < baseStart_1123253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123311 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 6]
def baseStart_1123311 : Nat := 118140960795 + 1123311 * 2 ^ 59
def prefixEnd_1123311 : Nat := 4983230072969 + 3 ^ 40 * 1123311 * 2
def baseEnd_1123311 : Nat := 128177437218391060943665

theorem tailTrace_1123311 : CollatzResearch.WordTrace tailWord_1123311 prefixEnd_1123311 128177437218391060943665 := by
  unfold tailWord_1123311
  simp only [CollatzResearch.WordTrace]
  refine ⟨40970518033443568090249787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27313678688962378726833191 40970518033443568090249787)
  ·
    refine ⟨61455777050165352135374681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40970518033443568090249787 61455777050165352135374681)
    ·
      refine ⟨46091832787624014101531011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61455777050165352135374681 46091832787624014101531011)
      ·
        refine ⟨69137749181436021152296517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46091832787624014101531011 69137749181436021152296517)
        ·
          refine ⟨12963327971519253966055597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69137749181436021152296517 12963327971519253966055597)
          ·
            refine ⟨4861247989319720237270849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12963327971519253966055597 4861247989319720237270849)
            ·
              refine ⟨3645935991989790177953137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4861247989319720237270849 3645935991989790177953137)
              ·
                refine ⟨2734451993992342633464853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3645935991989790177953137 2734451993992342633464853)
                ·
                  refine ⟨128177437218391060943665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2734451993992342633464853 128177437218391060943665)
                  ·
                    rfl

theorem cell22_1123311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 6].length) (baseStart_1123311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123311 prefixEnd_1123311 := by exact prefixLift 1123311
  have htrace : WordTrace (prefixWord ++ tailWord_1123311) baseStart_1123311 baseEnd_1123311 := by
    simpa [prefixWord, tailWord_1123311, baseEnd_1123311] using wordTrace_append hprefix tailTrace_1123311
  have hstable : (prefixWord ++ tailWord_1123311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123311).length < 2 ^ (prefixWord ++ tailWord_1123311).sum := by decide
  have hdescent : baseEnd_1123311 < baseStart_1123311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123313 : List Nat := [1, 2, 2, 2, 4, 1, 1, 4, 1, 4]
def baseStart_1123313 : Nat := 118140960795 + 1123313 * 2 ^ 59
def prefixEnd_1123313 : Nat := 4983230072969 + 3 ^ 40 * 1123313 * 2
def baseEnd_1123313 : Nat := 384532996296045844280989

theorem tailTrace_1123313 : CollatzResearch.WordTrace tailWord_1123313 prefixEnd_1123313 384532996296045844280989 := by
  unfold tailWord_1123313
  simp only [CollatzResearch.WordTrace]
  refine ⟨40970590979436322431822593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27313727319624214954548395 40970590979436322431822593)
  ·
    refine ⟨30727943234577241823866945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40970590979436322431822593 30727943234577241823866945)
    ·
      refine ⟨23045957425932931367900209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30727943234577241823866945 23045957425932931367900209)
      ·
        refine ⟨17284468069449698525925157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23045957425932931367900209 17284468069449698525925157)
        ·
          refine ⟨3240837763021818473610967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17284468069449698525925157 3240837763021818473610967)
          ·
            refine ⟨4861256644532727710416451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3240837763021818473610967 4861256644532727710416451)
            ·
              refine ⟨7291884966799091565624677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4861256644532727710416451 7291884966799091565624677)
              ·
                refine ⟨1367228431274829668554627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7291884966799091565624677 1367228431274829668554627)
                ·
                  refine ⟨2050842646912244502831941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367228431274829668554627 2050842646912244502831941)
                  ·
                    refine ⟨384532996296045844280989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2050842646912244502831941 384532996296045844280989)
                    ·
                      rfl

theorem cell22_1123313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_1123313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123313 prefixEnd_1123313 := by exact prefixLift 1123313
  have htrace : WordTrace (prefixWord ++ tailWord_1123313) baseStart_1123313 baseEnd_1123313 := by
    simpa [prefixWord, tailWord_1123313, baseEnd_1123313] using wordTrace_append hprefix tailTrace_1123313
  have hstable : (prefixWord ++ tailWord_1123313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123313).length < 2 ^ (prefixWord ++ tailWord_1123313).sum := by decide
  have hdescent : baseEnd_1123313 < baseStart_1123313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123482 : List Nat := [3, 1, 1, 5, 1, 2, 2, 2, 1, 4]
def baseStart_1123482 : Nat := 118140960795 + 1123482 * 2 ^ 59
def prefixEnd_1123482 : Nat := 4983230072969 + 3 ^ 40 * 1123482 * 2
def baseEnd_1123482 : Nat := 384590848449785736805471

theorem tailTrace_1123482 : CollatzResearch.WordTrace tailWord_1123482 prefixEnd_1123482 384590848449785736805471 := by
  unfold tailWord_1123482
  simp only [CollatzResearch.WordTrace]
  refine ⟨10244188728956016073681175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27317836610549376196483133 10244188728956016073681175)
  ·
    refine ⟨15366283093434024110521763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10244188728956016073681175 15366283093434024110521763)
    ·
      refine ⟨23049424640151036165782645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15366283093434024110521763 23049424640151036165782645)
      ·
        refine ⟨2160883560014159640542123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23049424640151036165782645 2160883560014159640542123)
        ·
          refine ⟨3241325340021239460813185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2160883560014159640542123 3241325340021239460813185)
          ·
            refine ⟨2430994005015929595609889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3241325340021239460813185 2430994005015929595609889)
            ·
              refine ⟨1823245503761947196707417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2430994005015929595609889 1823245503761947196707417)
              ·
                refine ⟨1367434127821460397530563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1823245503761947196707417 1367434127821460397530563)
                ·
                  refine ⟨2051151191732190596295845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367434127821460397530563 2051151191732190596295845)
                  ·
                    refine ⟨384590848449785736805471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2051151191732190596295845 384590848449785736805471)
                    ·
                      rfl

theorem cell22_1123482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_1123482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123482 prefixEnd_1123482 := by exact prefixLift 1123482
  have htrace : WordTrace (prefixWord ++ tailWord_1123482) baseStart_1123482 baseEnd_1123482 := by
    simpa [prefixWord, tailWord_1123482, baseEnd_1123482] using wordTrace_append hprefix tailTrace_1123482
  have hstable : (prefixWord ++ tailWord_1123482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123482).length < 2 ^ (prefixWord ++ tailWord_1123482).sum := by decide
  have hdescent : baseEnd_1123482 < baseStart_1123482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123493 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_1123493 : Nat := 118140960795 + 1123493 * 2 ^ 59
def prefixEnd_1123493 : Nat := 4983230072969 + 3 ^ 40 * 1123493 * 2
def baseEnd_1123493 : Nat := 384594613974585374780437

theorem tailTrace_1123493 : CollatzResearch.WordTrace tailWord_1123493 prefixEnd_1123493 384594613974585374780437 := by
  unfold tailWord_1123493
  simp only [CollatzResearch.WordTrace]
  refine ⟨40977156118784213173375133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27318104079189475448916755 40977156118784213173375133)
  ·
    refine ⟨15366433544544079940015675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40977156118784213173375133 15366433544544079940015675)
    ·
      refine ⟨23049650316816119910023513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15366433544544079940015675 23049650316816119910023513)
      ·
        refine ⟨17287237737612089932517635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23049650316816119910023513 17287237737612089932517635)
        ·
          refine ⟨25930856606418134898776453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17287237737612089932517635 25930856606418134898776453)
          ·
            refine ⟨4862035613703400293520585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25930856606418134898776453 4862035613703400293520585)
            ·
              refine ⟨3646526710277550220140439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4862035613703400293520585 3646526710277550220140439)
              ·
                refine ⟨5469790065416325330210659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3646526710277550220140439 5469790065416325330210659)
                ·
                  refine ⟨8204685098124487995315989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5469790065416325330210659 8204685098124487995315989)
                  ·
                    refine ⟨384594613974585374780437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8204685098124487995315989 384594613974585374780437)
                    ·
                      rfl

theorem cell22_1123493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_1123493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123493 prefixEnd_1123493 := by exact prefixLift 1123493
  have htrace : WordTrace (prefixWord ++ tailWord_1123493) baseStart_1123493 baseEnd_1123493 := by
    simpa [prefixWord, tailWord_1123493, baseEnd_1123493] using wordTrace_append hprefix tailTrace_1123493
  have hstable : (prefixWord ++ tailWord_1123493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123493).length < 2 ^ (prefixWord ++ tailWord_1123493).sum := by decide
  have hdescent : baseEnd_1123493 < baseStart_1123493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123533 : List Nat := [1, 6, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1123533 : Nat := 118140960795 + 1123533 * 2 ^ 59
def prefixEnd_1123533 : Nat := 4983230072969 + 3 ^ 40 * 1123533 * 2
def baseEnd_1123533 : Nat := 384608306792038603780315

theorem tailTrace_1123533 : CollatzResearch.WordTrace tailWord_1123533 prefixEnd_1123533 384608306792038603780315 := by
  unfold tailWord_1123533
  simp only [CollatzResearch.WordTrace]
  refine ⟨40978615038639300004831253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27319076692426200003220835 40978615038639300004831253)
  ·
    refine ⟨1920872579936217187726465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40978615038639300004831253 1920872579936217187726465)
    ·
      refine ⟨1440654434952162890794849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1920872579936217187726465 1440654434952162890794849)
      ·
        refine ⟨1080490826214122168096137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1440654434952162890794849 1080490826214122168096137)
        ·
          refine ⟨810368119660591626072103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1080490826214122168096137 810368119660591626072103)
          ·
            refine ⟨1215552179490887439108155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810368119660591626072103 1215552179490887439108155)
            ·
              refine ⟨1823328269236331158662233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215552179490887439108155 1823328269236331158662233)
              ·
                refine ⟨1367496201927248368996675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1823328269236331158662233 1367496201927248368996675)
                ·
                  refine ⟨2051244302890872553495013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367496201927248368996675 2051244302890872553495013)
                  ·
                    refine ⟨384608306792038603780315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2051244302890872553495013 384608306792038603780315)
                    ·
                      rfl

theorem cell22_1123533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1123533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123533 prefixEnd_1123533 := by exact prefixLift 1123533
  have htrace : WordTrace (prefixWord ++ tailWord_1123533) baseStart_1123533 baseEnd_1123533 := by
    simpa [prefixWord, tailWord_1123533, baseEnd_1123533] using wordTrace_append hprefix tailTrace_1123533
  have hstable : (prefixWord ++ tailWord_1123533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123533).length < 2 ^ (prefixWord ++ tailWord_1123533).sum := by decide
  have hdescent : baseEnd_1123533 < baseStart_1123533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123585 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1123585 : Nat := 118140960795 + 1123585 * 2 ^ 59
def prefixEnd_1123585 : Nat := 4983230072969 + 3 ^ 40 * 1123585 * 2
def baseEnd_1123585 : Nat := 384626107454727801480155

theorem tailTrace_1123585 : CollatzResearch.WordTrace tailWord_1123585 prefixEnd_1123585 384626107454727801480155 := by
  unfold tailWord_1123585
  simp only [CollatzResearch.WordTrace]
  refine ⟨40980511634450912885724209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27320341089633941923816139 40980511634450912885724209)
  ·
    refine ⟨30735383725838184664293157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40980511634450912885724209 30735383725838184664293157)
    ·
      refine ⟨5762884448594659624554967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30735383725838184664293157 5762884448594659624554967)
      ·
        refine ⟨8644326672891989436832451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5762884448594659624554967 8644326672891989436832451)
        ·
          refine ⟨12966490009337984155248677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8644326672891989436832451 12966490009337984155248677)
          ·
            refine ⟨2431216876750872029109127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12966490009337984155248677 2431216876750872029109127)
            ·
              refine ⟨3646825315126308043663691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431216876750872029109127 3646825315126308043663691)
              ·
                refine ⟨5470237972689462065495537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3646825315126308043663691 5470237972689462065495537)
                ·
                  refine ⟨4102678479517096549121653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5470237972689462065495537 4102678479517096549121653)
                  ·
                    refine ⟨384626107454727801480155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4102678479517096549121653 384626107454727801480155)
                    ·
                      rfl

theorem cell22_1123585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1123585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123585 prefixEnd_1123585 := by exact prefixLift 1123585
  have htrace : WordTrace (prefixWord ++ tailWord_1123585) baseStart_1123585 baseEnd_1123585 := by
    simpa [prefixWord, tailWord_1123585, baseEnd_1123585] using wordTrace_append hprefix tailTrace_1123585
  have hstable : (prefixWord ++ tailWord_1123585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123585).length < 2 ^ (prefixWord ++ tailWord_1123585).sum := by decide
  have hdescent : baseEnd_1123585 < baseStart_1123585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123647 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 1, 5]
def baseStart_1123647 : Nat := 118140960795 + 1123647 * 2 ^ 59
def prefixEnd_1123647 : Nat := 4983230072969 + 3 ^ 40 * 1123647 * 2
def baseEnd_1123647 : Nat := 384647331321780306429965

theorem tailTrace_1123647 : CollatzResearch.WordTrace tailWord_1123647 prefixEnd_1123647 384647331321780306429965 := by
  unfold tailWord_1123647
  simp only [CollatzResearch.WordTrace]
  refine ⟨40982772960226297474481195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27321848640150864982987463 40982772960226297474481195)
  ·
    refine ⟨61474159440339446211721793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40982772960226297474481195 61474159440339446211721793)
    ·
      refine ⟨46105619580254584658791345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61474159440339446211721793 46105619580254584658791345)
      ·
        refine ⟨34579214685190938494093509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46105619580254584658791345 34579214685190938494093509)
        ·
          refine ⟨6483602753473300967642533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34579214685190938494093509 6483602753473300967642533)
          ·
            refine ⟨1215675516276243931432975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6483602753473300967642533 1215675516276243931432975)
            ·
              refine ⟨1823513274414365897149463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215675516276243931432975 1823513274414365897149463)
              ·
                refine ⟨2735269911621548845724195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1823513274414365897149463 2735269911621548845724195)
                ·
                  refine ⟨4102904867432323268586293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2735269911621548845724195 4102904867432323268586293)
                  ·
                    refine ⟨384647331321780306429965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4102904867432323268586293 384647331321780306429965)
                    ·
                      rfl

theorem cell22_1123647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 5].length) (baseStart_1123647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123647 prefixEnd_1123647 := by exact prefixLift 1123647
  have htrace : WordTrace (prefixWord ++ tailWord_1123647) baseStart_1123647 baseEnd_1123647 := by
    simpa [prefixWord, tailWord_1123647, baseEnd_1123647] using wordTrace_append hprefix tailTrace_1123647
  have hstable : (prefixWord ++ tailWord_1123647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123647).length < 2 ^ (prefixWord ++ tailWord_1123647).sum := by decide
  have hdescent : baseEnd_1123647 < baseStart_1123647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123660 : List Nat := [2, 2, 1, 3, 2, 3, 1, 8]
def baseStart_1123660 : Nat := 118140960795 + 1123660 * 2 ^ 59
def prefixEnd_1123660 : Nat := 4983230072969 + 3 ^ 40 * 1123660 * 2
def baseEnd_1123660 : Nat := 42739086831939178428325

theorem tailTrace_1123660 : CollatzResearch.WordTrace tailWord_1123660 prefixEnd_1123660 42739086831939178428325 := by
  unfold tailWord_1123660
  simp only [CollatzResearch.WordTrace]
  refine ⟨20491623554589600347352217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27322164739452800463136289 20491623554589600347352217)
  ·
    refine ⟨15368717665942200260514163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20491623554589600347352217 15368717665942200260514163)
    ·
      refine ⟨23053076498913300390771245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15368717665942200260514163 23053076498913300390771245)
      ·
        refine ⟨8644903687092487646539217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23053076498913300390771245 8644903687092487646539217)
        ·
          refine ⟨6483677765319365734904413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8644903687092487646539217 6483677765319365734904413)
          ·
            refine ⟨2431379161994762150589155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6483677765319365734904413 2431379161994762150589155)
            ·
              refine ⟨3647068742992143225883733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431379161994762150589155 3647068742992143225883733)
              ·
                refine ⟨42739086831939178428325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3647068742992143225883733 42739086831939178428325)
                ·
                  rfl

theorem cell22_1123660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 8].length) (baseStart_1123660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123660 prefixEnd_1123660 := by exact prefixLift 1123660
  have htrace : WordTrace (prefixWord ++ tailWord_1123660) baseStart_1123660 baseEnd_1123660 := by
    simpa [prefixWord, tailWord_1123660, baseEnd_1123660] using wordTrace_append hprefix tailTrace_1123660
  have hstable : (prefixWord ++ tailWord_1123660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123660).length < 2 ^ (prefixWord ++ tailWord_1123660).sum := by decide
  have hdescent : baseEnd_1123660 < baseStart_1123660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123694 : List Nat := [4, 1, 2, 4, 1, 1, 2, 7]
def baseStart_1123694 : Nat := 118140960795 + 1123694 * 2 ^ 59
def prefixEnd_1123694 : Nat := 4983230072969 + 3 ^ 40 * 1123694 * 2
def baseEnd_1123694 : Nat := 42740380042476427833869

theorem tailTrace_1123694 : CollatzResearch.WordTrace tailWord_1123694 prefixEnd_1123694 42740380042476427833869 := by
  unfold tailWord_1123694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5123060898882003062680267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27322991460704016334294757 5123060898882003062680267)
  ·
    refine ⟨7684591348323004594020401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5123060898882003062680267 7684591348323004594020401)
    ·
      refine ⟨5763443511242253445515301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7684591348323004594020401 5763443511242253445515301)
      ·
        refine ⟨1080645658357922521034119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5763443511242253445515301 1080645658357922521034119)
        ·
          refine ⟨1620968487536883781551179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1080645658357922521034119 1620968487536883781551179)
          ·
            refine ⟨2431452731305325672326769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620968487536883781551179 2431452731305325672326769)
            ·
              refine ⟨1823589548478994254245077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2431452731305325672326769 1823589548478994254245077)
              ·
                refine ⟨42740380042476427833869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1823589548478994254245077 42740380042476427833869)
                ·
                  rfl

theorem cell22_1123694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_1123694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123694 prefixEnd_1123694 := by exact prefixLift 1123694
  have htrace : WordTrace (prefixWord ++ tailWord_1123694) baseStart_1123694 baseEnd_1123694 := by
    simpa [prefixWord, tailWord_1123694, baseEnd_1123694] using wordTrace_append hprefix tailTrace_1123694
  have hstable : (prefixWord ++ tailWord_1123694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123694).length < 2 ^ (prefixWord ++ tailWord_1123694).sum := by decide
  have hdescent : baseEnd_1123694 < baseStart_1123694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123743 : List Nat := [1, 1, 2, 5, 1, 4, 2, 2, 1, 3]
def baseStart_1123743 : Nat := 118140960795 + 1123743 * 2 ^ 59
def prefixEnd_1123743 : Nat := 4983230072969 + 3 ^ 40 * 1123743 * 2
def baseEnd_1123743 : Nat := 384680194083668056029671

theorem tailTrace_1123743 : CollatzResearch.WordTrace tailWord_1123743 prefixEnd_1123743 384680194083668056029671 := by
  unfold tailWord_1123743
  simp only [CollatzResearch.WordTrace]
  refine ⟨40986274367878505869975883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27324182911919003913317255 40986274367878505869975883)
  ·
    refine ⟨61479411551817758804963825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40986274367878505869975883 61479411551817758804963825)
    ·
      refine ⟨46109558663863319103722869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61479411551817758804963825 46109558663863319103722869)
      ·
        refine ⟨4322771124737186165974019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46109558663863319103722869 4322771124737186165974019)
        ·
          refine ⟨6484156687105779248961029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4322771124737186165974019 6484156687105779248961029)
          ·
            refine ⟨1215779378832333609180193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6484156687105779248961029 1215779378832333609180193)
            ·
              refine ⟨911834534124250206885145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1215779378832333609180193 911834534124250206885145)
              ·
                refine ⟨683875900593187655163859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 911834534124250206885145 683875900593187655163859)
                ·
                  refine ⟨1025813850889781482745789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683875900593187655163859 1025813850889781482745789)
                  ·
                    refine ⟨384680194083668056029671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1025813850889781482745789 384680194083668056029671)
                    ·
                      rfl

theorem cell22_1123743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 1, 3].length) (baseStart_1123743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123743 prefixEnd_1123743 := by exact prefixLift 1123743
  have htrace : WordTrace (prefixWord ++ tailWord_1123743) baseStart_1123743 baseEnd_1123743 := by
    simpa [prefixWord, tailWord_1123743, baseEnd_1123743] using wordTrace_append hprefix tailTrace_1123743
  have hstable : (prefixWord ++ tailWord_1123743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123743).length < 2 ^ (prefixWord ++ tailWord_1123743).sum := by decide
  have hdescent : baseEnd_1123743 < baseStart_1123743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123784 : List Nat := [2, 1, 3, 1, 3, 1, 4, 3, 4]
def baseStart_1123784 : Nat := 118140960795 + 1123784 * 2 ^ 59
def prefixEnd_1123784 : Nat := 4983230072969 + 3 ^ 40 * 1123784 * 2
def baseEnd_1123784 : Nat := 128231409740519205251515

theorem tailTrace_1123784 : CollatzResearch.WordTrace tailWord_1123784 prefixEnd_1123784 128231409740519205251515 := by
  unfold tailWord_1123784
  simp only [CollatzResearch.WordTrace]
  refine ⟨20493884880364984936109203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27325179840486646581478937 20493884880364984936109203)
  ·
    refine ⟨30740827320547477404163805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20493884880364984936109203 30740827320547477404163805)
    ·
      refine ⟨11527810245205304026561427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30740827320547477404163805 11527810245205304026561427)
      ·
        refine ⟨17291715367807956039842141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11527810245205304026561427 17291715367807956039842141)
        ·
          refine ⟨6484393262927983514940803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17291715367807956039842141 6484393262927983514940803)
          ·
            refine ⟨9726589894391975272411205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6484393262927983514940803 9726589894391975272411205)
            ·
              refine ⟨1823735605198495363577101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9726589894391975272411205 1823735605198495363577101)
              ·
                refine ⟨683900851949435761341413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1823735605198495363577101 683900851949435761341413)
                ·
                  refine ⟨128231409740519205251515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 683900851949435761341413 128231409740519205251515)
                  ·
                    rfl

theorem cell22_1123784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 4].length) (baseStart_1123784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123784 prefixEnd_1123784 := by exact prefixLift 1123784
  have htrace : WordTrace (prefixWord ++ tailWord_1123784) baseStart_1123784 baseEnd_1123784 := by
    simpa [prefixWord, tailWord_1123784, baseEnd_1123784] using wordTrace_append hprefix tailTrace_1123784
  have hstable : (prefixWord ++ tailWord_1123784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123784).length < 2 ^ (prefixWord ++ tailWord_1123784).sum := by decide
  have hdescent : baseEnd_1123784 < baseStart_1123784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123786 : List Nat := [3, 1, 2, 1, 2, 5, 2, 1, 1, 4]
def baseStart_1123786 : Nat := 118140960795 + 1123786 * 2 ^ 59
def prefixEnd_1123786 : Nat := 4983230072969 + 3 ^ 40 * 1123786 * 2
def baseEnd_1123786 : Nat := 384694913862430277204539

theorem tailTrace_1123786 : CollatzResearch.WordTrace tailWord_1123786 prefixEnd_1123786 384694913862430277204539 := by
  unfold tailWord_1123786
  simp only [CollatzResearch.WordTrace]
  refine ⟨10246960676680681053447803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27325228471148482809194141 10246960676680681053447803)
  ·
    refine ⟨15370441015021021580171705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10246960676680681053447803 15370441015021021580171705)
    ·
      refine ⟨11527830761265766185128779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15370441015021021580171705 11527830761265766185128779)
      ·
        refine ⟨17291746141898649277693169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11527830761265766185128779 17291746141898649277693169)
        ·
          refine ⟨12968809606423986958269877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17291746141898649277693169 12968809606423986958269877)
          ·
            refine ⟨1215825900602248777337801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12968809606423986958269877 1215825900602248777337801)
            ·
              refine ⟨911869425451686583003351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1215825900602248777337801 911869425451686583003351)
              ·
                refine ⟨1367804138177529874505027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911869425451686583003351 1367804138177529874505027)
                ·
                  refine ⟨2051706207266294811757541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1367804138177529874505027 2051706207266294811757541)
                  ·
                    refine ⟨384694913862430277204539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2051706207266294811757541 384694913862430277204539)
                    ·
                      rfl

theorem cell22_1123786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_1123786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123786 prefixEnd_1123786 := by exact prefixLift 1123786
  have htrace : WordTrace (prefixWord ++ tailWord_1123786) baseStart_1123786 baseEnd_1123786 := by
    simpa [prefixWord, tailWord_1123786, baseEnd_1123786] using wordTrace_append hprefix tailTrace_1123786
  have hstable : (prefixWord ++ tailWord_1123786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123786).length < 2 ^ (prefixWord ++ tailWord_1123786).sum := by decide
  have hdescent : baseEnd_1123786 < baseStart_1123786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123797 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_1123797 : Nat := 118140960795 + 1123797 * 2 ^ 59
def prefixEnd_1123797 : Nat := 4983230072969 + 3 ^ 40 * 1123797 * 2
def baseEnd_1123797 : Nat := 384698679387229915179505

theorem tailTrace_1123797 : CollatzResearch.WordTrace tailWord_1123797 prefixEnd_1123797 384698679387229915179505 := by
  unfold tailWord_1123797
  simp only [CollatzResearch.WordTrace]
  refine ⟨40988243909682873092441645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27325495939788582061627763 40988243909682873092441645)
  ·
    refine ⟨15370591466131077409665617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40988243909682873092441645 15370591466131077409665617)
    ·
      refine ⟨11527943599598308057249213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15370591466131077409665617 11527943599598308057249213)
      ·
        refine ⟨4322978849849365521468455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11527943599598308057249213 4322978849849365521468455)
        ·
          refine ⟨6484468274774048282202683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4322978849849365521468455 6484468274774048282202683)
          ·
            refine ⟨9726702412161072423304025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6484468274774048282202683 9726702412161072423304025)
            ·
              refine ⟨7295026809120804317478019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9726702412161072423304025 7295026809120804317478019)
              ·
                refine ⟨10942540213681206476217029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7295026809120804317478019 10942540213681206476217029)
                ·
                  refine ⟨2051726290065226214290693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10942540213681206476217029 2051726290065226214290693)
                  ·
                    refine ⟨384698679387229915179505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2051726290065226214290693 384698679387229915179505)
                    ·
                      rfl

theorem cell22_1123797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_1123797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123797 prefixEnd_1123797 := by exact prefixLift 1123797
  have htrace : WordTrace (prefixWord ++ tailWord_1123797) baseStart_1123797 baseEnd_1123797 := by
    simpa [prefixWord, tailWord_1123797, baseEnd_1123797] using wordTrace_append hprefix tailTrace_1123797
  have hstable : (prefixWord ++ tailWord_1123797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123797).length < 2 ^ (prefixWord ++ tailWord_1123797).sum := by decide
  have hdescent : baseEnd_1123797 < baseStart_1123797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123816 : List Nat := [2, 1, 4, 1, 1, 2, 5, 1, 2, 3]
def baseStart_1123816 : Nat := 118140960795 + 1123816 * 2 ^ 59
def prefixEnd_1123816 : Nat := 4983230072969 + 3 ^ 40 * 1123816 * 2
def baseEnd_1123816 : Nat := 384705183475520198954447

theorem tailTrace_1123816 : CollatzResearch.WordTrace tailWord_1123816 prefixEnd_1123816 384705183475520198954447 := by
  unfold tailWord_1123816
  simp only [CollatzResearch.WordTrace]
  refine ⟨20494468448307019668691651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27325957931076026224922201 20494468448307019668691651)
  ·
    refine ⟨30741702672460529503037477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20494468448307019668691651 30741702672460529503037477)
    ·
      refine ⟨5764069251086349281819527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30741702672460529503037477 5764069251086349281819527)
      ·
        refine ⟨8646103876629523922729291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5764069251086349281819527 8646103876629523922729291)
        ·
          refine ⟨12969155814944285884093937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8646103876629523922729291 12969155814944285884093937)
          ·
            refine ⟨9726866861208214413070453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12969155814944285884093937 9726866861208214413070453)
            ·
              refine ⟨911893768238270101225355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9726866861208214413070453 911893768238270101225355)
              ·
                refine ⟨1367840652357405151838033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 911893768238270101225355 1367840652357405151838033)
                ·
                  refine ⟨1025880489268053863878525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1367840652357405151838033 1025880489268053863878525)
                  ·
                    refine ⟨384705183475520198954447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1025880489268053863878525 384705183475520198954447)
                    ·
                      rfl

theorem cell22_1123816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_1123816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123816 prefixEnd_1123816 := by exact prefixLift 1123816
  have htrace : WordTrace (prefixWord ++ tailWord_1123816) baseStart_1123816 baseEnd_1123816 := by
    simpa [prefixWord, tailWord_1123816, baseEnd_1123816] using wordTrace_append hprefix tailTrace_1123816
  have hstable : (prefixWord ++ tailWord_1123816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123816).length < 2 ^ (prefixWord ++ tailWord_1123816).sum := by decide
  have hdescent : baseEnd_1123816 < baseStart_1123816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123827 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 5, 3]
def baseStart_1123827 : Nat := 118140960795 + 1123827 * 2 ^ 59
def prefixEnd_1123827 : Nat := 4983230072969 + 3 ^ 40 * 1123827 * 2
def baseEnd_1123827 : Nat := 384708949000319836929413

theorem tailTrace_1123827 : CollatzResearch.WordTrace tailWord_1123827 prefixEnd_1123827 384708949000319836929413 := by
  unfold tailWord_1123827
  simp only [CollatzResearch.WordTrace]
  refine ⟨40989338099574188216033735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27326225399716125477355823 40989338099574188216033735)
  ·
    refine ⟨61484007149361282324050603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40989338099574188216033735 61484007149361282324050603)
    ·
      refine ⟨92226010724041923486075905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61484007149361282324050603 92226010724041923486075905)
      ·
        refine ⟨69169508043031442614556929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92226010724041923486075905 69169508043031442614556929)
        ·
          refine ⟨51877131032273581960917697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69169508043031442614556929 51877131032273581960917697)
          ·
            refine ⟨38907848274205186470688273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51877131032273581960917697 38907848274205186470688273)
            ·
              refine ⟨29180886205653889853016205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38907848274205186470688273 29180886205653889853016205)
              ·
                refine ⟨10942832327120208694881077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29180886205653889853016205 10942832327120208694881077)
                ·
                  refine ⟨1025890530667519565145101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10942832327120208694881077 1025890530667519565145101)
                  ·
                    refine ⟨384708949000319836929413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1025890530667519565145101 384708949000319836929413)
                    ·
                      rfl

theorem cell22_1123827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 3].length) (baseStart_1123827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123827 prefixEnd_1123827 := by exact prefixLift 1123827
  have htrace : WordTrace (prefixWord ++ tailWord_1123827) baseStart_1123827 baseEnd_1123827 := by
    simpa [prefixWord, tailWord_1123827, baseEnd_1123827] using wordTrace_append hprefix tailTrace_1123827
  have hstable : (prefixWord ++ tailWord_1123827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123827).length < 2 ^ (prefixWord ++ tailWord_1123827).sum := by decide
  have hdescent : baseEnd_1123827 < baseStart_1123827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123829 : List Nat := [1, 3, 5, 1, 1, 2, 1, 8]
def baseStart_1123829 : Nat := 118140960795 + 1123829 * 2 ^ 59
def prefixEnd_1123829 : Nat := 4983230072969 + 3 ^ 40 * 1123829 * 2
def baseEnd_1123829 : Nat := 42745514849021388708823

theorem tailTrace_1123829 : CollatzResearch.WordTrace tailWord_1123829 prefixEnd_1123829 42745514849021388708823 := by
  unfold tailWord_1123829
  simp only [CollatzResearch.WordTrace]
  refine ⟨40989411045566942557606541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27326274030377961705071027 40989411045566942557606541)
  ·
    refine ⟨15371029142087603459102453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40989411045566942557606541 15371029142087603459102453)
    ·
      refine ⟨1441033982070712824290855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15371029142087603459102453 1441033982070712824290855)
      ·
        refine ⟨2161550973106069236436283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441033982070712824290855 2161550973106069236436283)
        ·
          refine ⟨3242326459659103854654425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2161550973106069236436283 3242326459659103854654425)
          ·
            refine ⟨2431744844744327890990819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3242326459659103854654425 2431744844744327890990819)
            ·
              refine ⟨3647617267116491836486229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431744844744327890990819 3647617267116491836486229)
              ·
                refine ⟨42745514849021388708823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3647617267116491836486229 42745514849021388708823)
                ·
                  rfl

theorem cell22_1123829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 8].length) (baseStart_1123829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123829 prefixEnd_1123829 := by exact prefixLift 1123829
  have htrace : WordTrace (prefixWord ++ tailWord_1123829) baseStart_1123829 baseEnd_1123829 := by
    simpa [prefixWord, tailWord_1123829, baseEnd_1123829] using wordTrace_append hprefix tailTrace_1123829
  have hstable : (prefixWord ++ tailWord_1123829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123829).length < 2 ^ (prefixWord ++ tailWord_1123829).sum := by decide
  have hdescent : baseEnd_1123829 < baseStart_1123829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123857 : List Nat := [1, 2, 2, 1, 1, 2, 4, 4, 5]
def baseStart_1123857 : Nat := 118140960795 + 1123857 * 2 ^ 59
def prefixEnd_1123857 : Nat := 4983230072969 + 3 ^ 40 * 1123857 * 2
def baseEnd_1123857 : Nat := 128239739537803252893107

theorem tailTrace_1123857 : CollatzResearch.WordTrace tailWord_1123857 prefixEnd_1123857 128239739537803252893107 := by
  unfold tailWord_1123857
  simp only [CollatzResearch.WordTrace]
  refine ⟨40990432289465503339625825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27326954859643668893083883 40990432289465503339625825)
  ·
    refine ⟨30742824217099127504719369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40990432289465503339625825 30742824217099127504719369)
    ·
      refine ⟨23057118162824345628539527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30742824217099127504719369 23057118162824345628539527)
      ·
        refine ⟨34585677244236518442809291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23057118162824345628539527 34585677244236518442809291)
        ·
          refine ⟨51878515866354777664213937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34585677244236518442809291 51878515866354777664213937)
          ·
            refine ⟨38908886899766083248160453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51878515866354777664213937 38908886899766083248160453)
            ·
              refine ⟨7295416293706140609030085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38908886899766083248160453 7295416293706140609030085)
              ·
                refine ⟨1367890555069901364193141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7295416293706140609030085 1367890555069901364193141)
                ·
                  refine ⟨128239739537803252893107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1367890555069901364193141 128239739537803252893107)
                  ·
                    rfl

theorem cell22_1123857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 5].length) (baseStart_1123857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123857 prefixEnd_1123857 := by exact prefixLift 1123857
  have htrace : WordTrace (prefixWord ++ tailWord_1123857) baseStart_1123857 baseEnd_1123857 := by
    simpa [prefixWord, tailWord_1123857, baseEnd_1123857] using wordTrace_append hprefix tailTrace_1123857
  have hstable : (prefixWord ++ tailWord_1123857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123857).length < 2 ^ (prefixWord ++ tailWord_1123857).sum := by decide
  have hdescent : baseEnd_1123857 < baseStart_1123857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123861 : List Nat := [1, 3, 2, 1, 3, 4, 1, 1, 3, 3]
def baseStart_1123861 : Nat := 118140960795 + 1123861 * 2 ^ 59
def prefixEnd_1123861 : Nat := 4983230072969 + 3 ^ 40 * 1123861 * 2
def baseEnd_1123861 : Nat := 384720587895155081579309

theorem tailTrace_1123861 : CollatzResearch.WordTrace tailWord_1123861 prefixEnd_1123861 384720587895155081579309 := by
  unfold tailWord_1123861
  simp only [CollatzResearch.WordTrace]
  refine ⟨40990578181451012022771437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27327052120967341348514291 40990578181451012022771437)
  ·
    refine ⟨15371466818044129508539289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40990578181451012022771437 15371466818044129508539289)
    ·
      refine ⟨11528600113533097131404467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15371466818044129508539289 11528600113533097131404467)
      ·
        refine ⟨17292900170299645697106701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11528600113533097131404467 17292900170299645697106701)
        ·
          refine ⟨6484837563862367136415013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17292900170299645697106701 6484837563862367136415013)
          ·
            refine ⟨1215907043224193838077815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6484837563862367136415013 1215907043224193838077815)
            ·
              refine ⟨1823860564836290757116723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1215907043224193838077815 1823860564836290757116723)
              ·
                refine ⟨2735790847254436135675085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1823860564836290757116723 2735790847254436135675085)
                ·
                  refine ⟨1025921567720413550878157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2735790847254436135675085 1025921567720413550878157)
                  ·
                    refine ⟨384720587895155081579309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1025921567720413550878157 384720587895155081579309)
                    ·
                      rfl

theorem cell22_1123861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_1123861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123861 prefixEnd_1123861 := by exact prefixLift 1123861
  have htrace : WordTrace (prefixWord ++ tailWord_1123861) baseStart_1123861 baseEnd_1123861 := by
    simpa [prefixWord, tailWord_1123861, baseEnd_1123861] using wordTrace_append hprefix tailTrace_1123861
  have hstable : (prefixWord ++ tailWord_1123861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123861).length < 2 ^ (prefixWord ++ tailWord_1123861).sum := by decide
  have hdescent : baseEnd_1123861 < baseStart_1123861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123977 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 1, 8]
def baseStart_1123977 : Nat := 118140960795 + 1123977 * 2 ^ 59
def prefixEnd_1123977 : Nat := 4983230072969 + 3 ^ 40 * 1123977 * 2
def baseEnd_1123977 : Nat := 384760297065769445678953

theorem tailTrace_1123977 : CollatzResearch.WordTrace tailWord_1123977 prefixEnd_1123977 384760297065769445678953 := by
  unfold tailWord_1123977
  simp only [CollatzResearch.WordTrace]
  refine ⟨40994809049030763833994185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27329872699353842555996123 40994809049030763833994185)
  ·
    refine ⟨30746106786773072875495639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40994809049030763833994185 30746106786773072875495639)
    ·
      refine ⟨46119160180159609313243459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30746106786773072875495639 46119160180159609313243459)
      ·
        refine ⟨69178740270239413969865189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46119160180159609313243459 69178740270239413969865189)
        ·
          refine ⟨12971013800669890119349723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69178740270239413969865189 12971013800669890119349723)
          ·
            refine ⟨19456520701004835179024585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12971013800669890119349723 19456520701004835179024585)
            ·
              refine ⟨14592390525753626384268439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19456520701004835179024585 14592390525753626384268439)
              ·
                refine ⟨21888585788630439576402659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14592390525753626384268439 21888585788630439576402659)
                ·
                  refine ⟨32832878682945659364603989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21888585788630439576402659 32832878682945659364603989)
                  ·
                    refine ⟨384760297065769445678953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32832878682945659364603989 384760297065769445678953)
                    ·
                      rfl

theorem cell22_1123977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_1123977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123977 prefixEnd_1123977 := by exact prefixLift 1123977
  have htrace : WordTrace (prefixWord ++ tailWord_1123977) baseStart_1123977 baseEnd_1123977 := by
    simpa [prefixWord, tailWord_1123977, baseEnd_1123977] using wordTrace_append hprefix tailTrace_1123977
  have hstable : (prefixWord ++ tailWord_1123977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123977).length < 2 ^ (prefixWord ++ tailWord_1123977).sum := by decide
  have hdescent : baseEnd_1123977 < baseStart_1123977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1123998 : List Nat := [4, 3, 1, 1, 1, 4, 2, 6]
def baseStart_1123998 : Nat := 118140960795 + 1123998 * 2 ^ 59
def prefixEnd_1123998 : Nat := 4983230072969 + 3 ^ 40 * 1123998 * 2
def baseEnd_1123998 : Nat := 42751942866103598989321

theorem tailTrace_1123998 : CollatzResearch.WordTrace tailWord_1123998 prefixEnd_1123998 42751942866103598989321 := by
  unfold tailWord_1123998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5124446872744335552563581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27330383321303122947005765 5124446872744335552563581)
  ·
    refine ⟨1921667577279125832211343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5124446872744335552563581 1921667577279125832211343)
    ·
      refine ⟨2882501365918688748317015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1921667577279125832211343 2882501365918688748317015)
      ·
        refine ⟨4323752048878033122475523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2882501365918688748317015 4323752048878033122475523)
        ·
          refine ⟨6485628073317049683713285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4323752048878033122475523 6485628073317049683713285)
          ·
            refine ⟨1216055263746946815696241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6485628073317049683713285 1216055263746946815696241)
            ·
              refine ⟨912041447810210111772181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1216055263746946815696241 912041447810210111772181)
              ·
                refine ⟨42751942866103598989321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 912041447810210111772181 42751942866103598989321)
                ·
                  rfl

theorem cell22_1123998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_1123998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1123998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1123998 prefixEnd_1123998 := by exact prefixLift 1123998
  have htrace : WordTrace (prefixWord ++ tailWord_1123998) baseStart_1123998 baseEnd_1123998 := by
    simpa [prefixWord, tailWord_1123998, baseEnd_1123998] using wordTrace_append hprefix tailTrace_1123998
  have hstable : (prefixWord ++ tailWord_1123998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1123998).length < 2 ^ (prefixWord ++ tailWord_1123998).sum := by decide
  have hdescent : baseEnd_1123998 < baseStart_1123998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1123998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124039 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 3, 4]
def baseStart_1124039 : Nat := 118140960795 + 1124039 * 2 ^ 59
def prefixEnd_1124039 : Nat := 4983230072969 + 3 ^ 40 * 1124039 * 2
def baseEnd_1124039 : Nat := 384781520932821950628763

theorem tailTrace_1124039 : CollatzResearch.WordTrace tailWord_1124039 prefixEnd_1124039 384781520932821950628763 := by
  unfold tailWord_1124039
  simp only [CollatzResearch.WordTrace]
  refine ⟨40997070374806148422751171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27331380249870765615167447 40997070374806148422751171)
  ·
    refine ⟨61495605562209222634126757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40997070374806148422751171 61495605562209222634126757)
    ·
      refine ⟨11530426042914229243898767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61495605562209222634126757 11530426042914229243898767)
      ·
        refine ⟨17295639064371343865848151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11530426042914229243898767 17295639064371343865848151)
        ·
          refine ⟨25943458596557015798772227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17295639064371343865848151 25943458596557015798772227)
          ·
            refine ⟨38915187894835523698158341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25943458596557015798772227 38915187894835523698158341)
            ·
              refine ⟨7296597730281660693404689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38915187894835523698158341 7296597730281660693404689)
              ·
                refine ⟨5472448297711245520053517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7296597730281660693404689 5472448297711245520053517)
                ·
                  refine ⟨2052168111641717070020069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5472448297711245520053517 2052168111641717070020069)
                  ·
                    refine ⟨384781520932821950628763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2052168111641717070020069 384781520932821950628763)
                    ·
                      rfl

theorem cell22_1124039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_1124039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124039 prefixEnd_1124039 := by exact prefixLift 1124039
  have htrace : WordTrace (prefixWord ++ tailWord_1124039) baseStart_1124039 baseEnd_1124039 := by
    simpa [prefixWord, tailWord_1124039, baseEnd_1124039] using wordTrace_append hprefix tailTrace_1124039
  have hstable : (prefixWord ++ tailWord_1124039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124039).length < 2 ^ (prefixWord ++ tailWord_1124039).sum := by decide
  have hdescent : baseEnd_1124039 < baseStart_1124039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124099 : List Nat := [1, 1, 1, 3, 2, 2, 5, 7]
def baseStart_1124099 : Nat := 118140960795 + 1124099 * 2 ^ 59
def prefixEnd_1124099 : Nat := 4983230072969 + 3 ^ 40 * 1124099 * 2
def baseEnd_1124099 : Nat := 42755784462111310458731

theorem tailTrace_1124099 : CollatzResearch.WordTrace tailWord_1124099 prefixEnd_1124099 42755784462111310458731 := by
  unfold tailWord_1124099
  simp only [CollatzResearch.WordTrace]
  refine ⟨40999258754588778669935351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27332839169725852446623567 40999258754588778669935351)
  ·
    refine ⟨61498888131883168004903027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40999258754588778669935351 61498888131883168004903027)
    ·
      refine ⟨92248332197824752007354541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61498888131883168004903027 92248332197824752007354541)
      ·
        refine ⟨34593124574184282002757953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92248332197824752007354541 34593124574184282002757953)
        ·
          refine ⟨25944843430638211502068465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34593124574184282002757953 25944843430638211502068465)
          ·
            refine ⟨19458632572978658626551349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25944843430638211502068465 19458632572978658626551349)
            ·
              refine ⟨1824246803716749246239189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19458632572978658626551349 1824246803716749246239189)
              ·
                refine ⟨42755784462111310458731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1824246803716749246239189 42755784462111310458731)
                ·
                  rfl

theorem cell22_1124099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 7].length) (baseStart_1124099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124099 prefixEnd_1124099 := by exact prefixLift 1124099
  have htrace : WordTrace (prefixWord ++ tailWord_1124099) baseStart_1124099 baseEnd_1124099 := by
    simpa [prefixWord, tailWord_1124099, baseEnd_1124099] using wordTrace_append hprefix tailTrace_1124099
  have hstable : (prefixWord ++ tailWord_1124099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124099).length < 2 ^ (prefixWord ++ tailWord_1124099).sum := by decide
  have hdescent : baseEnd_1124099 < baseStart_1124099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124103 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 1, 5]
def baseStart_1124103 : Nat := 118140960795 + 1124103 * 2 ^ 59
def prefixEnd_1124103 : Nat := 4983230072969 + 3 ^ 40 * 1124103 * 2
def baseEnd_1124103 : Nat := 384803429440747117028567

theorem tailTrace_1124103 : CollatzResearch.WordTrace tailWord_1124103 prefixEnd_1124103 384803429440747117028567 := by
  unfold tailWord_1124103
  simp only [CollatzResearch.WordTrace]
  refine ⟨40999404646574287353080963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27332936431049524902053975 40999404646574287353080963)
  ·
    refine ⟨61499106969861431029621445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40999404646574287353080963 61499106969861431029621445)
    ·
      refine ⟨11531082556849018318054021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61499106969861431029621445 11531082556849018318054021)
      ·
        refine ⟨2162077979409190934635129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11531082556849018318054021 2162077979409190934635129)
        ·
          refine ⟨1621558484556893200976347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2162077979409190934635129 1621558484556893200976347)
          ·
            refine ⟨2432337726835339801464521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621558484556893200976347 2432337726835339801464521)
            ·
              refine ⟨1824253295126504851098391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2432337726835339801464521 1824253295126504851098391)
              ·
                refine ⟨2736379942689757276647587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824253295126504851098391 2736379942689757276647587)
                ·
                  refine ⟨4104569914034635914971381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736379942689757276647587 4104569914034635914971381)
                  ·
                    refine ⟨384803429440747117028567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4104569914034635914971381 384803429440747117028567)
                    ·
                      rfl

theorem cell22_1124103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_1124103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124103 prefixEnd_1124103 := by exact prefixLift 1124103
  have htrace : WordTrace (prefixWord ++ tailWord_1124103) baseStart_1124103 baseEnd_1124103 := by
    simpa [prefixWord, tailWord_1124103, baseEnd_1124103] using wordTrace_append hprefix tailTrace_1124103
  have hstable : (prefixWord ++ tailWord_1124103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124103).length < 2 ^ (prefixWord ++ tailWord_1124103).sum := by decide
  have hdescent : baseEnd_1124103 < baseStart_1124103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124221 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_1124221 : Nat := 118140960795 + 1124221 * 2 ^ 59
def prefixEnd_1124221 : Nat := 4983230072969 + 3 ^ 40 * 1124221 * 2
def baseEnd_1124221 : Nat := 384843823252234142578205

theorem tailTrace_1124221 : CollatzResearch.WordTrace tailWord_1124221 prefixEnd_1124221 384843823252234142578205 := by
  unfold tailWord_1124221
  simp only [CollatzResearch.WordTrace]
  refine ⟨41003708460146793505876517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27335805640097862337251011 41003708460146793505876517)
  ·
    refine ⟨7688195336277523782351847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41003708460146793505876517 7688195336277523782351847)
    ·
      refine ⟨11532293004416285673527771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7688195336277523782351847 11532293004416285673527771)
      ·
        refine ⟨17298439506624428510291657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11532293004416285673527771 17298439506624428510291657)
        ·
          refine ⟨12973829629968321382718743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17298439506624428510291657 12973829629968321382718743)
          ·
            refine ⟨19460744444952482074078115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12973829629968321382718743 19460744444952482074078115)
            ·
              refine ⟨29191116667428723111117173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19460744444952482074078115 29191116667428723111117173)
              ·
                refine ⟨2736667187571442791667235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29191116667428723111117173 2736667187571442791667235)
                ·
                  refine ⟨4105000781357164187500853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2736667187571442791667235 4105000781357164187500853)
                  ·
                    refine ⟨384843823252234142578205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4105000781357164187500853 384843823252234142578205)
                    ·
                      rfl

theorem cell22_1124221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_1124221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124221 prefixEnd_1124221 := by exact prefixLift 1124221
  have htrace : WordTrace (prefixWord ++ tailWord_1124221) baseStart_1124221 baseEnd_1124221 := by
    simpa [prefixWord, tailWord_1124221, baseEnd_1124221] using wordTrace_append hprefix tailTrace_1124221
  have hstable : (prefixWord ++ tailWord_1124221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124221).length < 2 ^ (prefixWord ++ tailWord_1124221).sum := by decide
  have hdescent : baseEnd_1124221 < baseStart_1124221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124225 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 3, 4]
def baseStart_1124225 : Nat := 118140960795 + 1124225 * 2 ^ 59
def prefixEnd_1124225 : Nat := 4983230072969 + 3 ^ 40 * 1124225 * 2
def baseEnd_1124225 : Nat := 384845192533979465478193

theorem tailTrace_1124225 : CollatzResearch.WordTrace tailWord_1124225 prefixEnd_1124225 384845192533979465478193 := by
  unfold tailWord_1124225
  simp only [CollatzResearch.WordTrace]
  refine ⟨41003854352132302189022129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27335902901421534792681419 41003854352132302189022129)
  ·
    refine ⟨30752890764099226641766597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41003854352132302189022129 30752890764099226641766597)
    ·
      refine ⟨5766167018268604995331237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30752890764099226641766597 5766167018268604995331237)
      ·
        refine ⟨1081156315925363436624607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5766167018268604995331237 1081156315925363436624607)
        ·
          refine ⟨1621734473888045154936911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1081156315925363436624607 1621734473888045154936911)
          ·
            refine ⟨2432601710832067732405367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621734473888045154936911 2432601710832067732405367)
            ·
              refine ⟨3648902566248101598608051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2432601710832067732405367 3648902566248101598608051)
              ·
                refine ⟨5473353849372152397912077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3648902566248101598608051 5473353849372152397912077)
                ·
                  refine ⟨2052507693514557149217029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5473353849372152397912077 2052507693514557149217029)
                  ·
                    refine ⟨384845192533979465478193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2052507693514557149217029 384845192533979465478193)
                    ·
                      rfl

theorem cell22_1124225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_1124225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124225 prefixEnd_1124225 := by exact prefixLift 1124225
  have htrace : WordTrace (prefixWord ++ tailWord_1124225) baseStart_1124225 baseEnd_1124225 := by
    simpa [prefixWord, tailWord_1124225, baseEnd_1124225] using wordTrace_append hprefix tailTrace_1124225
  have hstable : (prefixWord ++ tailWord_1124225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124225).length < 2 ^ (prefixWord ++ tailWord_1124225).sum := by decide
  have hdescent : baseEnd_1124225 < baseStart_1124225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124242 : List Nat := [3, 2, 3, 2, 1, 2, 3, 1, 1, 4]
def baseStart_1124242 : Nat := 118140960795 + 1124242 * 2 ^ 59
def prefixEnd_1124242 : Nat := 4983230072969 + 3 ^ 40 * 1124242 * 2
def baseEnd_1124242 : Nat := 384851011981397087803141

theorem tailTrace_1124242 : CollatzResearch.WordTrace tailWord_1124242 prefixEnd_1124242 384851011981397087803141 := by
  unfold tailWord_1124242
  simp only [CollatzResearch.WordTrace]
  refine ⟨10251118598267678523097745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27336316262047142728260653 10251118598267678523097745)
  ·
    refine ⟨7688338948700758892323309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10251118598267678523097745 7688338948700758892323309)
    ·
      refine ⟨2883127105762784584621241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7688338948700758892323309 2883127105762784584621241)
      ·
        refine ⟨2162345329322088438465931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2883127105762784584621241 2162345329322088438465931)
        ·
          refine ⟨3243517993983132657698897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2162345329322088438465931 3243517993983132657698897)
          ·
            refine ⟨2432638495487349493274173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3243517993983132657698897 2432638495487349493274173)
            ·
              refine ⟨912239435807756059977815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2432638495487349493274173 912239435807756059977815)
              ·
                refine ⟨1368359153711634089966723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912239435807756059977815 1368359153711634089966723)
                ·
                  refine ⟨2052538730567451134950085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368359153711634089966723 2052538730567451134950085)
                  ·
                    refine ⟨384851011981397087803141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2052538730567451134950085 384851011981397087803141)
                    ·
                      rfl

theorem cell22_1124242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_1124242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124242 prefixEnd_1124242 := by exact prefixLift 1124242
  have htrace : WordTrace (prefixWord ++ tailWord_1124242) baseStart_1124242 baseEnd_1124242 := by
    simpa [prefixWord, tailWord_1124242, baseEnd_1124242] using wordTrace_append hprefix tailTrace_1124242
  have hstable : (prefixWord ++ tailWord_1124242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124242).length < 2 ^ (prefixWord ++ tailWord_1124242).sum := by decide
  have hdescent : baseEnd_1124242 < baseStart_1124242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124253 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1124253 : Nat := 118140960795 + 1124253 * 2 ^ 59
def prefixEnd_1124253 : Nat := 4983230072969 + 3 ^ 40 * 1124253 * 2
def baseEnd_1124253 : Nat := 384854777506196725778107

theorem tailTrace_1124253 : CollatzResearch.WordTrace tailWord_1124253 prefixEnd_1124253 384854777506196725778107 := by
  unfold tailWord_1124253
  simp only [CollatzResearch.WordTrace]
  refine ⟨41004875596030862971041413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27336583730687241980694275 41004875596030862971041413)
  ·
    refine ⟨7688414174255786807070265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41004875596030862971041413 7688414174255786807070265)
    ·
      refine ⟨5766310630691840105302699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7688414174255786807070265 5766310630691840105302699)
      ·
        refine ⟨8649465946037760157954049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5766310630691840105302699 8649465946037760157954049)
        ·
          refine ⟨6487099459528320118465537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8649465946037760157954049 6487099459528320118465537)
          ·
            refine ⟨4865324594646240088849153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6487099459528320118465537 4865324594646240088849153)
            ·
              refine ⟨3648993445984680066636865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4865324594646240088849153 3648993445984680066636865)
              ·
                refine ⟨2736745084488510049977649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3648993445984680066636865 2736745084488510049977649)
                ·
                  refine ⟨2052558813366382537483237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2736745084488510049977649 2052558813366382537483237)
                  ·
                    refine ⟨384854777506196725778107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2052558813366382537483237 384854777506196725778107)
                    ·
                      rfl

theorem cell22_1124253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1124253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124253 prefixEnd_1124253 := by exact prefixLift 1124253
  have htrace : WordTrace (prefixWord ++ tailWord_1124253) baseStart_1124253 baseEnd_1124253 := by
    simpa [prefixWord, tailWord_1124253, baseEnd_1124253] using wordTrace_append hprefix tailTrace_1124253
  have hstable : (prefixWord ++ tailWord_1124253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124253).length < 2 ^ (prefixWord ++ tailWord_1124253).sum := by decide
  have hdescent : baseEnd_1124253 < baseStart_1124253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124281 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 2, 6]
def baseStart_1124281 : Nat := 118140960795 + 1124281 * 2 ^ 59
def prefixEnd_1124281 : Nat := 4983230072969 + 3 ^ 40 * 1124281 * 2
def baseEnd_1124281 : Nat := 384864362478413986078021

theorem tailTrace_1124281 : CollatzResearch.WordTrace tailWord_1124281 prefixEnd_1124281 384864362478413986078021 := by
  unfold tailWord_1124281
  simp only [CollatzResearch.WordTrace]
  refine ⟨41005896839929423753060697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27337264559952949168707131 41005896839929423753060697)
  ·
    refine ⟨30754422629947067814795523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41005896839929423753060697 30754422629947067814795523)
    ·
      refine ⟨46131633944920601722193285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30754422629947067814795523 46131633944920601722193285)
      ·
        refine ⟨8649681364672612822911241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46131633944920601722193285 8649681364672612822911241)
        ·
          refine ⟨6487261023504459617183431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8649681364672612822911241 6487261023504459617183431)
          ·
            refine ⟨9730891535256689425775147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6487261023504459617183431 9730891535256689425775147)
            ·
              refine ⟨14596337302885034138662721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9730891535256689425775147 14596337302885034138662721)
              ·
                refine ⟨10947252977163775603997041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14596337302885034138662721 10947252977163775603997041)
                ·
                  refine ⟨8210439732872831702997781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10947252977163775603997041 8210439732872831702997781)
                  ·
                    refine ⟨384864362478413986078021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8210439732872831702997781 384864362478413986078021)
                    ·
                      rfl

theorem cell22_1124281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_1124281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124281 prefixEnd_1124281 := by exact prefixLift 1124281
  have htrace : WordTrace (prefixWord ++ tailWord_1124281) baseStart_1124281 baseEnd_1124281 := by
    simpa [prefixWord, tailWord_1124281, baseEnd_1124281] using wordTrace_append hprefix tailTrace_1124281
  have hstable : (prefixWord ++ tailWord_1124281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124281).length < 2 ^ (prefixWord ++ tailWord_1124281).sum := by decide
  have hdescent : baseEnd_1124281 < baseStart_1124281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124311 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 4, 5]
def baseStart_1124311 : Nat := 118140960795 + 1124311 * 2 ^ 59
def prefixEnd_1124311 : Nat := 4983230072969 + 3 ^ 40 * 1124311 * 2
def baseEnd_1124311 : Nat := 384874632091503907827929

theorem tailTrace_1124311 : CollatzResearch.WordTrace tailWord_1124311 prefixEnd_1124311 384874632091503907827929 := by
  unfold tailWord_1124311
  simp only [CollatzResearch.WordTrace]
  refine ⟨41006991029820738876652787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27337994019880492584435191 41006991029820738876652787)
  ·
    refine ⟨61510486544731108314979181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41006991029820738876652787 61510486544731108314979181)
    ·
      refine ⟨23066432454274165618117193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61510486544731108314979181 23066432454274165618117193)
      ·
        refine ⟨17299824340705624213587895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23066432454274165618117193 17299824340705624213587895)
        ·
          refine ⟨25949736511058436320381843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17299824340705624213587895 25949736511058436320381843)
          ·
            refine ⟨38924604766587654480572765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25949736511058436320381843 38924604766587654480572765)
            ·
              refine ⟨14596726787470370430214787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38924604766587654480572765 14596726787470370430214787)
              ·
                refine ⟨21895090181205555645322181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14596726787470370430214787 21895090181205555645322181)
                ·
                  refine ⟨4105329408976041683497909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21895090181205555645322181 4105329408976041683497909)
                  ·
                    refine ⟨384874632091503907827929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4105329408976041683497909 384874632091503907827929)
                    ·
                      rfl

theorem cell22_1124311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_1124311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124311 prefixEnd_1124311 := by exact prefixLift 1124311
  have htrace : WordTrace (prefixWord ++ tailWord_1124311) baseStart_1124311 baseEnd_1124311 := by
    simpa [prefixWord, tailWord_1124311, baseEnd_1124311] using wordTrace_append hprefix tailTrace_1124311
  have hstable : (prefixWord ++ tailWord_1124311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124311).length < 2 ^ (prefixWord ++ tailWord_1124311).sum := by decide
  have hdescent : baseEnd_1124311 < baseStart_1124311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124313 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 7]
def baseStart_1124313 : Nat := 118140960795 + 1124313 * 2 ^ 59
def prefixEnd_1124313 : Nat := 4983230072969 + 3 ^ 40 * 1124313 * 2
def baseEnd_1124313 : Nat := 128291772244125523092641

theorem tailTrace_1124313 : CollatzResearch.WordTrace tailWord_1124313 prefixEnd_1124313 128291772244125523092641 := by
  unfold tailWord_1124313
  simp only [CollatzResearch.WordTrace]
  refine ⟨41007063975813493218225593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27338042650542328812150395 41007063975813493218225593)
  ·
    refine ⟨30755297981860119913669195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41007063975813493218225593 30755297981860119913669195)
    ·
      refine ⟨46132946972790179870503793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30755297981860119913669195 46132946972790179870503793)
      ·
        refine ⟨34599710229592634902877845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46132946972790179870503793 34599710229592634902877845)
        ·
          refine ⟨1621861417012154761072399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34599710229592634902877845 1621861417012154761072399)
          ·
            refine ⟨2432792125518232141608599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621861417012154761072399 2432792125518232141608599)
            ·
              refine ⟨3649188188277348212412899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2432792125518232141608599 3649188188277348212412899)
              ·
                refine ⟨5473782282416022318619349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3649188188277348212412899 5473782282416022318619349)
                ·
                  refine ⟨128291772244125523092641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5473782282416022318619349 128291772244125523092641)
                  ·
                    rfl

theorem cell22_1124313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 7].length) (baseStart_1124313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124313 prefixEnd_1124313 := by exact prefixLift 1124313
  have htrace : WordTrace (prefixWord ++ tailWord_1124313) baseStart_1124313 baseEnd_1124313 := by
    simpa [prefixWord, tailWord_1124313, baseEnd_1124313] using wordTrace_append hprefix tailTrace_1124313
  have hstable : (prefixWord ++ tailWord_1124313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124313).length < 2 ^ (prefixWord ++ tailWord_1124313).sum := by decide
  have hdescent : baseEnd_1124313 < baseStart_1124313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124317 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_1124317 : Nat := 118140960795 + 1124317 * 2 ^ 59
def prefixEnd_1124317 : Nat := 4983230072969 + 3 ^ 40 * 1124317 * 2
def baseEnd_1124317 : Nat := 384876686014121892177911

theorem tailTrace_1124317 : CollatzResearch.WordTrace tailWord_1124317 prefixEnd_1124317 384876686014121892177911 := by
  unfold tailWord_1124317
  simp only [CollatzResearch.WordTrace]
  refine ⟨41007209867799001901371205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27338139911866001267580803 41007209867799001901371205)
  ·
    refine ⟨7688851850212312856507101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41007209867799001901371205 7688851850212312856507101)
    ·
      refine ⟨2883319443829617321190163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7688851850212312856507101 2883319443829617321190163)
      ·
        refine ⟨4324979165744425981785245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2883319443829617321190163 4324979165744425981785245)
        ·
          refine ⟨1621867187154159743169467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4324979165744425981785245 1621867187154159743169467)
          ·
            refine ⟨2432800780731239614754201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621867187154159743169467 2432800780731239614754201)
            ·
              refine ⟨1824600585548429711065651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2432800780731239614754201 1824600585548429711065651)
              ·
                refine ⟨2736900878322644566598477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1824600585548429711065651 2736900878322644566598477)
                ·
                  refine ⟨1026337829370991712474429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2736900878322644566598477 1026337829370991712474429)
                  ·
                    refine ⟨384876686014121892177911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1026337829370991712474429 384876686014121892177911)
                    ·
                      rfl

theorem cell22_1124317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_1124317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124317 prefixEnd_1124317 := by exact prefixLift 1124317
  have htrace : WordTrace (prefixWord ++ tailWord_1124317) baseStart_1124317 baseEnd_1124317 := by
    simpa [prefixWord, tailWord_1124317, baseEnd_1124317] using wordTrace_append hprefix tailTrace_1124317
  have hstable : (prefixWord ++ tailWord_1124317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124317).length < 2 ^ (prefixWord ++ tailWord_1124317).sum := by decide
  have hdescent : baseEnd_1124317 < baseStart_1124317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124330 : List Nat := [3, 1, 3, 1, 2, 1, 5, 1, 5]
def baseStart_1124330 : Nat := 118140960795 + 1124330 * 2 ^ 59
def prefixEnd_1124330 : Nat := 4983230072969 + 3 ^ 40 * 1124330 * 2
def baseEnd_1124330 : Nat := 128293712059931397200957

theorem tailTrace_1124330 : CollatzResearch.WordTrace tailWord_1124330 prefixEnd_1124330 128293712059931397200957 := by
  unfold tailWord_1124330
  simp only [CollatzResearch.WordTrace]
  refine ⟨10251921004187976280398611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27338456011167936747729629 10251921004187976280398611)
  ·
    refine ⟨15377881506281964420597917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10251921004187976280398611 15377881506281964420597917)
    ·
      refine ⟨5766705564855736657724219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15377881506281964420597917 5766705564855736657724219)
      ·
        refine ⟨8650058347283604986586329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5766705564855736657724219 8650058347283604986586329)
        ·
          refine ⟨6487543760462703739939747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8650058347283604986586329 6487543760462703739939747)
          ·
            refine ⟨9731315640694055609909621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6487543760462703739939747 9731315640694055609909621)
            ·
              refine ⟨912310841315067713429027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9731315640694055609909621 912310841315067713429027)
              ·
                refine ⟨1368466261972601570143541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912310841315067713429027 1368466261972601570143541)
                ·
                  refine ⟨128293712059931397200957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1368466261972601570143541 128293712059931397200957)
                  ·
                    rfl

theorem cell22_1124330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_1124330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124330 prefixEnd_1124330 := by exact prefixLift 1124330
  have htrace : WordTrace (prefixWord ++ tailWord_1124330) baseStart_1124330 baseEnd_1124330 := by
    simpa [prefixWord, tailWord_1124330, baseEnd_1124330] using wordTrace_append hprefix tailTrace_1124330
  have hstable : (prefixWord ++ tailWord_1124330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124330).length < 2 ^ (prefixWord ++ tailWord_1124330).sum := by decide
  have hdescent : baseEnd_1124330 < baseStart_1124330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124422 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1124422 : Nat := 118140960795 + 1124422 * 2 ^ 59
def prefixEnd_1124422 : Nat := 4983230072969 + 3 ^ 40 * 1124422 * 2
def baseEnd_1124422 : Nat := 384912629659936618302589

theorem tailTrace_1124422 : CollatzResearch.WordTrace tailWord_1124422 prefixEnd_1124422 384912629659936618302589 := by
  unfold tailWord_1124422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1281594985388081401060735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27340693021612403222629013 1281594985388081401060735)
  ·
    refine ⟨1922392478082122101591103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1281594985388081401060735 1922392478082122101591103)
    ·
      refine ⟨2883588717123183152386655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1922392478082122101591103 2883588717123183152386655)
      ·
        refine ⟨4325383075684774728579983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2883588717123183152386655 4325383075684774728579983)
        ·
          refine ⟨6488074613527162092869975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4325383075684774728579983 6488074613527162092869975)
          ·
            refine ⟨9732111920290743139304963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6488074613527162092869975 9732111920290743139304963)
            ·
              refine ⟨14598167880436114708957445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9732111920290743139304963 14598167880436114708957445)
              ·
                refine ⟨2737156477581771507929521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14598167880436114708957445 2737156477581771507929521)
                ·
                  refine ⟨2052867358186328630947141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2737156477581771507929521 2052867358186328630947141)
                  ·
                    refine ⟨384912629659936618302589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2052867358186328630947141 384912629659936618302589)
                    ·
                      rfl

theorem cell22_1124422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1124422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124422 prefixEnd_1124422 := by exact prefixLift 1124422
  have htrace : WordTrace (prefixWord ++ tailWord_1124422) baseStart_1124422 baseEnd_1124422 := by
    simpa [prefixWord, tailWord_1124422, baseEnd_1124422] using wordTrace_append hprefix tailTrace_1124422
  have hstable : (prefixWord ++ tailWord_1124422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124422).length < 2 ^ (prefixWord ++ tailWord_1124422).sum := by decide
  have hdescent : baseEnd_1124422 < baseStart_1124422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124512 : List Nat := [2, 1, 1, 4, 2, 3, 2, 2, 1, 4]
def baseStart_1124512 : Nat := 118140960795 + 1124512 * 2 ^ 59
def prefixEnd_1124512 : Nat := 4983230072969 + 3 ^ 40 * 1124512 * 2
def baseEnd_1124512 : Nat := 384943438499206383552313

theorem tailTrace_1124512 : CollatzResearch.WordTrace tailWord_1124512 prefixEnd_1124512 384943438499206383552313 := by
  unfold tailWord_1124512
  simp only [CollatzResearch.WordTrace]
  refine ⟨20507161051046275102359895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27342881401395033469813193 20507161051046275102359895)
  ·
    refine ⟨30760741576569412653539843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20507161051046275102359895 30760741576569412653539843)
    ·
      refine ⟨46141112364854118980309765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30760741576569412653539843 46141112364854118980309765)
      ·
        refine ⟨8651458568410147308808081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46141112364854118980309765 8651458568410147308808081)
        ·
          refine ⟨6488593926307610481606061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8651458568410147308808081 6488593926307610481606061)
          ·
            refine ⟨2433222722365353930602273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6488593926307610481606061 2433222722365353930602273)
            ·
              refine ⟨1824917041774015447951705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2433222722365353930602273 1824917041774015447951705)
              ·
                refine ⟨1368687781330511585963779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1824917041774015447951705 1368687781330511585963779)
                ·
                  refine ⟨2053031671995767378945669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1368687781330511585963779 2053031671995767378945669)
                  ·
                    refine ⟨384943438499206383552313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2053031671995767378945669 384943438499206383552313)
                    ·
                      rfl

theorem cell22_1124512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_1124512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124512 prefixEnd_1124512 := by exact prefixLift 1124512
  have htrace : WordTrace (prefixWord ++ tailWord_1124512) baseStart_1124512 baseEnd_1124512 := by
    simpa [prefixWord, tailWord_1124512, baseEnd_1124512] using wordTrace_append hprefix tailTrace_1124512
  have hstable : (prefixWord ++ tailWord_1124512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124512).length < 2 ^ (prefixWord ++ tailWord_1124512).sum := by decide
  have hdescent : baseEnd_1124512 < baseStart_1124512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124538 : List Nat := [3, 1, 1, 1, 2, 2, 12]
def baseStart_1124538 : Nat := 118140960795 + 1124538 * 2 ^ 59
def prefixEnd_1124538 : Nat := 4983230072969 + 3 ^ 40 * 1124538 * 2
def baseEnd_1124538 : Nat := 14257494030761147496379

theorem tailTrace_1124538 : CollatzResearch.WordTrace tailWord_1124538 prefixEnd_1124538 14257494030761147496379 := by
  unfold tailWord_1124538
  simp only [CollatzResearch.WordTrace]
  refine ⟨10253817599999589161291567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27343513599998904430110845 10253817599999589161291567)
  ·
    refine ⟨15380726399999383741937351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10253817599999589161291567 15380726399999383741937351)
    ·
      refine ⟨23071089599999075612906027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15380726399999383741937351 23071089599999075612906027)
      ·
        refine ⟨34606634399998613419359041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23071089599999075612906027 34606634399998613419359041)
        ·
          refine ⟨25954975799998960064519281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34606634399998613419359041 25954975799998960064519281)
          ·
            refine ⟨19466231849999220048389461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25954975799998960064519281 19466231849999220048389461)
            ·
              refine ⟨14257494030761147496379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 19466231849999220048389461 14257494030761147496379)
              ·
                rfl

theorem cell22_1124538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 12].length) (baseStart_1124538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124538 prefixEnd_1124538 := by exact prefixLift 1124538
  have htrace : WordTrace (prefixWord ++ tailWord_1124538) baseStart_1124538 baseEnd_1124538 := by
    simpa [prefixWord, tailWord_1124538, baseEnd_1124538] using wordTrace_append hprefix tailTrace_1124538
  have hstable : (prefixWord ++ tailWord_1124538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124538).length < 2 ^ (prefixWord ++ tailWord_1124538).sum := by decide
  have hdescent : baseEnd_1124538 < baseStart_1124538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124544 : List Nat := [2, 1, 1, 2, 5, 2, 3, 2, 4]
def baseStart_1124544 : Nat := 118140960795 + 1124544 * 2 ^ 59
def prefixEnd_1124544 : Nat := 4983230072969 + 3 ^ 40 * 1124544 * 2
def baseEnd_1124544 : Nat := 128318130917722988917405

theorem tailTrace_1124544 : CollatzResearch.WordTrace tailWord_1124544 prefixEnd_1124544 128318130917722988917405 := by
  unfold tailWord_1124544
  simp only [CollatzResearch.WordTrace]
  refine ⟨20507744618988309834942343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27343659491984413113256457 20507744618988309834942343)
  ·
    refine ⟨30761616928482464752413515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20507744618988309834942343 30761616928482464752413515)
    ·
      refine ⟨46142425392723697128620273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30761616928482464752413515 46142425392723697128620273)
      ·
        refine ⟨34606819044542772846465205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46142425392723697128620273 34606819044542772846465205)
        ·
          refine ⟨3244389285425884954356113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34606819044542772846465205 3244389285425884954356113)
          ·
            refine ⟨2433291964069413715767085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3244389285425884954356113 2433291964069413715767085)
            ·
              refine ⟨912484486526030143412657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2433291964069413715767085 912484486526030143412657)
              ·
                refine ⟨684363364894522607559493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 912484486526030143412657 684363364894522607559493)
                ·
                  refine ⟨128318130917722988917405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 684363364894522607559493 128318130917722988917405)
                  ·
                    rfl

theorem cell22_1124544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 4].length) (baseStart_1124544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124544 prefixEnd_1124544 := by exact prefixLift 1124544
  have htrace : WordTrace (prefixWord ++ tailWord_1124544) baseStart_1124544 baseEnd_1124544 := by
    simpa [prefixWord, tailWord_1124544, baseEnd_1124544] using wordTrace_append hprefix tailTrace_1124544
  have hstable : (prefixWord ++ tailWord_1124544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124544).length < 2 ^ (prefixWord ++ tailWord_1124544).sum := by decide
  have hdescent : baseEnd_1124544 < baseStart_1124544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124553 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 2, 7]
def baseStart_1124553 : Nat := 118140960795 + 1124553 * 2 ^ 59
def prefixEnd_1124553 : Nat := 4983230072969 + 3 ^ 40 * 1124553 * 2
def baseEnd_1124553 : Nat := 384957473637095943277187

theorem tailTrace_1124553 : CollatzResearch.WordTrace tailWord_1124553 prefixEnd_1124553 384957473637095943277187 := by
  unfold tailWord_1124553
  simp only [CollatzResearch.WordTrace]
  refine ⟨41015817494944014206962313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27343878329962676137974875 41015817494944014206962313)
  ·
    refine ⟨30761863121208010655221735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41015817494944014206962313 30761863121208010655221735)
    ·
      refine ⟨46142794681812015982832603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30761863121208010655221735 46142794681812015982832603)
      ·
        refine ⟨69214192022718023974248905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46142794681812015982832603 69214192022718023974248905)
        ·
          refine ⟨51910644017038517980686679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69214192022718023974248905 51910644017038517980686679)
          ·
            refine ⟨77865966025557776971030019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51910644017038517980686679 77865966025557776971030019)
            ·
              refine ⟨116798949038336665456545029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77865966025557776971030019 116798949038336665456545029)
              ·
                refine ⟨21899802944688124773102193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116798949038336665456545029 21899802944688124773102193)
                ·
                  refine ⟨16424852208516093579826645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21899802944688124773102193 16424852208516093579826645)
                  ·
                    refine ⟨384957473637095943277187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16424852208516093579826645 384957473637095943277187)
                    ·
                      rfl

theorem cell22_1124553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_1124553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124553 prefixEnd_1124553 := by exact prefixLift 1124553
  have htrace : WordTrace (prefixWord ++ tailWord_1124553) baseStart_1124553 baseEnd_1124553 := by
    simpa [prefixWord, tailWord_1124553, baseEnd_1124553] using wordTrace_append hprefix tailTrace_1124553
  have hstable : (prefixWord ++ tailWord_1124553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124553).length < 2 ^ (prefixWord ++ tailWord_1124553).sum := by decide
  have hdescent : baseEnd_1124553 < baseStart_1124553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124638 : List Nat := [4, 3, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1124638 : Nat := 118140960795 + 1124638 * 2 ^ 59
def prefixEnd_1124638 : Nat := 4983230072969 + 3 ^ 40 * 1124638 * 2
def baseEnd_1124638 : Nat := 384986570874184054901927

theorem tailTrace_1124638 : CollatzResearch.WordTrace tailWord_1124638 prefixEnd_1124638 384986570874184054901927 := by
  unfold tailWord_1124638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5127364712454509215475821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27345945133090715815871045 5127364712454509215475821)
  ·
    refine ⟨1922761767170440955803433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5127364712454509215475821 1922761767170440955803433)
    ·
      refine ⟨1442071325377830716852575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1922761767170440955803433 1442071325377830716852575)
      ·
        refine ⟨2163106988066746075278863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1442071325377830716852575 2163106988066746075278863)
        ·
          refine ⟨3244660482100119112918295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163106988066746075278863 3244660482100119112918295)
          ·
            refine ⟨4866990723150178669377443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3244660482100119112918295 4866990723150178669377443)
            ·
              refine ⟨7300486084725268004066165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4866990723150178669377443 7300486084725268004066165)
              ·
                refine ⟨684420570442993875381203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7300486084725268004066165 684420570442993875381203)
                ·
                  refine ⟨1026630855664490813071805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 684420570442993875381203 1026630855664490813071805)
                  ·
                    refine ⟨384986570874184054901927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1026630855664490813071805 384986570874184054901927)
                    ·
                      rfl

theorem cell22_1124638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1124638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124638 prefixEnd_1124638 := by exact prefixLift 1124638
  have htrace : WordTrace (prefixWord ++ tailWord_1124638) baseStart_1124638 baseEnd_1124638 := by
    simpa [prefixWord, tailWord_1124638, baseEnd_1124638] using wordTrace_append hprefix tailTrace_1124638
  have hstable : (prefixWord ++ tailWord_1124638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124638).length < 2 ^ (prefixWord ++ tailWord_1124638).sum := by decide
  have hdescent : baseEnd_1124638 < baseStart_1124638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124675 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 1, 6]
def baseStart_1124675 : Nat := 118140960795 + 1124675 * 2 ^ 59
def prefixEnd_1124675 : Nat := 4983230072969 + 3 ^ 40 * 1124675 * 2
def baseEnd_1124675 : Nat := 384999236730328291726813

theorem tailTrace_1124675 : CollatzResearch.WordTrace tailWord_1124675 prefixEnd_1124675 384999236730328291726813 := by
  unfold tailWord_1124675
  simp only [CollatzResearch.WordTrace]
  refine ⟨41020267200502029042903479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27346844800334686028602319 41020267200502029042903479)
  ·
    refine ⟨61530400800753043564355219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41020267200502029042903479 61530400800753043564355219)
    ·
      refine ⟨92295601201129565346532829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61530400800753043564355219 92295601201129565346532829)
      ·
        refine ⟨34610850450423587004949811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92295601201129565346532829 34610850450423587004949811)
        ·
          refine ⟨51916275675635380507424717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34610850450423587004949811 51916275675635380507424717)
          ·
            refine ⟨19468603378363267690284269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51916275675635380507424717 19468603378363267690284269)
            ·
              refine ⟨7300726266886225383856601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19468603378363267690284269 7300726266886225383856601)
              ·
                refine ⟨5475544700164669037892451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7300726266886225383856601 5475544700164669037892451)
                ·
                  refine ⟨8213317050247003556838677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5475544700164669037892451 8213317050247003556838677)
                  ·
                    refine ⟨384999236730328291726813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8213317050247003556838677 384999236730328291726813)
                    ·
                      rfl

theorem cell22_1124675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 6].length) (baseStart_1124675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124675 prefixEnd_1124675 := by exact prefixLift 1124675
  have htrace : WordTrace (prefixWord ++ tailWord_1124675) baseStart_1124675 baseEnd_1124675 := by
    simpa [prefixWord, tailWord_1124675, baseEnd_1124675] using wordTrace_append hprefix tailTrace_1124675
  have hstable : (prefixWord ++ tailWord_1124675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124675).length < 2 ^ (prefixWord ++ tailWord_1124675).sum := by decide
  have hdescent : baseEnd_1124675 < baseStart_1124675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124692 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1124692 : Nat := 118140960795 + 1124692 * 2 ^ 59
def prefixEnd_1124692 : Nat := 4983230072969 + 3 ^ 40 * 1124692 * 2
def baseEnd_1124692 : Nat := 385005056177745914051761

theorem tailTrace_1124692 : CollatzResearch.WordTrace tailWord_1124692 prefixEnd_1124692 385005056177745914051761 := by
  unfold tailWord_1124692
  simp only [CollatzResearch.WordTrace]
  refine ⟨20510443620720220473136165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27347258160960293964181553 20510443620720220473136165)
  ·
    refine ⟨3845708178885041338713031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20510443620720220473136165 3845708178885041338713031)
    ·
      refine ⟨5768562268327562008069547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3845708178885041338713031 5768562268327562008069547)
      ·
        refine ⟨8652843402491343012104321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5768562268327562008069547 8652843402491343012104321)
        ·
          refine ⟨6489632551868507259078241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8652843402491343012104321 6489632551868507259078241)
          ·
            refine ⟨4867224413901380444308681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6489632551868507259078241 4867224413901380444308681)
            ·
              refine ⟨3650418310426035333231511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4867224413901380444308681 3650418310426035333231511)
              ·
                refine ⟨5475627465639052999847267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3650418310426035333231511 5475627465639052999847267)
                ·
                  refine ⟨8213441198458579499770901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5475627465639052999847267 8213441198458579499770901)
                  ·
                    refine ⟨385005056177745914051761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8213441198458579499770901 385005056177745914051761)
                    ·
                      rfl

theorem cell22_1124692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1124692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124692 prefixEnd_1124692 := by exact prefixLift 1124692
  have htrace : WordTrace (prefixWord ++ tailWord_1124692) baseStart_1124692 baseEnd_1124692 := by
    simpa [prefixWord, tailWord_1124692, baseEnd_1124692] using wordTrace_append hprefix tailTrace_1124692
  have hstable : (prefixWord ++ tailWord_1124692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124692).length < 2 ^ (prefixWord ++ tailWord_1124692).sum := by decide
  have hdescent : baseEnd_1124692 < baseStart_1124692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124758 : List Nat := [5, 3, 1, 2, 2, 9]
def baseStart_1124758 : Nat := 118140960795 + 1124758 * 2 ^ 59
def prefixEnd_1124758 : Nat := 4983230072969 + 3 ^ 40 * 1124758 * 2
def baseEnd_1124758 : Nat := 4753427769463502986439

theorem tailTrace_1124758 : CollatzResearch.WordTrace tailWord_1124758 prefixEnd_1124758 4753427769463502986439 := by
  unfold tailWord_1124758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2563955903700083388635933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27348862972800889478783285 2563955903700083388635933)
  ·
    refine ⟨961483463887531270738475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2563955903700083388635933 961483463887531270738475)
    ·
      refine ⟨1442225195831296906107713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 961483463887531270738475 1442225195831296906107713)
      ·
        refine ⟨1081668896873472679580785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1442225195831296906107713 1081668896873472679580785)
        ·
          refine ⟨811251672655104509685589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1081668896873472679580785 811251672655104509685589)
          ·
            refine ⟨4753427769463502986439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 811251672655104509685589 4753427769463502986439)
            ·
              rfl

theorem cell22_1124758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 9].length) (baseStart_1124758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124758 prefixEnd_1124758 := by exact prefixLift 1124758
  have htrace : WordTrace (prefixWord ++ tailWord_1124758) baseStart_1124758 baseEnd_1124758 := by
    simpa [prefixWord, tailWord_1124758, baseEnd_1124758] using wordTrace_append hprefix tailTrace_1124758
  have hstable : (prefixWord ++ tailWord_1124758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124758).length < 2 ^ (prefixWord ++ tailWord_1124758).sum := by decide
  have hdescent : baseEnd_1124758 < baseStart_1124758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124767 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 2, 5]
def baseStart_1124767 : Nat := 118140960795 + 1124767 * 2 ^ 59
def prefixEnd_1124767 : Nat := 4983230072969 + 3 ^ 40 * 1124767 * 2
def baseEnd_1124767 : Nat := 385030730210470718426531

theorem tailTrace_1124767 : CollatzResearch.WordTrace tailWord_1124767 prefixEnd_1124767 385030730210470718426531 := by
  unfold tailWord_1124767
  simp only [CollatzResearch.WordTrace]
  refine ⟨41023622716168728755252555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27349081810779152503501703 41023622716168728755252555)
  ·
    refine ⟨61535434074253093132878833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41023622716168728755252555 61535434074253093132878833)
    ·
      refine ⟨46151575555689819849659125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61535434074253093132878833 46151575555689819849659125)
      ·
        refine ⟨4326710208345920610905543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46151575555689819849659125 4326710208345920610905543)
        ·
          refine ⟨6490065312518880916358315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4326710208345920610905543 6490065312518880916358315)
          ·
            refine ⟨9735097968778321374537473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6490065312518880916358315 9735097968778321374537473)
            ·
              refine ⟨7301323476583741030903105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9735097968778321374537473 7301323476583741030903105)
              ·
                refine ⟨5475992607437805773177329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7301323476583741030903105 5475992607437805773177329)
                ·
                  refine ⟨4106994455578354329882997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5475992607437805773177329 4106994455578354329882997)
                  ·
                    refine ⟨385030730210470718426531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4106994455578354329882997 385030730210470718426531)
                    ·
                      rfl

theorem cell22_1124767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_1124767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124767 prefixEnd_1124767 := by exact prefixLift 1124767
  have htrace : WordTrace (prefixWord ++ tailWord_1124767) baseStart_1124767 baseEnd_1124767 := by
    simpa [prefixWord, tailWord_1124767, baseEnd_1124767] using wordTrace_append hprefix tailTrace_1124767
  have hstable : (prefixWord ++ tailWord_1124767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124767).length < 2 ^ (prefixWord ++ tailWord_1124767).sum := by decide
  have hdescent : baseEnd_1124767 < baseStart_1124767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124797 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 8]
def baseStart_1124797 : Nat := 118140960795 + 1124797 * 2 ^ 59
def prefixEnd_1124797 : Nat := 4983230072969 + 3 ^ 40 * 1124797 * 2
def baseEnd_1124797 : Nat := 128346999941186880058813

theorem tailTrace_1124797 : CollatzResearch.WordTrace tailWord_1124797 prefixEnd_1124797 128346999941186880058813 := by
  unfold tailWord_1124797
  simp only [CollatzResearch.WordTrace]
  refine ⟨41024716906060043878844645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27349811270706695919229763 41024716906060043878844645)
  ·
    refine ⟨7692134419886258227283371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41024716906060043878844645 7692134419886258227283371)
    ·
      refine ⟨11538201629829387340925057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7692134419886258227283371 11538201629829387340925057)
      ·
        refine ⟨8653651222372040505693793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11538201629829387340925057 8653651222372040505693793)
        ·
          refine ⟨6490238416779030379270345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8653651222372040505693793 6490238416779030379270345)
          ·
            refine ⟨4867678812584272784452759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6490238416779030379270345 4867678812584272784452759)
            ·
              refine ⟨7301518218876409176679139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4867678812584272784452759 7301518218876409176679139)
              ·
                refine ⟨10952277328314613765018709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7301518218876409176679139 10952277328314613765018709)
                ·
                  refine ⟨128346999941186880058813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10952277328314613765018709 128346999941186880058813)
                  ·
                    rfl

theorem cell22_1124797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_1124797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124797 prefixEnd_1124797 := by exact prefixLift 1124797
  have htrace : WordTrace (prefixWord ++ tailWord_1124797) baseStart_1124797 baseEnd_1124797 := by
    simpa [prefixWord, tailWord_1124797, baseEnd_1124797] using wordTrace_append hprefix tailTrace_1124797
  have hstable : (prefixWord ++ tailWord_1124797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124797).length < 2 ^ (prefixWord ++ tailWord_1124797).sum := by decide
  have hdescent : baseEnd_1124797 < baseStart_1124797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124846 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_1124846 : Nat := 118140960795 + 1124846 * 2 ^ 59
def prefixEnd_1124846 : Nat := 4983230072969 + 3 ^ 40 * 1124846 * 2
def baseEnd_1124846 : Nat := 385057773524940845701289

theorem tailTrace_1124846 : CollatzResearch.WordTrace tailWord_1124846 prefixEnd_1124846 385057773524940845701289 := by
  unfold tailWord_1124846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5128313010360315655922299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27351002721921683498252261 5128313010360315655922299)
  ·
    refine ⟨7692469515540473483883449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5128313010360315655922299 7692469515540473483883449)
    ·
      refine ⟨5769352136655355112912587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7692469515540473483883449 5769352136655355112912587)
      ·
        refine ⟨8654028204983032669368881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5769352136655355112912587 8654028204983032669368881)
        ·
          refine ⟨6490521153737274502026661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8654028204983032669368881 6490521153737274502026661)
          ·
            refine ⟨1216972716325738969129999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6490521153737274502026661 1216972716325738969129999)
            ·
              refine ⟨1825459074488608453694999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1216972716325738969129999 1825459074488608453694999)
              ·
                refine ⟨2738188611732912680542499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825459074488608453694999 2738188611732912680542499)
                ·
                  refine ⟨4107282917599369020813749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2738188611732912680542499 4107282917599369020813749)
                  ·
                    refine ⟨385057773524940845701289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4107282917599369020813749 385057773524940845701289)
                    ·
                      rfl

theorem cell22_1124846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_1124846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124846 prefixEnd_1124846 := by exact prefixLift 1124846
  have htrace : WordTrace (prefixWord ++ tailWord_1124846) baseStart_1124846 baseEnd_1124846 := by
    simpa [prefixWord, tailWord_1124846, baseEnd_1124846] using wordTrace_append hprefix tailTrace_1124846
  have hstable : (prefixWord ++ tailWord_1124846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124846).length < 2 ^ (prefixWord ++ tailWord_1124846).sum := by decide
  have hdescent : baseEnd_1124846 < baseStart_1124846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124872 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 1, 8]
def baseStart_1124872 : Nat := 118140960795 + 1124872 * 2 ^ 59
def prefixEnd_1124872 : Nat := 4983230072969 + 3 ^ 40 * 1124872 * 2
def baseEnd_1124872 : Nat := 385066673856285444551209

theorem tailTrace_1124872 : CollatzResearch.WordTrace tailWord_1124872 prefixEnd_1124872 385066673856285444551209 := by
  unfold tailWord_1124872
  simp only [CollatzResearch.WordTrace]
  refine ⟨20513726190394165843912435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27351634920525554458549913 20513726190394165843912435)
  ·
    refine ⟨30770589285591248765868653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20513726190394165843912435 30770589285591248765868653)
    ·
      refine ⟨11538970982096718287200745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30770589285591248765868653 11538970982096718287200745)
      ·
        refine ⟨8654228236572538715400559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11538970982096718287200745 8654228236572538715400559)
        ·
          refine ⟨12981342354858808073100839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8654228236572538715400559 12981342354858808073100839)
          ·
            refine ⟨19472013532288212109651259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12981342354858808073100839 19472013532288212109651259)
            ·
              refine ⟨29208020298432318164476889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19472013532288212109651259 29208020298432318164476889)
              ·
                refine ⟨21906015223824238623357667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29208020298432318164476889 21906015223824238623357667)
                ·
                  refine ⟨32859022835736357935036501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21906015223824238623357667 32859022835736357935036501)
                  ·
                    refine ⟨385066673856285444551209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32859022835736357935036501 385066673856285444551209)
                    ·
                      rfl

theorem cell22_1124872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_1124872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124872 prefixEnd_1124872 := by exact prefixLift 1124872
  have htrace : WordTrace (prefixWord ++ tailWord_1124872) baseStart_1124872 baseEnd_1124872 := by
    simpa [prefixWord, tailWord_1124872, baseEnd_1124872] using wordTrace_append hprefix tailTrace_1124872
  have hstable : (prefixWord ++ tailWord_1124872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124872).length < 2 ^ (prefixWord ++ tailWord_1124872).sum := by decide
  have hdescent : baseEnd_1124872 < baseStart_1124872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124947 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 1, 11]
def baseStart_1124947 : Nat := 118140960795 + 1124947 * 2 ^ 59
def prefixEnd_1124947 : Nat := 4983230072969 + 3 ^ 40 * 1124947 * 2
def baseEnd_1124947 : Nat := 385092347889010248925979

theorem tailTrace_1124947 : CollatzResearch.WordTrace tailWord_1124947 prefixEnd_1124947 385092347889010248925979 := by
  unfold tailWord_1124947
  simp only [CollatzResearch.WordTrace]
  refine ⟨41030187855516619496805095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27353458570344412997870063 41030187855516619496805095)
  ·
    refine ⟨61545281783274929245207643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41030187855516619496805095 61545281783274929245207643)
    ·
      refine ⟨92317922674912393867811465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61545281783274929245207643 92317922674912393867811465)
      ·
        refine ⟨69238442006184295400858599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92317922674912393867811465 69238442006184295400858599)
        ·
          refine ⟨103857663009276443101287899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69238442006184295400858599 103857663009276443101287899)
          ·
            refine ⟨155786494513914664651931849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103857663009276443101287899 155786494513914664651931849)
            ·
              refine ⟨116839870885435998488948887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155786494513914664651931849 116839870885435998488948887)
              ·
                refine ⟨175259806328153997733423331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116839870885435998488948887 175259806328153997733423331)
                ·
                  refine ⟨262889709492230996600134997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 175259806328153997733423331 262889709492230996600134997)
                  ·
                    refine ⟨385092347889010248925979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 262889709492230996600134997 385092347889010248925979)
                    ·
                      rfl

theorem cell22_1124947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_1124947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124947 prefixEnd_1124947 := by exact prefixLift 1124947
  have htrace : WordTrace (prefixWord ++ tailWord_1124947) baseStart_1124947 baseEnd_1124947 := by
    simpa [prefixWord, tailWord_1124947, baseEnd_1124947] using wordTrace_append hprefix tailTrace_1124947
  have hstable : (prefixWord ++ tailWord_1124947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124947).length < 2 ^ (prefixWord ++ tailWord_1124947).sum := by decide
  have hdescent : baseEnd_1124947 < baseStart_1124947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1124979 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 2, 4]
def baseStart_1124979 : Nat := 118140960795 + 1124979 * 2 ^ 59
def prefixEnd_1124979 : Nat := 4983230072969 + 3 ^ 40 * 1124979 * 2
def baseEnd_1124979 : Nat := 385103302142972832125881

theorem tailTrace_1124979 : CollatzResearch.WordTrace tailWord_1124979 prefixEnd_1124979 385103302142972832125881 := by
  unfold tailWord_1124979
  simp only [CollatzResearch.WordTrace]
  refine ⟨41031354991400688961969991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27354236660933792641313327 41031354991400688961969991)
  ·
    refine ⟨61547032487101033442954987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41031354991400688961969991 61547032487101033442954987)
    ·
      refine ⟨92320548730651550164432481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61547032487101033442954987 92320548730651550164432481)
      ·
        refine ⟨69240411547988662623324361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92320548730651550164432481 69240411547988662623324361)
        ·
          refine ⟨51930308660991496967493271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69240411547988662623324361 51930308660991496967493271)
          ·
            refine ⟨77895462991487245451239907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51930308660991496967493271 77895462991487245451239907)
            ·
              refine ⟨116843194487230868176859861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77895462991487245451239907 116843194487230868176859861)
              ·
                refine ⟨2738512370794473472895153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 116843194487230868176859861 2738512370794473472895153)
                ·
                  refine ⟨2053884278095855104671365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2738512370794473472895153 2053884278095855104671365)
                  ·
                    refine ⟨385103302142972832125881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2053884278095855104671365 385103302142972832125881)
                    ·
                      rfl

theorem cell22_1124979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 4].length) (baseStart_1124979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1124979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1124979 prefixEnd_1124979 := by exact prefixLift 1124979
  have htrace : WordTrace (prefixWord ++ tailWord_1124979) baseStart_1124979 baseEnd_1124979 := by
    simpa [prefixWord, tailWord_1124979, baseEnd_1124979] using wordTrace_append hprefix tailTrace_1124979
  have hstable : (prefixWord ++ tailWord_1124979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1124979).length < 2 ^ (prefixWord ++ tailWord_1124979).sum := by decide
  have hdescent : baseEnd_1124979 < baseStart_1124979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1124979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125034 : List Nat := [3, 1, 5, 2, 2, 1, 1, 3, 4]
def baseStart_1125034 : Nat := 118140960795 + 1125034 * 2 ^ 59
def prefixEnd_1125034 : Nat := 4983230072969 + 3 ^ 40 * 1125034 * 2
def baseEnd_1125034 : Nat := 128374043255657007333571

theorem tailTrace_1125034 : CollatzResearch.WordTrace tailWord_1125034 prefixEnd_1125034 128374043255657007333571 := by
  unfold tailWord_1125034
  simp only [CollatzResearch.WordTrace]
  refine ⟨10258340251550358338805539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27355574004134288903481437 10258340251550358338805539)
  ·
    refine ⟨15387510377325537508208309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10258340251550358338805539 15387510377325537508208309)
    ·
      refine ⟨1442579097874269141394529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15387510377325537508208309 1442579097874269141394529)
      ·
        refine ⟨1081934323405701856045897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1442579097874269141394529 1081934323405701856045897)
        ·
          refine ⟨811450742554276392034423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1081934323405701856045897 811450742554276392034423)
          ·
            refine ⟨1217176113831414588051635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811450742554276392034423 1217176113831414588051635)
            ·
              refine ⟨1825764170747121882077453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217176113831414588051635 1825764170747121882077453)
              ·
                refine ⟨684661564030170705779045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1825764170747121882077453 684661564030170705779045)
                ·
                  refine ⟨128374043255657007333571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 684661564030170705779045 128374043255657007333571)
                  ·
                    rfl

theorem cell22_1125034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_1125034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125034 prefixEnd_1125034 := by exact prefixLift 1125034
  have htrace : WordTrace (prefixWord ++ tailWord_1125034) baseStart_1125034 baseEnd_1125034 := by
    simpa [prefixWord, tailWord_1125034, baseEnd_1125034] using wordTrace_append hprefix tailTrace_1125034
  have hstable : (prefixWord ++ tailWord_1125034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125034).length < 2 ^ (prefixWord ++ tailWord_1125034).sum := by decide
  have hdescent : baseEnd_1125034 < baseStart_1125034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125039 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 7]
def baseStart_1125039 : Nat := 118140960795 + 1125039 * 2 ^ 59
def prefixEnd_1125039 : Nat := 4983230072969 + 3 ^ 40 * 1125039 * 2
def baseEnd_1125039 : Nat := 128374613789717558541899

theorem tailTrace_1125039 : CollatzResearch.WordTrace tailWord_1125039 prefixEnd_1125039 128374613789717558541899 := by
  unfold tailWord_1125039
  simp only [CollatzResearch.WordTrace]
  refine ⟨41033543371183319209154171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27355695580788879472769447 41033543371183319209154171)
  ·
    refine ⟨61550315056774978813731257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41033543371183319209154171 61550315056774978813731257)
    ·
      refine ⟨46162736292581234110298443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61550315056774978813731257 46162736292581234110298443)
      ·
        refine ⟨69244104438871851165447665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46162736292581234110298443 69244104438871851165447665)
        ·
          refine ⟨51933078329153888374085749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69244104438871851165447665 51933078329153888374085749)
          ·
            refine ⟨4868726093358177035070539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51933078329153888374085749 4868726093358177035070539)
            ·
              refine ⟨7303089140037265552605809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4868726093358177035070539 7303089140037265552605809)
              ·
                refine ⟨5477316855027949164454357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7303089140037265552605809 5477316855027949164454357)
                ·
                  refine ⟨128374613789717558541899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5477316855027949164454357 128374613789717558541899)
                  ·
                    rfl

theorem cell22_1125039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 7].length) (baseStart_1125039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125039 prefixEnd_1125039 := by exact prefixLift 1125039
  have htrace : WordTrace (prefixWord ++ tailWord_1125039) baseStart_1125039 baseEnd_1125039 := by
    simpa [prefixWord, tailWord_1125039, baseEnd_1125039] using wordTrace_append hprefix tailTrace_1125039
  have hstable : (prefixWord ++ tailWord_1125039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125039).length < 2 ^ (prefixWord ++ tailWord_1125039).sum := by decide
  have hdescent : baseEnd_1125039 < baseStart_1125039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125060 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_1125060 : Nat := 118140960795 + 1125060 * 2 ^ 59
def prefixEnd_1125060 : Nat := 4983230072969 + 3 ^ 40 * 1125060 * 2
def baseEnd_1125060 : Nat := 385131030098315620850633

theorem tailTrace_1125060 : CollatzResearch.WordTrace tailWord_1125060 prefixEnd_1125060 385131030098315620850633 := by
  unfold tailWord_1125060
  simp only [CollatzResearch.WordTrace]
  refine ⟨20517154652053619897834317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27356206202738159863779089 20517154652053619897834317)
  ·
    refine ⟨7693932994520107461687869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20517154652053619897834317 7693932994520107461687869)
    ·
      refine ⟨2885224872945040298132951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7693932994520107461687869 2885224872945040298132951)
      ·
        refine ⟨4327837309417560447199427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2885224872945040298132951 4327837309417560447199427)
        ·
          refine ⟨6491755964126340670799141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4327837309417560447199427 6491755964126340670799141)
          ·
            refine ⟨1217204243273688875774839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6491755964126340670799141 1217204243273688875774839)
            ·
              refine ⟨1825806364910533313662259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1217204243273688875774839 1825806364910533313662259)
              ·
                refine ⟨2738709547365799970493389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825806364910533313662259 2738709547365799970493389)
                ·
                  refine ⟨1027016080262174988935021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2738709547365799970493389 1027016080262174988935021)
                  ·
                    refine ⟨385131030098315620850633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1027016080262174988935021 385131030098315620850633)
                    ·
                      rfl

theorem cell22_1125060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_1125060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125060 prefixEnd_1125060 := by exact prefixLift 1125060
  have htrace : WordTrace (prefixWord ++ tailWord_1125060) baseStart_1125060 baseEnd_1125060 := by
    simpa [prefixWord, tailWord_1125060, baseEnd_1125060] using wordTrace_append hprefix tailTrace_1125060
  have hstable : (prefixWord ++ tailWord_1125060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125060).length < 2 ^ (prefixWord ++ tailWord_1125060).sum := by decide
  have hdescent : baseEnd_1125060 < baseStart_1125060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125148 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 2, 4]
def baseStart_1125148 : Nat := 118140960795 + 1125148 * 2 ^ 59
def prefixEnd_1125148 : Nat := 4983230072969 + 3 ^ 40 * 1125148 * 2
def baseEnd_1125148 : Nat := 385161154296712724650363

theorem tailTrace_1125148 : CollatzResearch.WordTrace tailWord_1125148 prefixEnd_1125148 385161154296712724650363 := by
  unfold tailWord_1125148
  simp only [CollatzResearch.WordTrace]
  refine ⟨20518759463894215412436049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27358345951858953883248065 20518759463894215412436049)
  ·
    refine ⟨15389069597920661559327037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20518759463894215412436049 15389069597920661559327037)
    ·
      refine ⟨5770901099220248084747639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15389069597920661559327037 5770901099220248084747639)
      ·
        refine ⟨8656351648830372127121459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5770901099220248084747639 8656351648830372127121459)
        ·
          refine ⟨12984527473245558190682189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8656351648830372127121459 12984527473245558190682189)
          ·
            refine ⟨4869197802467084321505821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12984527473245558190682189 4869197802467084321505821)
            ·
              refine ⟨1825949175925156620564683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4869197802467084321505821 1825949175925156620564683)
              ·
                refine ⟨2738923763887734930847025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1825949175925156620564683 2738923763887734930847025)
                ·
                  refine ⟨2054192822915801198135269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2738923763887734930847025 2054192822915801198135269)
                  ·
                    refine ⟨385161154296712724650363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2054192822915801198135269 385161154296712724650363)
                    ·
                      rfl

theorem cell22_1125148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_1125148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125148 prefixEnd_1125148 := by exact prefixLift 1125148
  have htrace : WordTrace (prefixWord ++ tailWord_1125148) baseStart_1125148 baseEnd_1125148 := by
    simpa [prefixWord, tailWord_1125148, baseEnd_1125148] using wordTrace_append hprefix tailTrace_1125148
  have hstable : (prefixWord ++ tailWord_1125148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125148).length < 2 ^ (prefixWord ++ tailWord_1125148).sum := by decide
  have hdescent : baseEnd_1125148 < baseStart_1125148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125197 : List Nat := [1, 6, 1, 2, 2, 2, 2, 6]
def baseStart_1125197 : Nat := 118140960795 + 1125197 * 2 ^ 59
def prefixEnd_1125197 : Nat := 4983230072969 + 3 ^ 40 * 1125197 * 2
def baseEnd_1125197 : Nat := 42797547555343658908357

theorem tailTrace_1125197 : CollatzResearch.WordTrace tailWord_1125197 prefixEnd_1125197 42797547555343658908357 := by
  unfold tailWord_1125197
  simp only [CollatzResearch.WordTrace]
  refine ⟨41039306104610912193405845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27359537403073941462270563 41039306104610912193405845)
  ·
    refine ⟨1923717473653636509065899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41039306104610912193405845 1923717473653636509065899)
    ·
      refine ⟨2885576210480454763598849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1923717473653636509065899 2885576210480454763598849)
      ·
        refine ⟨2164182157860341072699137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2885576210480454763598849 2164182157860341072699137)
        ·
          refine ⟨1623136618395255804524353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2164182157860341072699137 1623136618395255804524353)
          ·
            refine ⟨1217352463796441853393265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1623136618395255804524353 1217352463796441853393265)
            ·
              refine ⟨913014347847331390044949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1217352463796441853393265 913014347847331390044949)
              ·
                refine ⟨42797547555343658908357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 913014347847331390044949 42797547555343658908357)
                ·
                  rfl

theorem cell22_1125197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 6].length) (baseStart_1125197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125197 prefixEnd_1125197 := by exact prefixLift 1125197
  have htrace : WordTrace (prefixWord ++ tailWord_1125197) baseStart_1125197 baseEnd_1125197 := by
    simpa [prefixWord, tailWord_1125197, baseEnd_1125197] using wordTrace_append hprefix tailTrace_1125197
  have hstable : (prefixWord ++ tailWord_1125197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125197).length < 2 ^ (prefixWord ++ tailWord_1125197).sum := by decide
  have hdescent : baseEnd_1125197 < baseStart_1125197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125255 : List Nat := [1, 1, 4, 2, 3, 1, 3, 2, 1, 4]
def baseStart_1125255 : Nat := 118140960795 + 1125255 * 2 ^ 59
def prefixEnd_1125255 : Nat := 4983230072969 + 3 ^ 40 * 1125255 * 2
def baseEnd_1125255 : Nat := 385197782583400112225035

theorem tailTrace_1125255 : CollatzResearch.WordTrace tailWord_1125255 prefixEnd_1125255 385197782583400112225035 := by
  unfold tailWord_1125255
  simp only [CollatzResearch.WordTrace]
  refine ⟨41041421538400788099017219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27360947692267192066011479 41041421538400788099017219)
  ·
    refine ⟨61562132307601182148525829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41041421538400788099017219 61562132307601182148525829)
    ·
      refine ⟨11542899807675221652848593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61562132307601182148525829 11542899807675221652848593)
      ·
        refine ⟨8657174855756416239636445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11542899807675221652848593 8657174855756416239636445)
        ·
          refine ⟨3246440570908656089863667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8657174855756416239636445 3246440570908656089863667)
          ·
            refine ⟨4869660856362984134795501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3246440570908656089863667 4869660856362984134795501)
            ·
              refine ⟨1826122821136119050548313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4869660856362984134795501 1826122821136119050548313)
              ·
                refine ⟨1369592115852089287911235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1826122821136119050548313 1369592115852089287911235)
                ·
                  refine ⟨2054388173778133931866853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1369592115852089287911235 2054388173778133931866853)
                  ·
                    refine ⟨385197782583400112225035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2054388173778133931866853 385197782583400112225035)
                    ·
                      rfl

theorem cell22_1125255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_1125255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125255 prefixEnd_1125255 := by exact prefixLift 1125255
  have htrace : WordTrace (prefixWord ++ tailWord_1125255) baseStart_1125255 baseEnd_1125255 := by
    simpa [prefixWord, tailWord_1125255, baseEnd_1125255] using wordTrace_append hprefix tailTrace_1125255
  have hstable : (prefixWord ++ tailWord_1125255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125255).length < 2 ^ (prefixWord ++ tailWord_1125255).sum := by decide
  have hdescent : baseEnd_1125255 < baseStart_1125255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125283 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 2, 4]
def baseStart_1125283 : Nat := 118140960795 + 1125283 * 2 ^ 59
def prefixEnd_1125283 : Nat := 4983230072969 + 3 ^ 40 * 1125283 * 2
def baseEnd_1125283 : Nat := 385207367555617372524949

theorem tailTrace_1125283 : CollatzResearch.WordTrace tailWord_1125283 prefixEnd_1125283 385207367555617372524949 := by
  unfold tailWord_1125283
  simp only [CollatzResearch.WordTrace]
  refine ⟨41042442782299348881036503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27361628521532899254024335 41042442782299348881036503)
  ·
    refine ⟨61563664173449023321554755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41042442782299348881036503 61563664173449023321554755)
    ·
      refine ⟨92345496260173534982332133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61563664173449023321554755 92345496260173534982332133)
      ·
        refine ⟨17314780548782537809187275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92345496260173534982332133 17314780548782537809187275)
        ·
          refine ⟨25972170823173806713780913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17314780548782537809187275 25972170823173806713780913)
          ·
            refine ⟨19479128117380355035335685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25972170823173806713780913 19479128117380355035335685)
            ·
              refine ⟨3652336522008816569125441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19479128117380355035335685 3652336522008816569125441)
              ·
                refine ⟨2739252391506612426844081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3652336522008816569125441 2739252391506612426844081)
                ·
                  refine ⟨2054439293629959320133061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2739252391506612426844081 2054439293629959320133061)
                  ·
                    refine ⟨385207367555617372524949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2054439293629959320133061 385207367555617372524949)
                    ·
                      rfl

theorem cell22_1125283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 4].length) (baseStart_1125283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125283 prefixEnd_1125283 := by exact prefixLift 1125283
  have htrace : WordTrace (prefixWord ++ tailWord_1125283) baseStart_1125283 baseEnd_1125283 := by
    simpa [prefixWord, tailWord_1125283, baseEnd_1125283] using wordTrace_append hprefix tailTrace_1125283
  have hstable : (prefixWord ++ tailWord_1125283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125283).length < 2 ^ (prefixWord ++ tailWord_1125283).sum := by decide
  have hdescent : baseEnd_1125283 < baseStart_1125283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125287 : List Nat := [1, 1, 6, 1, 3, 1, 1, 4, 4]
def baseStart_1125287 : Nat := 118140960795 + 1125287 * 2 ^ 59
def prefixEnd_1125287 : Nat := 4983230072969 + 3 ^ 40 * 1125287 * 2
def baseEnd_1125287 : Nat := 128402912279120898474979

theorem tailTrace_1125287 : CollatzResearch.WordTrace tailWord_1125287 prefixEnd_1125287 128402912279120898474979 := by
  unfold tailWord_1125287
  simp only [CollatzResearch.WordTrace]
  refine ⟨41042588674284857564182115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27361725782856571709454743 41042588674284857564182115)
  ·
    refine ⟨61563883011427286346273173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41042588674284857564182115 61563883011427286346273173)
    ·
      refine ⟨2885807016160654047481555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 61563883011427286346273173 2885807016160654047481555)
      ·
        refine ⟨4328710524240981071222333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2885807016160654047481555 4328710524240981071222333)
        ·
          refine ⟨1623266446590367901708375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4328710524240981071222333 1623266446590367901708375)
          ·
            refine ⟨2434899669885551852562563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1623266446590367901708375 2434899669885551852562563)
            ·
              refine ⟨3652349504828327778843845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2434899669885551852562563 3652349504828327778843845)
              ·
                refine ⟨684815532155311458533221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3652349504828327778843845 684815532155311458533221)
                ·
                  refine ⟨128402912279120898474979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 684815532155311458533221 128402912279120898474979)
                  ·
                    rfl

theorem cell22_1125287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 4].length) (baseStart_1125287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125287 prefixEnd_1125287 := by exact prefixLift 1125287
  have htrace : WordTrace (prefixWord ++ tailWord_1125287) baseStart_1125287 baseEnd_1125287 := by
    simpa [prefixWord, tailWord_1125287, baseEnd_1125287] using wordTrace_append hprefix tailTrace_1125287
  have hstable : (prefixWord ++ tailWord_1125287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125287).length < 2 ^ (prefixWord ++ tailWord_1125287).sum := by decide
  have hdescent : baseEnd_1125287 < baseStart_1125287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125347 : List Nat := [1, 1, 1, 6, 1, 1, 1, 6, 1, 3]
def baseStart_1125347 : Nat := 118140960795 + 1125347 * 2 ^ 59
def prefixEnd_1125347 : Nat := 4983230072969 + 3 ^ 40 * 1125347 * 2
def baseEnd_1125347 : Nat := 385229276063542538924753

theorem tailTrace_1125347 : CollatzResearch.WordTrace tailWord_1125347 prefixEnd_1125347 385229276063542538924753 := by
  unfold tailWord_1125347
  simp only [CollatzResearch.WordTrace]
  refine ⟨41044777054067487811366295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27363184702711658540910863 41044777054067487811366295)
  ·
    refine ⟨61567165581101231717049443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41044777054067487811366295 61567165581101231717049443)
    ·
      refine ⟨92350748371651847575574165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61567165581101231717049443 92350748371651847575574165)
      ·
        refine ⟨4328941329921180355105039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92350748371651847575574165 4328941329921180355105039)
        ·
          refine ⟨6493411994881770532657559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4328941329921180355105039 6493411994881770532657559)
          ·
            refine ⟨9740117992322655798986339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6493411994881770532657559 9740117992322655798986339)
            ·
              refine ⟨14610176988483983698479509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9740117992322655798986339 14610176988483983698479509)
              ·
                refine ⟨684852046335186735866227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14610176988483983698479509 684852046335186735866227)
                ·
                  refine ⟨1027278069502780103799341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 684852046335186735866227 1027278069502780103799341)
                  ·
                    refine ⟨385229276063542538924753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1027278069502780103799341 385229276063542538924753)
                    ·
                      rfl

theorem cell22_1125347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 1, 3].length) (baseStart_1125347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125347 prefixEnd_1125347 := by exact prefixLift 1125347
  have htrace : WordTrace (prefixWord ++ tailWord_1125347) baseStart_1125347 baseEnd_1125347 := by
    simpa [prefixWord, tailWord_1125347, baseEnd_1125347] using wordTrace_append hprefix tailTrace_1125347
  have hstable : (prefixWord ++ tailWord_1125347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125347).length < 2 ^ (prefixWord ++ tailWord_1125347).sum := by decide
  have hdescent : baseEnd_1125347 < baseStart_1125347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125482 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 5, 3]
def baseStart_1125482 : Nat := 118140960795 + 1125482 * 2 ^ 59
def prefixEnd_1125482 : Nat := 4983230072969 + 3 ^ 40 * 1125482 * 2
def baseEnd_1125482 : Nat := 385275489322447186799339

theorem tailTrace_1125482 : CollatzResearch.WordTrace tailWord_1125482 prefixEnd_1125482 385275489322447186799339 := by
  unfold tailWord_1125482
  simp only [CollatzResearch.WordTrace]
  refine ⟨10262425227144601466882675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27366467272385603911687133 10262425227144601466882675)
  ·
    refine ⟨15393637840716902200324013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10262425227144601466882675 15393637840716902200324013)
    ·
      refine ⟨5772614190268838325121505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15393637840716902200324013 5772614190268838325121505)
      ·
        refine ⟨4329460642701628743841129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5772614190268838325121505 4329460642701628743841129)
        ·
          refine ⟨3247095482026221557880847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4329460642701628743841129 3247095482026221557880847)
          ·
            refine ⟨4870643223039332336821271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3247095482026221557880847 4870643223039332336821271)
            ·
              refine ⟨7305964834558998505231907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4870643223039332336821271 7305964834558998505231907)
              ·
                refine ⟨10958947251838497757847861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7305964834558998505231907 10958947251838497757847861)
                ·
                  refine ⟨1027401304859859164798237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10958947251838497757847861 1027401304859859164798237)
                  ·
                    refine ⟨385275489322447186799339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1027401304859859164798237 385275489322447186799339)
                    ·
                      rfl

theorem cell22_1125482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_1125482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125482 prefixEnd_1125482 := by exact prefixLift 1125482
  have htrace : WordTrace (prefixWord ++ tailWord_1125482) baseStart_1125482 baseEnd_1125482 := by
    simpa [prefixWord, tailWord_1125482, baseEnd_1125482] using wordTrace_append hprefix tailTrace_1125482
  have hstable : (prefixWord ++ tailWord_1125482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125482).length < 2 ^ (prefixWord ++ tailWord_1125482).sum := by decide
  have hdescent : baseEnd_1125482 < baseStart_1125482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125512 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 7]
def baseStart_1125512 : Nat := 118140960795 + 1125512 * 2 ^ 59
def prefixEnd_1125512 : Nat := 4983230072969 + 3 ^ 40 * 1125512 * 2
def baseEnd_1125512 : Nat := 128428586311845702849749

theorem tailTrace_1125512 : CollatzResearch.WordTrace tailWord_1125512 prefixEnd_1125512 128428586311845702849749 := by
  unfold tailWord_1125512
  simp only [CollatzResearch.WordTrace]
  refine ⟨20525397549234860495561395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27367196732313147327415193 20525397549234860495561395)
  ·
    refine ⟨30788096323852290743342093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20525397549234860495561395 30788096323852290743342093)
    ·
      refine ⟨11545536121444609028753285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30788096323852290743342093 11545536121444609028753285)
      ·
        refine ⟨2164788022770864192891241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11545536121444609028753285 2164788022770864192891241)
        ·
          refine ⟨1623591017078148144668431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2164788022770864192891241 1623591017078148144668431)
          ·
            refine ⟨2435386525617222217002647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1623591017078148144668431 2435386525617222217002647)
            ·
              refine ⟨3653079788425833325503971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2435386525617222217002647 3653079788425833325503971)
              ·
                refine ⟨5479619682638749988255957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653079788425833325503971 5479619682638749988255957)
                ·
                  refine ⟨128428586311845702849749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5479619682638749988255957 128428586311845702849749)
                  ·
                    rfl

theorem cell22_1125512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 7].length) (baseStart_1125512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125512 prefixEnd_1125512 := by exact prefixLift 1125512
  have htrace : WordTrace (prefixWord ++ tailWord_1125512) baseStart_1125512 baseEnd_1125512 := by
    simpa [prefixWord, tailWord_1125512, baseEnd_1125512] using wordTrace_append hprefix tailTrace_1125512
  have hstable : (prefixWord ++ tailWord_1125512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125512).length < 2 ^ (prefixWord ++ tailWord_1125512).sum := by decide
  have hdescent : baseEnd_1125512 < baseStart_1125512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125525 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_1125525 : Nat := 118140960795 + 1125525 * 2 ^ 59
def prefixEnd_1125525 : Nat := 4983230072969 + 3 ^ 40 * 1125525 * 2
def baseEnd_1125525 : Nat := 385290209101209407974207

theorem tailTrace_1125525 : CollatzResearch.WordTrace tailWord_1125525 prefixEnd_1125525 385290209101209407974207 := by
  unfold tailWord_1125525
  simp only [CollatzResearch.WordTrace]
  refine ⟨41051269247422624211346029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27367512831615082807564019 41051269247422624211346029)
  ·
    refine ⟨15394225967783484079254761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41051269247422624211346029 15394225967783484079254761)
    ·
      refine ⟨11545669475837613059441071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15394225967783484079254761 11545669475837613059441071)
      ·
        refine ⟨17318504213756419589161607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11545669475837613059441071 17318504213756419589161607)
        ·
          refine ⟨25977756320634629383742411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17318504213756419589161607 25977756320634629383742411)
          ·
            refine ⟨38966634480951944075613617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25977756320634629383742411 38966634480951944075613617)
            ·
              refine ⟨29224975860713958056710213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38966634480951944075613617 29224975860713958056710213)
              ·
                refine ⟨5479682973883867135633165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29224975860713958056710213 5479682973883867135633165)
                ·
                  refine ⟨2054881115206450175862437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5479682973883867135633165 2054881115206450175862437)
                  ·
                    refine ⟨385290209101209407974207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2054881115206450175862437 385290209101209407974207)
                    ·
                      rfl

theorem cell22_1125525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_1125525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125525 prefixEnd_1125525 := by exact prefixLift 1125525
  have htrace : WordTrace (prefixWord ++ tailWord_1125525) baseStart_1125525 baseEnd_1125525 := by
    simpa [prefixWord, tailWord_1125525, baseEnd_1125525] using wordTrace_append hprefix tailTrace_1125525
  have hstable : (prefixWord ++ tailWord_1125525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125525).length < 2 ^ (prefixWord ++ tailWord_1125525).sum := by decide
  have hdescent : baseEnd_1125525 < baseStart_1125525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125555 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 1, 5]
def baseStart_1125555 : Nat := 118140960795 + 1125555 * 2 ^ 59
def prefixEnd_1125555 : Nat := 4983230072969 + 3 ^ 40 * 1125555 * 2
def baseEnd_1125555 : Nat := 385300478714299329724115

theorem tailTrace_1125555 : CollatzResearch.WordTrace tailWord_1125555 prefixEnd_1125555 385300478714299329724115 := by
  unfold tailWord_1125555
  simp only [CollatzResearch.WordTrace]
  refine ⟨41052363437313939334938119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27368242291542626223292079 41052363437313939334938119)
  ·
    refine ⟨61578545155970909002407179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41052363437313939334938119 61578545155970909002407179)
    ·
      refine ⟨92367817733956363503610769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61578545155970909002407179 92367817733956363503610769)
      ·
        refine ⟨69275863300467272627708077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92367817733956363503610769 69275863300467272627708077)
        ·
          refine ⟨25978448737675227235390529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69275863300467272627708077 25978448737675227235390529)
          ·
            refine ⟨19483836553256420426542897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25978448737675227235390529 19483836553256420426542897)
            ·
              refine ⟨14612877414942315319907173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19483836553256420426542897 14612877414942315319907173)
              ·
                refine ⟨2739914515301684122482595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14612877414942315319907173 2739914515301684122482595)
                ·
                  refine ⟨4109871772952526183723893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2739914515301684122482595 4109871772952526183723893)
                  ·
                    refine ⟨385300478714299329724115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4109871772952526183723893 385300478714299329724115)
                    ·
                      rfl

theorem cell22_1125555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 5].length) (baseStart_1125555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125555 prefixEnd_1125555 := by exact prefixLift 1125555
  have htrace : WordTrace (prefixWord ++ tailWord_1125555) baseStart_1125555 baseEnd_1125555 := by
    simpa [prefixWord, tailWord_1125555, baseEnd_1125555] using wordTrace_append hprefix tailTrace_1125555
  have hstable : (prefixWord ++ tailWord_1125555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125555).length < 2 ^ (prefixWord ++ tailWord_1125555).sum := by decide
  have hdescent : baseEnd_1125555 < baseStart_1125555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125692 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 6]
def baseStart_1125692 : Nat := 118140960795 + 1125692 * 2 ^ 59
def prefixEnd_1125692 : Nat := 4983230072969 + 3 ^ 40 * 1125692 * 2
def baseEnd_1125692 : Nat := 128449125538025546349565

theorem tailTrace_1125692 : CollatzResearch.WordTrace tailWord_1125692 prefixEnd_1125692 128449125538025546349565 := by
  unfold tailWord_1125692
  simp only [CollatzResearch.WordTrace]
  refine ⟨20528680118908805866337665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27371573491878407821783553 20528680118908805866337665)
  ·
    refine ⟨15396510089181604399753249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20528680118908805866337665 15396510089181604399753249)
    ·
      refine ⟨11547382566886203299814937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15396510089181604399753249 11547382566886203299814937)
      ·
        refine ⟨8660536925164652474861203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11547382566886203299814937 8660536925164652474861203)
        ·
          refine ⟨12990805387746978712291805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8660536925164652474861203 12990805387746978712291805)
          ·
            refine ⟨4871552020405117017109427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12990805387746978712291805 4871552020405117017109427)
            ·
              refine ⟨7307328030607675525664141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4871552020405117017109427 7307328030607675525664141)
              ·
                refine ⟨2740248011477878322124053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7307328030607675525664141 2740248011477878322124053)
                ·
                  refine ⟨128449125538025546349565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2740248011477878322124053 128449125538025546349565)
                  ·
                    rfl

theorem cell22_1125692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_1125692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125692 prefixEnd_1125692 := by exact prefixLift 1125692
  have htrace : WordTrace (prefixWord ++ tailWord_1125692) baseStart_1125692 baseEnd_1125692 := by
    simpa [prefixWord, tailWord_1125692, baseEnd_1125692] using wordTrace_append hprefix tailTrace_1125692
  have hstable : (prefixWord ++ tailWord_1125692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125692).length < 2 ^ (prefixWord ++ tailWord_1125692).sum := by decide
  have hdescent : baseEnd_1125692 < baseStart_1125692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125722 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_1125722 : Nat := 118140960795 + 1125722 * 2 ^ 59
def prefixEnd_1125722 : Nat := 4983230072969 + 3 ^ 40 * 1125722 * 2
def baseEnd_1125722 : Nat := 385357646227166560798603

theorem tailTrace_1125722 : CollatzResearch.WordTrace tailWord_1125722 prefixEnd_1125722 385357646227166560798603 := by
  unfold tailWord_1125722
  simp only [CollatzResearch.WordTrace]
  refine ⟨10264613606927231714066855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27372302951805951237511613 10264613606927231714066855)
  ·
    refine ⟨15396920410390847571100283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10264613606927231714066855 15396920410390847571100283)
    ·
      refine ⟨23095380615586271356650425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15396920410390847571100283 23095380615586271356650425)
      ·
        refine ⟨17321535461689703517487819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23095380615586271356650425 17321535461689703517487819)
        ·
          refine ⟨25982303192534555276231729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17321535461689703517487819 25982303192534555276231729)
          ·
            refine ⟨19486727394400916457173797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25982303192534555276231729 19486727394400916457173797)
            ·
              refine ⟨3653761386450171835720087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19486727394400916457173797 3653761386450171835720087)
              ·
                refine ⟨5480642079675257753580131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3653761386450171835720087 5480642079675257753580131)
                ·
                  refine ⟨8220963119512886630370197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5480642079675257753580131 8220963119512886630370197)
                  ·
                    refine ⟨385357646227166560798603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8220963119512886630370197 385357646227166560798603)
                    ·
                      rfl

theorem cell22_1125722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_1125722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125722 prefixEnd_1125722 := by exact prefixLift 1125722
  have htrace : WordTrace (prefixWord ++ tailWord_1125722) baseStart_1125722 baseEnd_1125722 := by
    simpa [prefixWord, tailWord_1125722, baseEnd_1125722] using wordTrace_append hprefix tailTrace_1125722
  have hstable : (prefixWord ++ tailWord_1125722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125722).length < 2 ^ (prefixWord ++ tailWord_1125722).sum := by decide
  have hdescent : baseEnd_1125722 < baseStart_1125722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125827 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 8]
def baseStart_1125827 : Nat := 118140960795 + 1125827 * 2 ^ 59
def prefixEnd_1125827 : Nat := 4983230072969 + 3 ^ 40 * 1125827 * 2
def baseEnd_1125827 : Nat := 128464529957660428974427

theorem tailTrace_1125827 : CollatzResearch.WordTrace tailWord_1125827 prefixEnd_1125827 128464529957660428974427 := by
  unfold tailWord_1125827
  simp only [CollatzResearch.WordTrace]
  refine ⟨41062284092328529788839735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27374856061552353192559823 41062284092328529788839735)
  ·
    refine ⟨61593426138492794683259603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41062284092328529788839735 61593426138492794683259603)
    ·
      refine ⟨92390139207739192024889405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61593426138492794683259603 92390139207739192024889405)
      ·
        refine ⟨34646302202902197009333527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92390139207739192024889405 34646302202902197009333527)
        ·
          refine ⟨51969453304353295514000291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34646302202902197009333527 51969453304353295514000291)
          ·
            refine ⟨77954179956529943271000437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51969453304353295514000291 77954179956529943271000437)
            ·
              refine ⟨7308204370924682181656291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77954179956529943271000437 7308204370924682181656291)
              ·
                refine ⟨10962306556387023272484437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7308204370924682181656291 10962306556387023272484437)
                ·
                  refine ⟨128464529957660428974427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10962306556387023272484437 128464529957660428974427)
                  ·
                    rfl

theorem cell22_1125827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 8].length) (baseStart_1125827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125827 prefixEnd_1125827 := by exact prefixLift 1125827
  have htrace : WordTrace (prefixWord ++ tailWord_1125827) baseStart_1125827 baseEnd_1125827 := by
    simpa [prefixWord, tailWord_1125827, baseEnd_1125827] using wordTrace_append hprefix tailTrace_1125827
  have hstable : (prefixWord ++ tailWord_1125827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125827).length < 2 ^ (prefixWord ++ tailWord_1125827).sum := by decide
  have hdescent : baseEnd_1125827 < baseStart_1125827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1125861 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 6]
def baseStart_1125861 : Nat := 118140960795 + 1125861 * 2 ^ 59
def prefixEnd_1125861 : Nat := 4983230072969 + 3 ^ 40 * 1125861 * 2
def baseEnd_1125861 : Nat := 128468409589272177191059

theorem tailTrace_1125861 : CollatzResearch.WordTrace tailWord_1125861 prefixEnd_1125861 128468409589272177191059 := by
  unfold tailWord_1125861
  simp only [CollatzResearch.WordTrace]
  refine ⟨41063524174205353595577437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27375682782803569063718291 41063524174205353595577437)
  ·
    refine ⟨15398821565327007598341539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41063524174205353595577437 15398821565327007598341539)
    ·
      refine ⟨23098232347990511397512309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15398821565327007598341539 23098232347990511397512309)
      ·
        refine ⟨2165459282624110443516779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23098232347990511397512309 2165459282624110443516779)
        ·
          refine ⟨3248188923936165665275169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2165459282624110443516779 3248188923936165665275169)
          ·
            refine ⟨2436141692952124248956377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3248188923936165665275169 2436141692952124248956377)
            ·
              refine ⟨1827106269714093186717283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2436141692952124248956377 1827106269714093186717283)
              ·
                refine ⟨2740659404571139780075925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827106269714093186717283 2740659404571139780075925)
                ·
                  refine ⟨128468409589272177191059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2740659404571139780075925 128468409589272177191059)
                  ·
                    rfl

theorem cell22_1125861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_1125861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1125861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1125861 prefixEnd_1125861 := by exact prefixLift 1125861
  have htrace : WordTrace (prefixWord ++ tailWord_1125861) baseStart_1125861 baseEnd_1125861 := by
    simpa [prefixWord, tailWord_1125861, baseEnd_1125861] using wordTrace_append hprefix tailTrace_1125861
  have hstable : (prefixWord ++ tailWord_1125861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1125861).length < 2 ^ (prefixWord ++ tailWord_1125861).sum := by decide
  have hdescent : baseEnd_1125861 < baseStart_1125861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1125861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126011 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 4, 3]
def baseStart_1126011 : Nat := 118140960795 + 1126011 * 2 ^ 59
def prefixEnd_1126011 : Nat := 4983230072969 + 3 ^ 40 * 1126011 * 2
def baseEnd_1126011 : Nat := 385456576833266140322717

theorem tailTrace_1126011 : CollatzResearch.WordTrace tailWord_1126011 prefixEnd_1126011 385456576833266140322717 := by
  unfold tailWord_1126011
  simp only [CollatzResearch.WordTrace]
  refine ⟨41068995123661929213537887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27379330082441286142358591 41068995123661929213537887)
  ·
    refine ⟨61603492685492893820306831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41068995123661929213537887 61603492685492893820306831)
    ·
      refine ⟨92405239028239340730460247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61603492685492893820306831 92405239028239340730460247)
      ·
        refine ⟨138607858542359011095690371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92405239028239340730460247 138607858542359011095690371)
        ·
          refine ⟨207911787813538516643535557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138607858542359011095690371 207911787813538516643535557)
          ·
            refine ⟨38983460215038471870662917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 207911787813538516643535557 38983460215038471870662917)
            ·
              refine ⟨7309398790319713475749297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38983460215038471870662917 7309398790319713475749297)
              ·
                refine ⟨5482049092739785106811973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7309398790319713475749297 5482049092739785106811973)
                ·
                  refine ⟨1027884204888709707527245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5482049092739785106811973 1027884204888709707527245)
                  ·
                    refine ⟨385456576833266140322717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1027884204888709707527245 385456576833266140322717)
                    ·
                      rfl

theorem cell22_1126011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 3].length) (baseStart_1126011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126011 prefixEnd_1126011 := by exact prefixLift 1126011
  have htrace : WordTrace (prefixWord ++ tailWord_1126011) baseStart_1126011 baseEnd_1126011 := by
    simpa [prefixWord, tailWord_1126011, baseEnd_1126011] using wordTrace_append hprefix tailTrace_1126011
  have hstable : (prefixWord ++ tailWord_1126011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126011).length < 2 ^ (prefixWord ++ tailWord_1126011).sum := by decide
  have hdescent : baseEnd_1126011 < baseStart_1126011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126013 : List Nat := [1, 4, 1, 1, 4, 1, 1, 5, 4]
def baseStart_1126013 : Nat := 118140960795 + 1126013 * 2 ^ 59
def prefixEnd_1126013 : Nat := 4983230072969 + 3 ^ 40 * 1126013 * 2
def baseEnd_1126013 : Nat := 128485753824712933924237

theorem tailTrace_1126013 : CollatzResearch.WordTrace tailWord_1126013 prefixEnd_1126013 128485753824712933924237 := by
  unfold tailWord_1126013
  simp only [CollatzResearch.WordTrace]
  refine ⟨41069068069654683555110693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27379378713103122370073795 41069068069654683555110693)
  ·
    refine ⟨7700450263060253166583255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41069068069654683555110693 7700450263060253166583255)
    ·
      refine ⟨11550675394590379749874883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7700450263060253166583255 11550675394590379749874883)
      ·
        refine ⟨17326013091885569624812325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11550675394590379749874883 17326013091885569624812325)
        ·
          refine ⟨3248627454728544304652311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17326013091885569624812325 3248627454728544304652311)
          ·
            refine ⟨4872941182092816456978467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3248627454728544304652311 4872941182092816456978467)
            ·
              refine ⟨7309411773139224685467701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4872941182092816456978467 7309411773139224685467701)
              ·
                refine ⟨685257353731802314262597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7309411773139224685467701 685257353731802314262597)
                ·
                  refine ⟨128485753824712933924237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 685257353731802314262597 128485753824712933924237)
                  ·
                    rfl

theorem cell22_1126013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_1126013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126013 prefixEnd_1126013 := by exact prefixLift 1126013
  have htrace : WordTrace (prefixWord ++ tailWord_1126013) baseStart_1126013 baseEnd_1126013 := by
    simpa [prefixWord, tailWord_1126013, baseEnd_1126013] using wordTrace_append hprefix tailTrace_1126013
  have hstable : (prefixWord ++ tailWord_1126013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126013).length < 2 ^ (prefixWord ++ tailWord_1126013).sum := by decide
  have hdescent : baseEnd_1126013 < baseStart_1126013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126161 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 1, 6]
def baseStart_1126161 : Nat := 118140960795 + 1126161 * 2 ^ 59
def prefixEnd_1126161 : Nat := 4983230072969 + 3 ^ 40 * 1126161 * 2
def baseEnd_1126161 : Nat := 385507924898715749072257

theorem tailTrace_1126161 : CollatzResearch.WordTrace tailWord_1126161 prefixEnd_1126161 385507924898715749072257 := by
  unfold tailWord_1126161
  simp only [CollatzResearch.WordTrace]
  refine ⟨41074466073118504831498337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27382977382079003220998891 41074466073118504831498337)
  ·
    refine ⟨30805849554838878623623753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41074466073118504831498337 30805849554838878623623753)
    ·
      refine ⟨23104387166129158967717815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30805849554838878623623753 23104387166129158967717815)
      ·
        refine ⟨34656580749193738451576723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23104387166129158967717815 34656580749193738451576723)
        ·
          refine ⟨51984871123790607677365085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34656580749193738451576723 51984871123790607677365085)
          ·
            refine ⟨19494326671421477879011907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51984871123790607677365085 19494326671421477879011907)
            ·
              refine ⟨29241490007132216818517861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19494326671421477879011907 29241490007132216818517861)
              ·
                refine ⟨5482779376337290653472099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29241490007132216818517861 5482779376337290653472099)
                ·
                  refine ⟨8224169064505935980208149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5482779376337290653472099 8224169064505935980208149)
                  ·
                    refine ⟨385507924898715749072257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8224169064505935980208149 385507924898715749072257)
                    ·
                      rfl

theorem cell22_1126161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_1126161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126161 prefixEnd_1126161 := by exact prefixLift 1126161
  have htrace : WordTrace (prefixWord ++ tailWord_1126161) baseStart_1126161 baseEnd_1126161 := by
    simpa [prefixWord, tailWord_1126161, baseEnd_1126161] using wordTrace_append hprefix tailTrace_1126161
  have hstable : (prefixWord ++ tailWord_1126161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126161).length < 2 ^ (prefixWord ++ tailWord_1126161).sum := by decide
  have hdescent : baseEnd_1126161 < baseStart_1126161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126178 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1126178 : Nat := 118140960795 + 1126178 * 2 ^ 59
def prefixEnd_1126178 : Nat := 4983230072969 + 3 ^ 40 * 1126178 * 2
def baseEnd_1126178 : Nat := 385513744346133371397205

theorem tailTrace_1126178 : CollatzResearch.WordTrace tailWord_1126178 prefixEnd_1126178 385513744346133371397205 := by
  unfold tailWord_1126178
  simp only [CollatzResearch.WordTrace]
  refine ⟨10268771528514229183716797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27383390742704611156578125 10268771528514229183716797)
  ·
    refine ⟨3850789323192835943893799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10268771528514229183716797 3850789323192835943893799)
    ·
      refine ⟨5776183984789253915840699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3850789323192835943893799 5776183984789253915840699)
      ·
        refine ⟨8664275977183880873761049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5776183984789253915840699 8664275977183880873761049)
        ·
          refine ⟨6498206982887910655320787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8664275977183880873761049 6498206982887910655320787)
          ·
            refine ⟨9747310474331865982981181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6498206982887910655320787 9747310474331865982981181)
            ·
              refine ⟨3655241427874449743617943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9747310474331865982981181 3655241427874449743617943)
              ·
                refine ⟨5482862141811674615426915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3655241427874449743617943 5482862141811674615426915)
                ·
                  refine ⟨8224293212717511923140373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5482862141811674615426915 8224293212717511923140373)
                  ·
                    refine ⟨385513744346133371397205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8224293212717511923140373 385513744346133371397205)
                    ·
                      rfl

theorem cell22_1126178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1126178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126178 prefixEnd_1126178 := by exact prefixLift 1126178
  have htrace : WordTrace (prefixWord ++ tailWord_1126178) baseStart_1126178 baseEnd_1126178 := by
    simpa [prefixWord, tailWord_1126178, baseEnd_1126178] using wordTrace_append hprefix tailTrace_1126178
  have hstable : (prefixWord ++ tailWord_1126178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126178).length < 2 ^ (prefixWord ++ tailWord_1126178).sum := by decide
  have hdescent : baseEnd_1126178 < baseStart_1126178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126214 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_1126214 : Nat := 118140960795 + 1126214 * 2 ^ 59
def prefixEnd_1126214 : Nat := 4983230072969 + 3 ^ 40 * 1126214 * 2
def baseEnd_1126214 : Nat := 385526067881841277497095

theorem tailTrace_1126214 : CollatzResearch.WordTrace tailWord_1126214 prefixEnd_1126214 385526067881841277497095 := by
  unfold tailWord_1126214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283637473185202965099303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27384266094617663255451797 1283637473185202965099303)
  ·
    refine ⟨1925456209777804447648955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1283637473185202965099303 1925456209777804447648955)
    ·
      refine ⟨2888184314666706671473433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1925456209777804447648955 2888184314666706671473433)
      ·
        refine ⟨2166138236000030003605075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2888184314666706671473433 2166138236000030003605075)
        ·
          refine ⟨3249207354000045005407613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2166138236000030003605075 3249207354000045005407613)
          ·
            refine ⟨1218452757750016877027855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3249207354000045005407613 1218452757750016877027855)
            ·
              refine ⟨1827679136625025315541783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1218452757750016877027855 1827679136625025315541783)
              ·
                refine ⟨2741518704937537973312675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1827679136625025315541783 2741518704937537973312675)
                ·
                  refine ⟨4112278057406306959969013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2741518704937537973312675 4112278057406306959969013)
                  ·
                    refine ⟨385526067881841277497095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4112278057406306959969013 385526067881841277497095)
                    ·
                      rfl

theorem cell22_1126214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_1126214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126214 prefixEnd_1126214 := by exact prefixLift 1126214
  have htrace : WordTrace (prefixWord ++ tailWord_1126214) baseStart_1126214 baseEnd_1126214 := by
    simpa [prefixWord, tailWord_1126214, baseEnd_1126214] using wordTrace_append hprefix tailTrace_1126214
  have hstable : (prefixWord ++ tailWord_1126214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126214).length < 2 ^ (prefixWord ++ tailWord_1126214).sum := by decide
  have hdescent : baseEnd_1126214 < baseStart_1126214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126225 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 3, 3]
def baseStart_1126225 : Nat := 118140960795 + 1126225 * 2 ^ 59
def prefixEnd_1126225 : Nat := 4983230072969 + 3 ^ 40 * 1126225 * 2
def baseEnd_1126225 : Nat := 385529833406640915472061

theorem tailTrace_1126225 : CollatzResearch.WordTrace tailWord_1126225 prefixEnd_1126225 385529833406640915472061 := by
  unfold tailWord_1126225
  simp only [CollatzResearch.WordTrace]
  refine ⟨41076800344886643761828129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27384533563257762507885419 41076800344886643761828129)
  ·
    refine ⟨30807600258664982821371097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41076800344886643761828129 30807600258664982821371097)
    ·
      refine ⟨23105700193998737116028323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30807600258664982821371097 23105700193998737116028323)
      ·
        refine ⟨34658550290998105674042485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23105700193998737116028323 34658550290998105674042485)
        ·
          refine ⟨3249239089781072406941483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34658550290998105674042485 3249239089781072406941483)
          ·
            refine ⟨4873858634671608610412225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3249239089781072406941483 4873858634671608610412225)
            ·
              refine ⟨3655393976003706457809169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4873858634671608610412225 3655393976003706457809169)
              ·
                refine ⟨2741545482002779843356877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3655393976003706457809169 2741545482002779843356877)
                ·
                  refine ⟨1028079555751042441258829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2741545482002779843356877 1028079555751042441258829)
                  ·
                    refine ⟨385529833406640915472061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1028079555751042441258829 385529833406640915472061)
                    ·
                      rfl

theorem cell22_1126225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_1126225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126225 prefixEnd_1126225 := by exact prefixLift 1126225
  have htrace : WordTrace (prefixWord ++ tailWord_1126225) baseStart_1126225 baseEnd_1126225 := by
    simpa [prefixWord, tailWord_1126225, baseEnd_1126225] using wordTrace_append hprefix tailTrace_1126225
  have hstable : (prefixWord ++ tailWord_1126225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126225).length < 2 ^ (prefixWord ++ tailWord_1126225).sum := by decide
  have hdescent : baseEnd_1126225 < baseStart_1126225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126253 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_1126253 : Nat := 118140960795 + 1126253 * 2 ^ 59
def prefixEnd_1126253 : Nat := 4983230072969 + 3 ^ 40 * 1126253 * 2
def baseEnd_1126253 : Nat := 385539418378858175771975

theorem tailTrace_1126253 : CollatzResearch.WordTrace tailWord_1126253 prefixEnd_1126253 385539418378858175771975 := by
  unfold tailWord_1126253
  simp only [CollatzResearch.WordTrace]
  refine ⟨41077821588785204543847413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27385214392523469695898275 41077821588785204543847413)
  ·
    refine ⟨3851045773948612925985695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41077821588785204543847413 3851045773948612925985695)
    ·
      refine ⟨5776568660922919388978543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3851045773948612925985695 5776568660922919388978543)
      ·
        refine ⟨8664852991384379083467815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5776568660922919388978543 8664852991384379083467815)
        ·
          refine ⟨12997279487076568625201723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8664852991384379083467815 12997279487076568625201723)
          ·
            refine ⟨19495919230614852937802585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12997279487076568625201723 19495919230614852937802585)
            ·
              refine ⟨14621939422961139703351939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19495919230614852937802585 14621939422961139703351939)
              ·
                refine ⟨21932909134441709555027909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14621939422961139703351939 21932909134441709555027909)
                ·
                  refine ⟨4112420462707820541567733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21932909134441709555027909 4112420462707820541567733)
                  ·
                    refine ⟨385539418378858175771975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4112420462707820541567733 385539418378858175771975)
                    ·
                      rfl

theorem cell22_1126253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_1126253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126253 prefixEnd_1126253 := by exact prefixLift 1126253
  have htrace : WordTrace (prefixWord ++ tailWord_1126253) baseStart_1126253 baseEnd_1126253 := by
    simpa [prefixWord, tailWord_1126253, baseEnd_1126253] using wordTrace_append hprefix tailTrace_1126253
  have hstable : (prefixWord ++ tailWord_1126253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126253).length < 2 ^ (prefixWord ++ tailWord_1126253).sum := by decide
  have hdescent : baseEnd_1126253 < baseStart_1126253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126313 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 4, 4]
def baseStart_1126313 : Nat := 118140960795 + 1126313 * 2 ^ 59
def prefixEnd_1126313 : Nat := 4983230072969 + 3 ^ 40 * 1126313 * 2
def baseEnd_1126313 : Nat := 385559957605038019271791

theorem tailTrace_1126313 : CollatzResearch.WordTrace tailWord_1126313 prefixEnd_1126313 385559957605038019271791 := by
  unfold tailWord_1126313
  simp only [CollatzResearch.WordTrace]
  refine ⟨41080009968567834791031593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27386673312378556527354395 41080009968567834791031593)
  ·
    refine ⟨30810007476425876093273695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41080009968567834791031593 30810007476425876093273695)
    ·
      refine ⟨46215011214638814139910543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30810007476425876093273695 46215011214638814139910543)
      ·
        refine ⟨69322516821958221209865815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46215011214638814139910543 69322516821958221209865815)
        ·
          refine ⟨103983775232937331814798723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69322516821958221209865815 103983775232937331814798723)
          ·
            refine ⟨155975662849405997722198085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103983775232937331814798723 155975662849405997722198085)
            ·
              refine ⟨29245436784263624572912141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 155975662849405997722198085 29245436784263624572912141)
              ·
                refine ⟨10967038794098859214842053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29245436784263624572912141 10967038794098859214842053)
                ·
                  refine ⟨2056319773893536102782885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10967038794098859214842053 2056319773893536102782885)
                  ·
                    refine ⟨385559957605038019271791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2056319773893536102782885 385559957605038019271791)
                    ·
                      rfl

theorem cell22_1126313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_1126313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126313 prefixEnd_1126313 := by exact prefixLift 1126313
  have htrace : WordTrace (prefixWord ++ tailWord_1126313) baseStart_1126313 baseEnd_1126313 := by
    simpa [prefixWord, tailWord_1126313, baseEnd_1126313] using wordTrace_append hprefix tailTrace_1126313
  have hstable : (prefixWord ++ tailWord_1126313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126313).length < 2 ^ (prefixWord ++ tailWord_1126313).sum := by decide
  have hdescent : baseEnd_1126313 < baseStart_1126313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126360 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 5, 3]
def baseStart_1126360 : Nat := 118140960795 + 1126360 * 2 ^ 59
def prefixEnd_1126360 : Nat := 4983230072969 + 3 ^ 40 * 1126360 * 2
def baseEnd_1126360 : Nat := 385576046665545563346647

theorem tailTrace_1126360 : CollatzResearch.WordTrace tailWord_1126360 prefixEnd_1126360 385576046665545563346647 := by
  unfold tailWord_1126360
  simp only [CollatzResearch.WordTrace]
  refine ⟨20540862099698780908996267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27387816132931707878661689 20540862099698780908996267)
  ·
    refine ⟨30811293149548171363494401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20540862099698780908996267 30811293149548171363494401)
    ·
      refine ⟨23108469862161128522620801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30811293149548171363494401 23108469862161128522620801)
      ·
        refine ⟨17331352396620846391965601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23108469862161128522620801 17331352396620846391965601)
        ·
          refine ⟨12998514297465634793974201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17331352396620846391965601 12998514297465634793974201)
          ·
            refine ⟨9748885723099226095480651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12998514297465634793974201 9748885723099226095480651)
            ·
              refine ⟨14623328584648839143220977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9748885723099226095480651 14623328584648839143220977)
              ·
                refine ⟨10967496438486629357415733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14623328584648839143220977 10967496438486629357415733)
                ·
                  refine ⟨1028202791108121502257725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10967496438486629357415733 1028202791108121502257725)
                  ·
                    refine ⟨385576046665545563346647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1028202791108121502257725 385576046665545563346647)
                    ·
                      rfl

theorem cell22_1126360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_1126360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126360 prefixEnd_1126360 := by exact prefixLift 1126360
  have htrace : WordTrace (prefixWord ++ tailWord_1126360) baseStart_1126360 baseEnd_1126360 := by
    simpa [prefixWord, tailWord_1126360, baseEnd_1126360] using wordTrace_append hprefix tailTrace_1126360
  have hstable : (prefixWord ++ tailWord_1126360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126360).length < 2 ^ (prefixWord ++ tailWord_1126360).sum := by decide
  have hdescent : baseEnd_1126360 < baseStart_1126360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126403 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 2, 8]
def baseStart_1126403 : Nat := 118140960795 + 1126403 * 2 ^ 59
def prefixEnd_1126403 : Nat := 4983230072969 + 3 ^ 40 * 1126403 * 2
def baseEnd_1126403 : Nat := 385590766444307784521515

theorem tailTrace_1126403 : CollatzResearch.WordTrace tailWord_1126403 prefixEnd_1126403 385590766444307784521515 := by
  unfold tailWord_1126403
  simp only [CollatzResearch.WordTrace]
  refine ⟨41083292538241780161807863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27388861692161186774538575 41083292538241780161807863)
  ·
    refine ⟨61624938807362670242711795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41083292538241780161807863 61624938807362670242711795)
    ·
      refine ⟨92437408211044005364067693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61624938807362670242711795 92437408211044005364067693)
      ·
        refine ⟨34664028079141502011525385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92437408211044005364067693 34664028079141502011525385)
        ·
          refine ⟨25998021059356126508644039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34664028079141502011525385 25998021059356126508644039)
          ·
            refine ⟨38997031589034189762966059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25998021059356126508644039 38997031589034189762966059)
            ·
              refine ⟨58495547383551284644449089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38997031589034189762966059 58495547383551284644449089)
              ·
                refine ⟨43871660537663463483336817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58495547383551284644449089 43871660537663463483336817)
                ·
                  refine ⟨32903745403247597612502613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43871660537663463483336817 32903745403247597612502613)
                  ·
                    refine ⟨385590766444307784521515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32903745403247597612502613 385590766444307784521515)
                    ·
                      rfl

theorem cell22_1126403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_1126403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126403 prefixEnd_1126403 := by exact prefixLift 1126403
  have htrace : WordTrace (prefixWord ++ tailWord_1126403) baseStart_1126403 baseEnd_1126403 := by
    simpa [prefixWord, tailWord_1126403, baseEnd_1126403] using wordTrace_append hprefix tailTrace_1126403
  have hstable : (prefixWord ++ tailWord_1126403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126403).length < 2 ^ (prefixWord ++ tailWord_1126403).sum := by decide
  have hdescent : baseEnd_1126403 < baseStart_1126403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126512 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 5, 3]
def baseStart_1126512 : Nat := 118140960795 + 1126512 * 2 ^ 59
def prefixEnd_1126512 : Nat := 4983230072969 + 3 ^ 40 * 1126512 * 2
def baseEnd_1126512 : Nat := 385628079371867833546181

theorem tailTrace_1126512 : CollatzResearch.WordTrace tailWord_1126512 prefixEnd_1126512 385628079371867833546181 := by
  unfold tailWord_1126512
  simp only [CollatzResearch.WordTrace]
  refine ⟨20543634047423445888762895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27391512063231261185017193 20543634047423445888762895)
  ·
    refine ⟨30815451071135168833144343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20543634047423445888762895 30815451071135168833144343)
    ·
      refine ⟨46223176606702753249716515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30815451071135168833144343 46223176606702753249716515)
      ·
        refine ⟨69334764910054129874574773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46223176606702753249716515 69334764910054129874574773)
        ·
          refine ⟨6500134210317574675741385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69334764910054129874574773 6500134210317574675741385)
          ·
            refine ⟨4875100657738181006806039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6500134210317574675741385 4875100657738181006806039)
            ·
              refine ⟨7312650986607271510209059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4875100657738181006806039 7312650986607271510209059)
              ·
                refine ⟨10968976479910907265313589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7312650986607271510209059 10968976479910907265313589)
                ·
                  refine ⟨1028341544991647556123149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10968976479910907265313589 1028341544991647556123149)
                  ·
                    refine ⟨385628079371867833546181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1028341544991647556123149 385628079371867833546181)
                    ·
                      rfl

theorem cell22_1126512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 5, 3].length) (baseStart_1126512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126512 prefixEnd_1126512 := by exact prefixLift 1126512
  have htrace : WordTrace (prefixWord ++ tailWord_1126512) baseStart_1126512 baseEnd_1126512 := by
    simpa [prefixWord, tailWord_1126512, baseEnd_1126512] using wordTrace_append hprefix tailTrace_1126512
  have hstable : (prefixWord ++ tailWord_1126512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126512).length < 2 ^ (prefixWord ++ tailWord_1126512).sum := by decide
  have hdescent : baseEnd_1126512 < baseStart_1126512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126546 : List Nat := [3, 2, 3, 1, 1, 1, 1, 6, 1, 3]
def baseStart_1126546 : Nat := 118140960795 + 1126546 * 2 ^ 59
def prefixEnd_1126546 : Nat := 4983230072969 + 3 ^ 40 * 1126546 * 2
def baseEnd_1126546 : Nat := 385639718266703078196077

theorem tailTrace_1126546 : CollatzResearch.WordTrace tailWord_1126546 prefixEnd_1126546 385639718266703078196077 := by
  unfold tailWord_1126546
  simp only [CollatzResearch.WordTrace]
  refine ⟨10272127044180928896065873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27392338784482477056175661 10272127044180928896065873)
  ·
    refine ⟨7704095283135696672049405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10272127044180928896065873 7704095283135696672049405)
    ·
      refine ⟨2889035731175886252018527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7704095283135696672049405 2889035731175886252018527)
      ·
        refine ⟨4333553596763829378027791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2889035731175886252018527 4333553596763829378027791)
        ·
          refine ⟨6500330395145744067041687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4333553596763829378027791 6500330395145744067041687)
          ·
            refine ⟨9750495592718616100562531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6500330395145744067041687 9750495592718616100562531)
            ·
              refine ⟨14625743389077924150843797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9750495592718616100562531 14625743389077924150843797)
              ·
                refine ⟨685581721363027694570803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14625743389077924150843797 685581721363027694570803)
                ·
                  refine ⟨1028372582044541541856205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 685581721363027694570803 1028372582044541541856205)
                  ·
                    refine ⟨385639718266703078196077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1028372582044541541856205 385639718266703078196077)
                    ·
                      rfl

theorem cell22_1126546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_1126546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126546 prefixEnd_1126546 := by exact prefixLift 1126546
  have htrace : WordTrace (prefixWord ++ tailWord_1126546) baseStart_1126546 baseEnd_1126546 := by
    simpa [prefixWord, tailWord_1126546, baseEnd_1126546] using wordTrace_append hprefix tailTrace_1126546
  have hstable : (prefixWord ++ tailWord_1126546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126546).length < 2 ^ (prefixWord ++ tailWord_1126546).sum := by decide
  have hdescent : baseEnd_1126546 < baseStart_1126546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126557 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1126557 : Nat := 118140960795 + 1126557 * 2 ^ 59
def prefixEnd_1126557 : Nat := 4983230072969 + 3 ^ 40 * 1126557 * 2
def baseEnd_1126557 : Nat := 385643483791502716171043

theorem tailTrace_1126557 : CollatzResearch.WordTrace tailWord_1126557 prefixEnd_1126557 385643483791502716171043 := by
  unfold tailWord_1126557
  simp only [CollatzResearch.WordTrace]
  refine ⟨41088909379683864462913925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27392606253122576308609283 41088909379683864462913925)
  ·
    refine ⟨7704170508690724586796361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41088909379683864462913925 7704170508690724586796361)
    ·
      refine ⟨5778127881518043440097271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7704170508690724586796361 5778127881518043440097271)
      ·
        refine ⟨8667191822277065160145907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5778127881518043440097271 8667191822277065160145907)
        ·
          refine ⟨13000787733415597740218861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8667191822277065160145907 13000787733415597740218861)
          ·
            refine ⟨4875295400030849152582073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13000787733415597740218861 4875295400030849152582073)
            ·
              refine ⟨3656471550023136864436555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4875295400030849152582073 3656471550023136864436555)
              ·
                refine ⟨5484707325034705296654833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3656471550023136864436555 5484707325034705296654833)
                ·
                  refine ⟨4113530493776028972491125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5484707325034705296654833 4113530493776028972491125)
                  ·
                    refine ⟨385643483791502716171043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4113530493776028972491125 385643483791502716171043)
                    ·
                      rfl

theorem cell22_1126557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1126557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126557 prefixEnd_1126557 := by exact prefixLift 1126557
  have htrace : WordTrace (prefixWord ++ tailWord_1126557) baseStart_1126557 baseEnd_1126557 := by
    simpa [prefixWord, tailWord_1126557, baseEnd_1126557] using wordTrace_append hprefix tailTrace_1126557
  have hstable : (prefixWord ++ tailWord_1126557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126557).length < 2 ^ (prefixWord ++ tailWord_1126557).sum := by decide
  have hdescent : baseEnd_1126557 < baseStart_1126557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126632 : List Nat := [2, 1, 4, 1, 2, 2, 2, 8]
def baseStart_1126632 : Nat := 118140960795 + 1126632 * 2 ^ 59
def prefixEnd_1126632 : Nat := 4983230072969 + 3 ^ 40 * 1126632 * 2
def baseEnd_1126632 : Nat := 42852128647136391171757

theorem tailTrace_1126632 : CollatzResearch.WordTrace tailWord_1126632 prefixEnd_1126632 42852128647136391171757 := by
  unfold tailWord_1126632
  simp only [CollatzResearch.WordTrace]
  refine ⟨20545822427206076135947075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27394429902941434847929433 20545822427206076135947075)
  ·
    refine ⟨30818733640809114203920613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20545822427206076135947075 30818733640809114203920613)
    ·
      refine ⟨5778512557651708913235115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30818733640809114203920613 5778512557651708913235115)
      ·
        refine ⟨8667768836477563369852673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5778512557651708913235115 8667768836477563369852673)
        ·
          refine ⟨6500826627358172527389505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8667768836477563369852673 6500826627358172527389505)
          ·
            refine ⟨4875619970518629395542129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6500826627358172527389505 4875619970518629395542129)
            ·
              refine ⟨3656714977888972046656597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4875619970518629395542129 3656714977888972046656597)
              ·
                refine ⟨42852128647136391171757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3656714977888972046656597 42852128647136391171757)
                ·
                  rfl

theorem cell22_1126632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 8].length) (baseStart_1126632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126632 prefixEnd_1126632 := by exact prefixLift 1126632
  have htrace : WordTrace (prefixWord ++ tailWord_1126632) baseStart_1126632 baseEnd_1126632 := by
    simpa [prefixWord, tailWord_1126632, baseEnd_1126632] using wordTrace_append hprefix tailTrace_1126632
  have hstable : (prefixWord ++ tailWord_1126632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126632).length < 2 ^ (prefixWord ++ tailWord_1126632).sum := by decide
  have hdescent : baseEnd_1126632 < baseStart_1126632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126634 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 2, 4]
def baseStart_1126634 : Nat := 118140960795 + 1126634 * 2 ^ 59
def prefixEnd_1126634 : Nat := 4983230072969 + 3 ^ 40 * 1126634 * 2
def baseEnd_1126634 : Nat := 385669842465100181995807

theorem tailTrace_1126634 : CollatzResearch.WordTrace tailWord_1126634 prefixEnd_1126634 385669842465100181995807 := by
  unfold tailWord_1126634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10272929450101226653366739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27394478533603271075644637 10272929450101226653366739)
  ·
    refine ⟨15409394175151839980050109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10272929450101226653366739 15409394175151839980050109)
    ·
      refine ⟨5778522815681939992518791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15409394175151839980050109 5778522815681939992518791)
      ·
        refine ⟨8667784223522909988778187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5778522815681939992518791 8667784223522909988778187)
        ·
          refine ⟨13001676335284364983167281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8667784223522909988778187 13001676335284364983167281)
          ·
            refine ⟨9751257251463273737375461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13001676335284364983167281 9751257251463273737375461)
            ·
              refine ⟨1828360734649363825757899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9751257251463273737375461 1828360734649363825757899)
              ·
                refine ⟨2742541101974045738636849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1828360734649363825757899 2742541101974045738636849)
                ·
                  refine ⟨2056905826480534303977637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2742541101974045738636849 2056905826480534303977637)
                  ·
                    refine ⟨385669842465100181995807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2056905826480534303977637 385669842465100181995807)
                    ·
                      rfl

theorem cell22_1126634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_1126634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126634 prefixEnd_1126634 := by exact prefixLift 1126634
  have htrace : WordTrace (prefixWord ++ tailWord_1126634) baseStart_1126634 baseEnd_1126634 := by
    simpa [prefixWord, tailWord_1126634, baseEnd_1126634] using wordTrace_append hprefix tailTrace_1126634
  have hstable : (prefixWord ++ tailWord_1126634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126634).length < 2 ^ (prefixWord ++ tailWord_1126634).sum := by decide
  have hdescent : baseEnd_1126634 < baseStart_1126634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126846 : List Nat := [4, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_1126846 : Nat := 118140960795 + 1126846 * 2 ^ 59
def prefixEnd_1126846 : Nat := 4983230072969 + 3 ^ 40 * 1126846 * 2
def baseEnd_1126846 : Nat := 128580804799200765231719

theorem tailTrace_1126846 : CollatzResearch.WordTrace tailWord_1126846 prefixEnd_1126846 128580804799200765231719 := by
  unfold tailWord_1126846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5137431259454608352523049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27399633383757911213456261 5137431259454608352523049)
  ·
    refine ⟨3853073444590956264392287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5137431259454608352523049 3853073444590956264392287)
    ·
      refine ⟨5779610166886434396588431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3853073444590956264392287 5779610166886434396588431)
      ·
        refine ⟨8669415250329651594882647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5779610166886434396588431 8669415250329651594882647)
        ·
          refine ⟨13004122875494477392323971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8669415250329651594882647 13004122875494477392323971)
          ·
            refine ⟨19506184313241716088485957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13004122875494477392323971 19506184313241716088485957)
            ·
              refine ⟨3657409558732821766591117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19506184313241716088485957 3657409558732821766591117)
              ·
                refine ⟨1371528584524808162471669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3657409558732821766591117 1371528584524808162471669)
                ·
                  refine ⟨128580804799200765231719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1371528584524808162471669 128580804799200765231719)
                  ·
                    rfl

theorem cell22_1126846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_1126846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126846 prefixEnd_1126846 := by exact prefixLift 1126846
  have htrace : WordTrace (prefixWord ++ tailWord_1126846) baseStart_1126846 baseEnd_1126846 := by
    simpa [prefixWord, tailWord_1126846, baseEnd_1126846] using wordTrace_append hprefix tailTrace_1126846
  have hstable : (prefixWord ++ tailWord_1126846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126846).length < 2 ^ (prefixWord ++ tailWord_1126846).sum := by decide
  have hdescent : baseEnd_1126846 < baseStart_1126846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126874 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 8]
def baseStart_1126874 : Nat := 118140960795 + 1126874 * 2 ^ 59
def prefixEnd_1126874 : Nat := 4983230072969 + 3 ^ 40 * 1126874 * 2
def baseEnd_1126874 : Nat := 128583999789939851998357

theorem tailTrace_1126874 : CollatzResearch.WordTrace tailWord_1126874 prefixEnd_1126874 128583999789939851998357 := by
  unfold tailWord_1126874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10275117829883856900550919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27400314213023618401469117 10275117829883856900550919)
  ·
    refine ⟨15412676744825785350826379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10275117829883856900550919 15412676744825785350826379)
    ·
      refine ⟨23119015117238678026239569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15412676744825785350826379 23119015117238678026239569)
      ·
        refine ⟨17339261337929008519679677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23119015117238678026239569 17339261337929008519679677)
        ·
          refine ⟨6502223001723378194879879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17339261337929008519679677 6502223001723378194879879)
          ·
            refine ⟨9753334502585067292319819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6502223001723378194879879 9753334502585067292319819)
            ·
              refine ⟨14630001753877600938479729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9753334502585067292319819 14630001753877600938479729)
              ·
                refine ⟨10972501315408200703859797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14630001753877600938479729 10972501315408200703859797)
                ·
                  refine ⟨128583999789939851998357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10972501315408200703859797 128583999789939851998357)
                  ·
                    rfl

theorem cell22_1126874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_1126874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126874 prefixEnd_1126874 := by exact prefixLift 1126874
  have htrace : WordTrace (prefixWord ++ tailWord_1126874) baseStart_1126874 baseEnd_1126874 := by
    simpa [prefixWord, tailWord_1126874, baseEnd_1126874] using wordTrace_append hprefix tailTrace_1126874
  have hstable : (prefixWord ++ tailWord_1126874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126874).length < 2 ^ (prefixWord ++ tailWord_1126874).sum := by decide
  have hdescent : baseEnd_1126874 < baseStart_1126874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126891 : List Nat := [1, 1, 1, 1, 2, 3, 3, 6, 4]
def baseStart_1126891 : Nat := 118140960795 + 1126891 * 2 ^ 59
def prefixEnd_1126891 : Nat := 4983230072969 + 3 ^ 40 * 1126891 * 2
def baseEnd_1126891 : Nat := 128585939605745726106673

theorem tailTrace_1126891 : CollatzResearch.WordTrace tailWord_1126891 prefixEnd_1126891 128585939605745726106673 := by
  unfold tailWord_1126891
  simp only [CollatzResearch.WordTrace]
  refine ⟨41101091360473839505572527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27400727573649226337048351 41101091360473839505572527)
  ·
    refine ⟨61651637040710759258358791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41101091360473839505572527 61651637040710759258358791)
    ·
      refine ⟨92477455561066138887538187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61651637040710759258358791 92477455561066138887538187)
      ·
        refine ⟨138716183341599208331307281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92477455561066138887538187 138716183341599208331307281)
        ·
          refine ⟨104037137506199406248480461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138716183341599208331307281 104037137506199406248480461)
          ·
            refine ⟨39013926564824777343180173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104037137506199406248480461 39013926564824777343180173)
            ·
              refine ⟨14630222461809291503692565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39013926564824777343180173 14630222461809291503692565)
              ·
                refine ⟨685791677897310539235589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14630222461809291503692565 685791677897310539235589)
                ·
                  refine ⟨128585939605745726106673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 685791677897310539235589 128585939605745726106673)
                  ·
                    rfl

theorem cell22_1126891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 4].length) (baseStart_1126891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126891 prefixEnd_1126891 := by exact prefixLift 1126891
  have htrace : WordTrace (prefixWord ++ tailWord_1126891) baseStart_1126891 baseEnd_1126891 := by
    simpa [prefixWord, tailWord_1126891, baseEnd_1126891] using wordTrace_append hprefix tailTrace_1126891
  have hstable : (prefixWord ++ tailWord_1126891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126891).length < 2 ^ (prefixWord ++ tailWord_1126891).sum := by decide
  have hdescent : baseEnd_1126891 < baseStart_1126891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126904 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 3, 6]
def baseStart_1126904 : Nat := 118140960795 + 1126904 * 2 ^ 59
def prefixEnd_1126904 : Nat := 4983230072969 + 3 ^ 40 * 1126904 * 2
def baseEnd_1126904 : Nat := 385762268982909477744979

theorem tailTrace_1126904 : CollatzResearch.WordTrace tailWord_1126904 prefixEnd_1126904 385762268982909477744979 := by
  unfold tailWord_1126904
  simp only [CollatzResearch.WordTrace]
  refine ⟨20550782754713371362897883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27401043672951161817197177 20550782754713371362897883)
  ·
    refine ⟨30826174132070057044346825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20550782754713371362897883 30826174132070057044346825)
    ·
      refine ⟨23119630599052542783260119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30826174132070057044346825 23119630599052542783260119)
      ·
        refine ⟨34679445898578814174890179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23119630599052542783260119 34679445898578814174890179)
        ·
          refine ⟨52019168847868221262335269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34679445898578814174890179 52019168847868221262335269)
          ·
            refine ⟨9753594158975291486687863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52019168847868221262335269 9753594158975291486687863)
            ·
              refine ⟨14630391238462937230031795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9753594158975291486687863 14630391238462937230031795)
              ·
                refine ⟨21945586857694405845047693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14630391238462937230031795 21945586857694405845047693)
                ·
                  refine ⟨8229595071635402191892885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21945586857694405845047693 8229595071635402191892885)
                  ·
                    refine ⟨385762268982909477744979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8229595071635402191892885 385762268982909477744979)
                    ·
                      rfl

theorem cell22_1126904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_1126904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126904 prefixEnd_1126904 := by exact prefixLift 1126904
  have htrace : WordTrace (prefixWord ++ tailWord_1126904) baseStart_1126904 baseEnd_1126904 := by
    simpa [prefixWord, tailWord_1126904, baseEnd_1126904] using wordTrace_append hprefix tailTrace_1126904
  have hstable : (prefixWord ++ tailWord_1126904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126904).length < 2 ^ (prefixWord ++ tailWord_1126904).sum := by decide
  have hdescent : baseEnd_1126904 < baseStart_1126904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1126936 : List Nat := [2, 1, 2, 3, 3, 3, 8]
def baseStart_1126936 : Nat := 118140960795 + 1126936 * 2 ^ 59
def prefixEnd_1126936 : Nat := 4983230072969 + 3 ^ 40 * 1126936 * 2
def baseEnd_1126936 : Nat := 14287897156921187442403

theorem tailTrace_1126936 : CollatzResearch.WordTrace tailWord_1126936 prefixEnd_1126936 14287897156921187442403 := by
  unfold tailWord_1126936
  simp only [CollatzResearch.WordTrace]
  refine ⟨20551366322655406095480331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27401821763540541460640441 20551366322655406095480331)
  ·
    refine ⟨30827049483983109143220497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20551366322655406095480331 30827049483983109143220497)
    ·
      refine ⟨23120287112987331857415373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30827049483983109143220497 23120287112987331857415373)
      ·
        refine ⟨8670107667370249446530765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23120287112987331857415373 8670107667370249446530765)
        ·
          refine ⟨3251290375263843542449037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8670107667370249446530765 3251290375263843542449037)
          ·
            refine ⟨1219233890723941328418389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3251290375263843542449037 1219233890723941328418389)
            ·
              refine ⟨14287897156921187442403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1219233890723941328418389 14287897156921187442403)
              ·
                rfl

theorem cell22_1126936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 8].length) (baseStart_1126936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1126936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1126936 prefixEnd_1126936 := by exact prefixLift 1126936
  have htrace : WordTrace (prefixWord ++ tailWord_1126936) baseStart_1126936 baseEnd_1126936 := by
    simpa [prefixWord, tailWord_1126936, baseEnd_1126936] using wordTrace_append hprefix tailTrace_1126936
  have hstable : (prefixWord ++ tailWord_1126936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1126936).length < 2 ^ (prefixWord ++ tailWord_1126936).sum := by decide
  have hdescent : baseEnd_1126936 < baseStart_1126936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1126936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127011 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 5, 4]
def baseStart_1127011 : Nat := 118140960795 + 1127011 * 2 ^ 59
def prefixEnd_1127011 : Nat := 4983230072969 + 3 ^ 40 * 1127011 * 2
def baseEnd_1127011 : Nat := 385798897269596865319651

theorem tailTrace_1127011 : CollatzResearch.WordTrace tailWord_1127011 prefixEnd_1127011 385798897269596865319651 := by
  unfold tailWord_1127011
  simp only [CollatzResearch.WordTrace]
  refine ⟨41105468120039099999940887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27403645413359399999960591 41105468120039099999940887)
  ·
    refine ⟨61658202180058649999911331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41105468120039099999940887 61658202180058649999911331)
    ·
      refine ⟨92487303270087974999866997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61658202180058649999911331 92487303270087974999866997)
      ·
        refine ⟨8670684681570747656237531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92487303270087974999866997 8670684681570747656237531)
        ·
          refine ⟨13006027022356121484356297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8670684681570747656237531 13006027022356121484356297)
          ·
            refine ⟨9754520266767091113267223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13006027022356121484356297 9754520266767091113267223)
            ·
              refine ⟨14631780400150636669900835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9754520266767091113267223 14631780400150636669900835)
              ·
                refine ⟨21947670600225955004851253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14631780400150636669900835 21947670600225955004851253)
                ·
                  refine ⟨2057594118771183281704805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21947670600225955004851253 2057594118771183281704805)
                  ·
                    refine ⟨385798897269596865319651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2057594118771183281704805 385798897269596865319651)
                    ·
                      rfl

theorem cell22_1127011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 4].length) (baseStart_1127011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127011 prefixEnd_1127011 := by exact prefixLift 1127011
  have htrace : WordTrace (prefixWord ++ tailWord_1127011) baseStart_1127011 baseEnd_1127011 := by
    simpa [prefixWord, tailWord_1127011, baseEnd_1127011] using wordTrace_append hprefix tailTrace_1127011
  have hstable : (prefixWord ++ tailWord_1127011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127011).length < 2 ^ (prefixWord ++ tailWord_1127011).sum := by decide
  have hdescent : baseEnd_1127011 < baseStart_1127011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127013 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 2, 5]
def baseStart_1127013 : Nat := 118140960795 + 1127013 * 2 ^ 59
def prefixEnd_1127013 : Nat := 4983230072969 + 3 ^ 40 * 1127013 * 2
def baseEnd_1127013 : Nat := 385799581910469526769645

theorem tailTrace_1127013 : CollatzResearch.WordTrace tailWord_1127013 prefixEnd_1127013 385799581910469526769645 := by
  unfold tailWord_1127013
  simp only [CollatzResearch.WordTrace]
  refine ⟨41105541066031854341513693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27403694044021236227675795 41105541066031854341513693)
  ·
    refine ⟨15414577899761945378067635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41105541066031854341513693 15414577899761945378067635)
    ·
      refine ⟨23121866849642918067101453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15414577899761945378067635 23121866849642918067101453)
      ·
        refine ⟨8670700068616094275163045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23121866849642918067101453 8670700068616094275163045)
        ·
          refine ⟨1625756262865517676593071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8670700068616094275163045 1625756262865517676593071)
          ·
            refine ⟨2438634394298276514889607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625756262865517676593071 2438634394298276514889607)
            ·
              refine ⟨3657951591447414772334411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2438634394298276514889607 3657951591447414772334411)
              ·
                refine ⟨5486927387171122158501617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3657951591447414772334411 5486927387171122158501617)
                ·
                  refine ⟨4115195540378341618876213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5486927387171122158501617 4115195540378341618876213)
                  ·
                    refine ⟨385799581910469526769645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4115195540378341618876213 385799581910469526769645)
                    ·
                      rfl

theorem cell22_1127013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_1127013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127013 prefixEnd_1127013 := by exact prefixLift 1127013
  have htrace : WordTrace (prefixWord ++ tailWord_1127013) baseStart_1127013 baseEnd_1127013 := by
    simpa [prefixWord, tailWord_1127013, baseEnd_1127013] using wordTrace_append hprefix tailTrace_1127013
  have hstable : (prefixWord ++ tailWord_1127013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127013).length < 2 ^ (prefixWord ++ tailWord_1127013).sum := by decide
  have hdescent : baseEnd_1127013 < baseStart_1127013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127043 : List Nat := [1, 1, 1, 3, 3, 1, 3, 5, 4]
def baseStart_1127043 : Nat := 118140960795 + 1127043 * 2 ^ 59
def prefixEnd_1127043 : Nat := 4983230072969 + 3 ^ 40 * 1127043 * 2
def baseEnd_1127043 : Nat := 128603283841186482839851

theorem tailTrace_1127043 : CollatzResearch.WordTrace tailWord_1127043 prefixEnd_1127043 128603283841186482839851 := by
  unfold tailWord_1127043
  simp only [CollatzResearch.WordTrace]
  refine ⟨41106635255923169465105783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27404423503948779643403855 41106635255923169465105783)
  ·
    refine ⟨61659952883884754197658675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41106635255923169465105783 61659952883884754197658675)
    ·
      refine ⟨92489929325827131296488013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61659952883884754197658675 92489929325827131296488013)
      ·
        refine ⟨34683723497185174236183005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92489929325827131296488013 34683723497185174236183005)
        ·
          refine ⟨13006396311444440338568627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34683723497185174236183005 13006396311444440338568627)
          ·
            refine ⟨19509594467166660507852941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13006396311444440338568627 19509594467166660507852941)
            ·
              refine ⟨7316097925187497690444853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19509594467166660507852941 7316097925187497690444853)
              ·
                refine ⟨685884180486327908479205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7316097925187497690444853 685884180486327908479205)
                ·
                  refine ⟨128603283841186482839851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 685884180486327908479205 128603283841186482839851)
                  ·
                    rfl

theorem cell22_1127043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 4].length) (baseStart_1127043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127043 prefixEnd_1127043 := by exact prefixLift 1127043
  have htrace : WordTrace (prefixWord ++ tailWord_1127043) baseStart_1127043 baseEnd_1127043 := by
    simpa [prefixWord, tailWord_1127043, baseEnd_1127043] using wordTrace_append hprefix tailTrace_1127043
  have hstable : (prefixWord ++ tailWord_1127043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127043).length < 2 ^ (prefixWord ++ tailWord_1127043).sum := by decide
  have hdescent : baseEnd_1127043 < baseStart_1127043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127045 : List Nat := [1, 3, 1, 1, 4, 2, 4, 1, 1, 4]
def baseStart_1127045 : Nat := 118140960795 + 1127045 * 2 ^ 59
def prefixEnd_1127045 : Nat := 4983230072969 + 3 ^ 40 * 1127045 * 2
def baseEnd_1127045 : Nat := 385810536164432109969547

theorem tailTrace_1127045 : CollatzResearch.WordTrace tailWord_1127045 prefixEnd_1127045 385810536164432109969547 := by
  unfold tailWord_1127045
  simp only [CollatzResearch.WordTrace]
  refine ⟨41106708201915923806678589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27404472134610615871119059 41106708201915923806678589)
  ·
    refine ⟨15415015575718471427504471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41106708201915923806678589 15415015575718471427504471)
    ·
      refine ⟨23122523363577707141256707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15415015575718471427504471 23122523363577707141256707)
      ·
        refine ⟨34683785045366560711885061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23122523363577707141256707 34683785045366560711885061)
        ·
          refine ⟨6503209696006230133478449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34683785045366560711885061 6503209696006230133478449)
          ·
            refine ⟨4877407272004672600108837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6503209696006230133478449 4877407272004672600108837)
            ·
              refine ⟨914513863500876112520407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4877407272004672600108837 914513863500876112520407)
              ·
                refine ⟨1371770795251314168780611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914513863500876112520407 1371770795251314168780611)
                ·
                  refine ⟨2057656192876971253170917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371770795251314168780611 2057656192876971253170917)
                  ·
                    refine ⟨385810536164432109969547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2057656192876971253170917 385810536164432109969547)
                    ·
                      rfl

theorem cell22_1127045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_1127045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127045 prefixEnd_1127045 := by exact prefixLift 1127045
  have htrace : WordTrace (prefixWord ++ tailWord_1127045) baseStart_1127045 baseEnd_1127045 := by
    simpa [prefixWord, tailWord_1127045, baseEnd_1127045] using wordTrace_append hprefix tailTrace_1127045
  have hstable : (prefixWord ++ tailWord_1127045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127045).length < 2 ^ (prefixWord ++ tailWord_1127045).sum := by decide
  have hdescent : baseEnd_1127045 < baseStart_1127045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127060 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 6]
def baseStart_1127060 : Nat := 118140960795 + 1127060 * 2 ^ 59
def prefixEnd_1127060 : Nat := 4983230072969 + 3 ^ 40 * 1127060 * 2
def baseEnd_1127060 : Nat := 128605223656992356948167

theorem tailTrace_1127060 : CollatzResearch.WordTrace tailWord_1127060 prefixEnd_1127060 128605223656992356948167 := by
  unfold tailWord_1127060
  simp only [CollatzResearch.WordTrace]
  refine ⟨20553627648430790684237317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27404836864574387578983089 20553627648430790684237317)
  ·
    refine ⟨3853805184080773253294497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20553627648430790684237317 3853805184080773253294497)
    ·
      refine ⟨2890353888060579939970873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3853805184080773253294497 2890353888060579939970873)
      ·
        refine ⟨2167765416045434954978155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2890353888060579939970873 2167765416045434954978155)
        ·
          refine ⟨3251648124068152432467233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2167765416045434954978155 3251648124068152432467233)
          ·
            refine ⟨2438736093051114324350425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3251648124068152432467233 2438736093051114324350425)
            ·
              refine ⟨1829052069788335743262819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2438736093051114324350425 1829052069788335743262819)
              ·
                refine ⟨2743578104682503614894229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829052069788335743262819 2743578104682503614894229)
                ·
                  refine ⟨128605223656992356948167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2743578104682503614894229 128605223656992356948167)
                  ·
                    rfl

theorem cell22_1127060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_1127060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127060 prefixEnd_1127060 := by exact prefixLift 1127060
  have htrace : WordTrace (prefixWord ++ tailWord_1127060) baseStart_1127060 baseEnd_1127060 := by
    simpa [prefixWord, tailWord_1127060, baseEnd_1127060] using wordTrace_append hprefix tailTrace_1127060
  have hstable : (prefixWord ++ tailWord_1127060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127060).length < 2 ^ (prefixWord ++ tailWord_1127060).sum := by decide
  have hdescent : baseEnd_1127060 < baseStart_1127060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127178 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 6]
def baseStart_1127178 : Nat := 118140960795 + 1127178 * 2 ^ 59
def prefixEnd_1127178 : Nat := 4983230072969 + 3 ^ 40 * 1127178 * 2
def baseEnd_1127178 : Nat := 128618688260821365464713

theorem tailTrace_1127178 : CollatzResearch.WordTrace tailWord_1127178 prefixEnd_1127178 128618688260821365464713 := by
  unfold tailWord_1127178
  simp only [CollatzResearch.WordTrace]
  refine ⟨10277889777608521880317547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27407706073622725014180125 10277889777608521880317547)
  ·
    refine ⟨15416834666412782820476321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10277889777608521880317547 15416834666412782820476321)
    ·
      refine ⟨11562625999809587115357241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15416834666412782820476321 11562625999809587115357241)
      ·
        refine ⟨8671969499857190336517931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11562625999809587115357241 8671969499857190336517931)
        ·
          refine ⟨13007954249785785504776897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8671969499857190336517931 13007954249785785504776897)
          ·
            refine ⟨9755965687339339128582673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13007954249785785504776897 9755965687339339128582673)
            ·
              refine ⟨7316974265504504346437005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9755965687339339128582673 7316974265504504346437005)
              ·
                refine ⟨2743865349564189129913877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7316974265504504346437005 2743865349564189129913877)
                ·
                  refine ⟨128618688260821365464713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2743865349564189129913877 128618688260821365464713)
                  ·
                    rfl

theorem cell22_1127178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_1127178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127178 prefixEnd_1127178 := by exact prefixLift 1127178
  have htrace : WordTrace (prefixWord ++ tailWord_1127178) baseStart_1127178 baseEnd_1127178 := by
    simpa [prefixWord, tailWord_1127178, baseEnd_1127178] using wordTrace_append hprefix tailTrace_1127178
  have hstable : (prefixWord ++ tailWord_1127178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127178).length < 2 ^ (prefixWord ++ tailWord_1127178).sum := by decide
  have hdescent : baseEnd_1127178 < baseStart_1127178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127214 : List Nat := [4, 1, 3, 2, 1, 1, 4, 1, 1, 4]
def baseStart_1127214 : Nat := 118140960795 + 1127214 * 2 ^ 59
def prefixEnd_1127214 : Nat := 4983230072969 + 3 ^ 40 * 1127214 * 2
def baseEnd_1127214 : Nat := 385868388318172002494029

theorem tailTrace_1127214 : CollatzResearch.WordTrace tailWord_1127214 prefixEnd_1127214 385868388318172002494029 := by
  unfold tailWord_1127214
  simp only [CollatzResearch.WordTrace]
  refine ⟨5139109017287958208697587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27408581425535777113053797 5139109017287958208697587)
  ·
    refine ⟨7708663525931937313046381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5139109017287958208697587 7708663525931937313046381)
    ·
      refine ⟨2890748822224476492392393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7708663525931937313046381 2890748822224476492392393)
      ·
        refine ⟨2168061616668357369294295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2890748822224476492392393 2168061616668357369294295)
        ·
          refine ⟨3252092425002536053941443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2168061616668357369294295 3252092425002536053941443)
          ·
            refine ⟨4878138637503804080912165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3252092425002536053941443 4878138637503804080912165)
            ·
              refine ⟨914650994531963265171031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4878138637503804080912165 914650994531963265171031)
              ·
                refine ⟨1371976491797944897756547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914650994531963265171031 1371976491797944897756547)
                ·
                  refine ⟨2057964737696917346634821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1371976491797944897756547 2057964737696917346634821)
                  ·
                    refine ⟨385868388318172002494029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2057964737696917346634821 385868388318172002494029)
                    ·
                      rfl

theorem cell22_1127214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_1127214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127214 prefixEnd_1127214 := by exact prefixLift 1127214
  have htrace : WordTrace (prefixWord ++ tailWord_1127214) baseStart_1127214 baseEnd_1127214 := by
    simpa [prefixWord, tailWord_1127214, baseEnd_1127214] using wordTrace_append hprefix tailTrace_1127214
  have hstable : (prefixWord ++ tailWord_1127214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127214).length < 2 ^ (prefixWord ++ tailWord_1127214).sum := by decide
  have hdescent : baseEnd_1127214 < baseStart_1127214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127244 : List Nat := [2, 2, 1, 3, 3, 2, 3, 1, 2, 3]
def baseStart_1127244 : Nat := 118140960795 + 1127244 * 2 ^ 59
def prefixEnd_1127244 : Nat := 4983230072969 + 3 ^ 40 * 1127244 * 2
def baseEnd_1127244 : Nat := 385878657931261924243937

theorem tailTrace_1127244 : CollatzResearch.WordTrace tailWord_1127244 prefixEnd_1127244 385878657931261924243937 := by
  unfold tailWord_1127244
  simp only [CollatzResearch.WordTrace]
  refine ⟨20556983164097490396586393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27409310885463320528781857 20556983164097490396586393)
  ·
    refine ⟨15417737373073117797439795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20556983164097490396586393 15417737373073117797439795)
    ·
      refine ⟨23126606059609676696159693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15417737373073117797439795 23126606059609676696159693)
      ·
        refine ⟨8672477272353628761059885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23126606059609676696159693 8672477272353628761059885)
        ·
          refine ⟨3252178977132610785397457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8672477272353628761059885 3252178977132610785397457)
          ·
            refine ⟨2439134232849458089048093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3252178977132610785397457 2439134232849458089048093)
            ·
              refine ⟨914675337318546783393035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2439134232849458089048093 914675337318546783393035)
              ·
                refine ⟨1372013005977820175089553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914675337318546783393035 1372013005977820175089553)
                ·
                  refine ⟨1029009754483365131317165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1372013005977820175089553 1029009754483365131317165)
                  ·
                    refine ⟨385878657931261924243937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1029009754483365131317165 385878657931261924243937)
                    ·
                      rfl

theorem cell22_1127244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_1127244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127244 prefixEnd_1127244 := by exact prefixLift 1127244
  have htrace : WordTrace (prefixWord ++ tailWord_1127244) baseStart_1127244 baseEnd_1127244 := by
    simpa [prefixWord, tailWord_1127244, baseEnd_1127244] using wordTrace_append hprefix tailTrace_1127244
  have hstable : (prefixWord ++ tailWord_1127244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127244).length < 2 ^ (prefixWord ++ tailWord_1127244).sum := by decide
  have hdescent : baseEnd_1127244 < baseStart_1127244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127283 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 4, 5]
def baseStart_1127283 : Nat := 118140960795 + 1127283 * 2 ^ 59
def prefixEnd_1127283 : Nat := 4983230072969 + 3 ^ 40 * 1127283 * 2
def baseEnd_1127283 : Nat := 385892008428278822518817

theorem tailTrace_1127283 : CollatzResearch.WordTrace tailWord_1127283 prefixEnd_1127283 385892008428278822518817 := by
  unfold tailWord_1127283
  simp only [CollatzResearch.WordTrace]
  refine ⟨41115388775053690453842503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27410259183369126969228335 41115388775053690453842503)
  ·
    refine ⟨61673083162580535680763755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41115388775053690453842503 61673083162580535680763755)
    ·
      refine ⟨92509624743870803521145633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61673083162580535680763755 92509624743870803521145633)
      ·
        refine ⟨69382218557903102640859225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92509624743870803521145633 69382218557903102640859225)
        ·
          refine ⟨52036663918427326980644419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69382218557903102640859225 52036663918427326980644419)
          ·
            refine ⟨78054995877640990470966629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52036663918427326980644419 78054995877640990470966629)
            ·
              refine ⟨14635311727057685713306243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78054995877640990470966629 14635311727057685713306243)
              ·
                refine ⟨21952967590586528569959365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14635311727057685713306243 21952967590586528569959365)
                ·
                  refine ⟨4116181423234974106867381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21952967590586528569959365 4116181423234974106867381)
                  ·
                    refine ⟨385892008428278822518817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4116181423234974106867381 385892008428278822518817)
                    ·
                      rfl

theorem cell22_1127283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 5].length) (baseStart_1127283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127283 prefixEnd_1127283 := by exact prefixLift 1127283
  have htrace : WordTrace (prefixWord ++ tailWord_1127283) baseStart_1127283 baseEnd_1127283 := by
    simpa [prefixWord, tailWord_1127283, baseEnd_1127283] using wordTrace_append hprefix tailTrace_1127283
  have hstable : (prefixWord ++ tailWord_1127283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127283).length < 2 ^ (prefixWord ++ tailWord_1127283).sum := by decide
  have hdescent : baseEnd_1127283 < baseStart_1127283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127285 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 7]
def baseStart_1127285 : Nat := 118140960795 + 1127285 * 2 ^ 59
def prefixEnd_1127285 : Nat := 4983230072969 + 3 ^ 40 * 1127285 * 2
def baseEnd_1127285 : Nat := 128630897689717161322937

theorem tailTrace_1127285 : CollatzResearch.WordTrace tailWord_1127285 prefixEnd_1127285 128630897689717161322937 := by
  unfold tailWord_1127285
  simp only [CollatzResearch.WordTrace]
  refine ⟨41115461721046444795415309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27410307814030963196943539 41115461721046444795415309)
  ·
    refine ⟨15418298145392416798280741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41115461721046444795415309 15418298145392416798280741)
    ·
      refine ⟨2890930902261078149677639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15418298145392416798280741 2890930902261078149677639)
      ·
        refine ⟨4336396353391617224516459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2890930902261078149677639 4336396353391617224516459)
        ·
          refine ⟨6504594530087425836774689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4336396353391617224516459 6504594530087425836774689)
          ·
            refine ⟨4878445897565569377581017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6504594530087425836774689 4878445897565569377581017)
            ·
              refine ⟨3658834423174177033185763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4878445897565569377581017 3658834423174177033185763)
              ·
                refine ⟨5488251634761265549778645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3658834423174177033185763 5488251634761265549778645)
                ·
                  refine ⟨128630897689717161322937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5488251634761265549778645 128630897689717161322937)
                  ·
                    rfl

theorem cell22_1127285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_1127285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127285 prefixEnd_1127285 := by exact prefixLift 1127285
  have htrace : WordTrace (prefixWord ++ tailWord_1127285) baseStart_1127285 baseEnd_1127285 := by
    simpa [prefixWord, tailWord_1127285, baseEnd_1127285] using wordTrace_append hprefix tailTrace_1127285
  have hstable : (prefixWord ++ tailWord_1127285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127285).length < 2 ^ (prefixWord ++ tailWord_1127285).sum := by decide
  have hdescent : baseEnd_1127285 < baseStart_1127285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127313 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 8]
def baseStart_1127313 : Nat := 118140960795 + 1127313 * 2 ^ 59
def prefixEnd_1127313 : Nat := 4983230072969 + 3 ^ 40 * 1127313 * 2
def baseEnd_1127313 : Nat := 128634092680456248089575

theorem tailTrace_1127313 : CollatzResearch.WordTrace tailWord_1127313 prefixEnd_1127313 128634092680456248089575 := by
  unfold tailWord_1127313
  simp only [CollatzResearch.WordTrace]
  refine ⟨41116482964945005577434593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27410988643296670384956395 41116482964945005577434593)
  ·
    refine ⟨30837362223708754183075945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41116482964945005577434593 30837362223708754183075945)
    ·
      refine ⟨23128021667781565637306959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30837362223708754183075945 23128021667781565637306959)
      ·
        refine ⟨34692032501672348455960439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23128021667781565637306959 34692032501672348455960439)
        ·
          refine ⟨52038048752508522683940659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34692032501672348455960439 52038048752508522683940659)
          ·
            refine ⟨78057073128762784025910989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52038048752508522683940659 78057073128762784025910989)
            ·
              refine ⟨29271402423286044009716621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78057073128762784025910989 29271402423286044009716621)
              ·
                refine ⟨10976775908732266503643733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29271402423286044009716621 10976775908732266503643733)
                ·
                  refine ⟨128634092680456248089575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10976775908732266503643733 128634092680456248089575)
                  ·
                    rfl

theorem cell22_1127313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_1127313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127313 prefixEnd_1127313 := by exact prefixLift 1127313
  have htrace : WordTrace (prefixWord ++ tailWord_1127313) baseStart_1127313 baseEnd_1127313 := by
    simpa [prefixWord, tailWord_1127313, baseEnd_1127313] using wordTrace_append hprefix tailTrace_1127313
  have hstable : (prefixWord ++ tailWord_1127313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127313).length < 2 ^ (prefixWord ++ tailWord_1127313).sum := by decide
  have hdescent : baseEnd_1127313 < baseStart_1127313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127315 : List Nat := [1, 1, 1, 2, 1, 2, 1, 8, 1, 4]
def baseStart_1127315 : Nat := 118140960795 + 1127315 * 2 ^ 59
def prefixEnd_1127315 : Nat := 4983230072969 + 3 ^ 40 * 1127315 * 2
def baseEnd_1127315 : Nat := 385902962682241405718719

theorem tailTrace_1127315 : CollatzResearch.WordTrace tailWord_1127315 prefixEnd_1127315 385902962682241405718719 := by
  unfold tailWord_1127315
  simp only [CollatzResearch.WordTrace]
  refine ⟨41116555910937759919007399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27411037273958506612671599 41116555910937759919007399)
  ·
    refine ⟨61674833866406639878511099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41116555910937759919007399 61674833866406639878511099)
    ·
      refine ⟨92512250799609959817766649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61674833866406639878511099 92512250799609959817766649)
      ·
        refine ⟨69384188099707469863324987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92512250799609959817766649 69384188099707469863324987)
        ·
          refine ⟨104076282149561204794987481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69384188099707469863324987 104076282149561204794987481)
          ·
            refine ⟨78057211612170903596240611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104076282149561204794987481 78057211612170903596240611)
            ·
              refine ⟨117085817418256355394360917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78057211612170903596240611 117085817418256355394360917)
              ·
                refine ⟨1372099422870191664777667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 117085817418256355394360917 1372099422870191664777667)
                ·
                  refine ⟨2058149134305287497166501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1372099422870191664777667 2058149134305287497166501)
                  ·
                    refine ⟨385902962682241405718719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2058149134305287497166501 385902962682241405718719)
                    ·
                      rfl

theorem cell22_1127315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 4].length) (baseStart_1127315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127315 prefixEnd_1127315 := by exact prefixLift 1127315
  have htrace : WordTrace (prefixWord ++ tailWord_1127315) baseStart_1127315 baseEnd_1127315 := by
    simpa [prefixWord, tailWord_1127315, baseEnd_1127315] using wordTrace_append hprefix tailTrace_1127315
  have hstable : (prefixWord ++ tailWord_1127315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127315).length < 2 ^ (prefixWord ++ tailWord_1127315).sum := by decide
  have hdescent : baseEnd_1127315 < baseStart_1127315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127364 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 6]
def baseStart_1127364 : Nat := 118140960795 + 1127364 * 2 ^ 59
def prefixEnd_1127364 : Nat := 4983230072969 + 3 ^ 40 * 1127364 * 2
def baseEnd_1127364 : Nat := 128639912127873870414523

theorem tailTrace_1127364 : CollatzResearch.WordTrace tailWord_1127364 prefixEnd_1127364 128639912127873870414523 := by
  unfold tailWord_1127364
  simp only [CollatzResearch.WordTrace]
  refine ⟨20559171543880120643770573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27412228725173494191694097 20559171543880120643770573)
  ·
    refine ⟨7709689328955045241413965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20559171543880120643770573 7709689328955045241413965)
    ·
      refine ⟨2891133498358141965530237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7709689328955045241413965 2891133498358141965530237)
      ·
        refine ⟨1084175061884303237073839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2891133498358141965530237 1084175061884303237073839)
        ·
          refine ⟨1626262592826454855610759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1084175061884303237073839 1626262592826454855610759)
          ·
            refine ⟨2439393889239682283416139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1626262592826454855610759 2439393889239682283416139)
            ·
              refine ⟨3659090833859523425124209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2439393889239682283416139 3659090833859523425124209)
              ·
                refine ⟨2744318125394642568843157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3659090833859523425124209 2744318125394642568843157)
                ·
                  refine ⟨128639912127873870414523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2744318125394642568843157 128639912127873870414523)
                  ·
                    rfl

theorem cell22_1127364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_1127364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127364 prefixEnd_1127364 := by exact prefixLift 1127364
  have htrace : WordTrace (prefixWord ++ tailWord_1127364) baseStart_1127364 baseEnd_1127364 := by
    simpa [prefixWord, tailWord_1127364, baseEnd_1127364] using wordTrace_append hprefix tailTrace_1127364
  have hstable : (prefixWord ++ tailWord_1127364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127364).length < 2 ^ (prefixWord ++ tailWord_1127364).sum := by decide
  have hdescent : baseEnd_1127364 < baseStart_1127364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127407 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 3, 3]
def baseStart_1127407 : Nat := 118140960795 + 1127407 * 2 ^ 59
def prefixEnd_1127407 : Nat := 4983230072969 + 3 ^ 40 * 1127407 * 2
def baseEnd_1127407 : Nat := 385934456162383832418437

theorem tailTrace_1127407 : CollatzResearch.WordTrace tailWord_1127407 prefixEnd_1127407 385934456162383832418437 := by
  unfold tailWord_1127407
  simp only [CollatzResearch.WordTrace]
  refine ⟨41119911426604459631356475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27413274284402973087570983 41119911426604459631356475)
  ·
    refine ⟨61679867139906689447034713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41119911426604459631356475 61679867139906689447034713)
    ·
      refine ⟨46259900354930017085276035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61679867139906689447034713 46259900354930017085276035)
      ·
        refine ⟨69389850532395025627914053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46259900354930017085276035 69389850532395025627914053)
        ·
          refine ⟨13010596974824067305233885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69389850532395025627914053 13010596974824067305233885)
          ·
            refine ⟨4878973865559025239462707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13010596974824067305233885 4878973865559025239462707)
            ·
              refine ⟨7318460798338537859194061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4878973865559025239462707 7318460798338537859194061)
              ·
                refine ⟨2744422799376951697197773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7318460798338537859194061 2744422799376951697197773)
                ·
                  refine ⟨1029158549766356886449165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2744422799376951697197773 1029158549766356886449165)
                  ·
                    refine ⟨385934456162383832418437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1029158549766356886449165 385934456162383832418437)
                    ·
                      rfl

theorem cell22_1127407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 3].length) (baseStart_1127407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127407 prefixEnd_1127407 := by exact prefixLift 1127407
  have htrace : WordTrace (prefixWord ++ tailWord_1127407) baseStart_1127407 baseEnd_1127407 := by
    simpa [prefixWord, tailWord_1127407, baseEnd_1127407] using wordTrace_append hprefix tailTrace_1127407
  have hstable : (prefixWord ++ tailWord_1127407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127407).length < 2 ^ (prefixWord ++ tailWord_1127407).sum := by decide
  have hdescent : baseEnd_1127407 < baseStart_1127407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127413 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1127413 : Nat := 118140960795 + 1127413 * 2 ^ 59
def prefixEnd_1127413 : Nat := 4983230072969 + 3 ^ 40 * 1127413 * 2
def baseEnd_1127413 : Nat := 385936510085001816768419

theorem tailTrace_1127413 : CollatzResearch.WordTrace tailWord_1127413 prefixEnd_1127413 385936510085001816768419 := by
  unfold tailWord_1127413
  simp only [CollatzResearch.WordTrace]
  refine ⟨41120130264582722656074893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27413420176388481770716595 41120130264582722656074893)
  ·
    refine ⟨15420048849218520996028085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41120130264582722656074893 15420048849218520996028085)
    ·
      refine ⟨1445629579614236343377633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15420048849218520996028085 1445629579614236343377633)
      ·
        refine ⟨1084222184710677257533225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1445629579614236343377633 1084222184710677257533225)
        ·
          refine ⟨813166638533007943149919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1084222184710677257533225 813166638533007943149919)
          ·
            refine ⟨1219749957799511914724879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813166638533007943149919 1219749957799511914724879)
            ·
              refine ⟨1829624936699267872087319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219749957799511914724879 1829624936699267872087319)
              ·
                refine ⟨2744437405048901808130979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829624936699267872087319 2744437405048901808130979)
                ·
                  refine ⟨4116656107573352712196469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2744437405048901808130979 4116656107573352712196469)
                  ·
                    refine ⟨385936510085001816768419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4116656107573352712196469 385936510085001816768419)
                    ·
                      rfl

theorem cell22_1127413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1127413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127413 prefixEnd_1127413 := by exact prefixLift 1127413
  have htrace : WordTrace (prefixWord ++ tailWord_1127413) baseStart_1127413 baseEnd_1127413 := by
    simpa [prefixWord, tailWord_1127413, baseEnd_1127413] using wordTrace_append hprefix tailTrace_1127413
  have hstable : (prefixWord ++ tailWord_1127413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127413).length < 2 ^ (prefixWord ++ tailWord_1127413).sum := by decide
  have hdescent : baseEnd_1127413 < baseStart_1127413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127458 : List Nat := [3, 3, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_1127458 : Nat := 118140960795 + 1127458 * 2 ^ 59
def prefixEnd_1127458 : Nat := 4983230072969 + 3 ^ 40 * 1127458 * 2
def baseEnd_1127458 : Nat := 385951914504636699393281

theorem tailTrace_1127458 : CollatzResearch.WordTrace tailWord_1127458 prefixEnd_1127458 385951914504636699393281 := by
  unfold tailWord_1127458
  simp only [CollatzResearch.WordTrace]
  refine ⟨10280442887354923835365757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27414514366279796894308685 10280442887354923835365757)
  ·
    refine ⟨3855166082758096438262159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10280442887354923835365757 3855166082758096438262159)
    ·
      refine ⟨5782749124137144657393239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3855166082758096438262159 5782749124137144657393239)
      ·
        refine ⟨8674123686205716986089859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5782749124137144657393239 8674123686205716986089859)
        ·
          refine ⟨13011185529308575479134789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8674123686205716986089859 13011185529308575479134789)
          ·
            refine ⟨2439597286745357902337773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13011185529308575479134789 2439597286745357902337773)
            ·
              refine ⟨914848982529509213376665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2439597286745357902337773 914848982529509213376665)
              ·
                refine ⟨686136736897131910032499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 914848982529509213376665 686136736897131910032499)
                ·
                  refine ⟨1029205105345697865048749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686136736897131910032499 1029205105345697865048749)
                  ·
                    refine ⟨385951914504636699393281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1029205105345697865048749 385951914504636699393281)
                    ·
                      rfl

theorem cell22_1127458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_1127458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127458 prefixEnd_1127458 := by exact prefixLift 1127458
  have htrace : WordTrace (prefixWord ++ tailWord_1127458) baseStart_1127458 baseEnd_1127458 := by
    simpa [prefixWord, tailWord_1127458, baseEnd_1127458] using wordTrace_append hprefix tailTrace_1127458
  have hstable : (prefixWord ++ tailWord_1127458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127458).length < 2 ^ (prefixWord ++ tailWord_1127458).sum := by decide
  have hdescent : baseEnd_1127458 < baseStart_1127458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127484 : List Nat := [2, 2, 2, 2, 2, 2, 3, 2, 1, 4]
def baseStart_1127484 : Nat := 118140960795 + 1127484 * 2 ^ 59
def prefixEnd_1127484 : Nat := 4983230072969 + 3 ^ 40 * 1127484 * 2
def baseEnd_1127484 : Nat := 385960814835981298243201

theorem tailTrace_1127484 : CollatzResearch.WordTrace tailWord_1127484 prefixEnd_1127484 385960814835981298243201 := by
  unfold tailWord_1127484
  simp only [CollatzResearch.WordTrace]
  refine ⟨20561359923662750890954753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27415146564883667854606337 20561359923662750890954753)
  ·
    refine ⟨15421019942747063168216065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20561359923662750890954753 15421019942747063168216065)
    ·
      refine ⟨11565764957060297376162049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15421019942747063168216065 11565764957060297376162049)
      ·
        refine ⟨8674323717795223032121537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11565764957060297376162049 8674323717795223032121537)
        ·
          refine ⟨6505742788346417274091153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8674323717795223032121537 6505742788346417274091153)
          ·
            refine ⟨4879307091259812955568365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6505742788346417274091153 4879307091259812955568365)
            ·
              refine ⟨1829740159222429858338137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4879307091259812955568365 1829740159222429858338137)
              ·
                refine ⟨1372305119416822393753603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1829740159222429858338137 1372305119416822393753603)
                ·
                  refine ⟨2058457679125233590630405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1372305119416822393753603 2058457679125233590630405)
                  ·
                    refine ⟨385960814835981298243201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2058457679125233590630405 385960814835981298243201)
                    ·
                      rfl

theorem cell22_1127484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_1127484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127484 prefixEnd_1127484 := by exact prefixLift 1127484
  have htrace : WordTrace (prefixWord ++ tailWord_1127484) baseStart_1127484 baseEnd_1127484 := by
    simpa [prefixWord, tailWord_1127484, baseEnd_1127484] using wordTrace_append hprefix tailTrace_1127484
  have hstable : (prefixWord ++ tailWord_1127484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127484).length < 2 ^ (prefixWord ++ tailWord_1127484).sum := by decide
  have hdescent : baseEnd_1127484 < baseStart_1127484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127497 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 4, 3]
def baseStart_1127497 : Nat := 118140960795 + 1127497 * 2 ^ 59
def prefixEnd_1127497 : Nat := 4983230072969 + 3 ^ 40 * 1127497 * 2
def baseEnd_1127497 : Nat := 385965265001653597668161

theorem tailTrace_1127497 : CollatzResearch.WordTrace tailWord_1127497 prefixEnd_1127497 385965265001653597668161 := by
  unfold tailWord_1127497
  simp only [CollatzResearch.WordTrace]
  refine ⟨41123193996278405002132745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27415462664185603334755163 41123193996278405002132745)
  ·
    refine ⟨30842395497208803751599559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41123193996278405002132745 30842395497208803751599559)
    ·
      refine ⟨46263593245813205627399339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30842395497208803751599559 46263593245813205627399339)
      ·
        refine ⟨69395389868719808441099009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46263593245813205627399339 69395389868719808441099009)
        ·
          refine ⟨52046542401539856330824257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69395389868719808441099009 52046542401539856330824257)
          ·
            refine ⟨39034906801154892248118193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52046542401539856330824257 39034906801154892248118193)
            ·
              refine ⟨29276180100866169186088645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39034906801154892248118193 29276180100866169186088645)
              ·
                refine ⟨5489283768912406722391621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29276180100866169186088645 5489283768912406722391621)
                ·
                  refine ⟨1029240706671076260448429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5489283768912406722391621 1029240706671076260448429)
                  ·
                    refine ⟨385965265001653597668161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1029240706671076260448429 385965265001653597668161)
                    ·
                      rfl

theorem cell22_1127497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 3].length) (baseStart_1127497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127497 prefixEnd_1127497 := by exact prefixLift 1127497
  have htrace : WordTrace (prefixWord ++ tailWord_1127497) baseStart_1127497 baseEnd_1127497 := by
    simpa [prefixWord, tailWord_1127497, baseEnd_1127497] using wordTrace_append hprefix tailTrace_1127497
  have hstable : (prefixWord ++ tailWord_1127497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127497).length < 2 ^ (prefixWord ++ tailWord_1127497).sum := by decide
  have hdescent : baseEnd_1127497 < baseStart_1127497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127512 : List Nat := [2, 1, 2, 2, 1, 3, 1, 4, 2, 4]
def baseStart_1127512 : Nat := 118140960795 + 1127512 * 2 ^ 59
def prefixEnd_1127512 : Nat := 4983230072969 + 3 ^ 40 * 1127512 * 2
def baseEnd_1127512 : Nat := 385970399808198558543115

theorem tailTrace_1127512 : CollatzResearch.WordTrace tailWord_1127512 prefixEnd_1127512 385970399808198558543115 := by
  unfold tailWord_1127512
  simp only [CollatzResearch.WordTrace]
  refine ⟨20561870545612031281964395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27415827394149375042619193 20561870545612031281964395)
  ·
    refine ⟨30842805818418046922946593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20561870545612031281964395 30842805818418046922946593)
    ·
      refine ⟨23132104363813535192209945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30842805818418046922946593 23132104363813535192209945)
      ·
        refine ⟨17349078272860151394157459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23132104363813535192209945 17349078272860151394157459)
        ·
          refine ⟨26023617409290227091236189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17349078272860151394157459 26023617409290227091236189)
          ·
            refine ⟨9758856528483835159213571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26023617409290227091236189 9758856528483835159213571)
            ·
              refine ⟨14638284792725752738820357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9758856528483835159213571 14638284792725752738820357)
              ·
                refine ⟨2744678398636078638528817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14638284792725752738820357 2744678398636078638528817)
                ·
                  refine ⟨2058508798977058978896613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2744678398636078638528817 2058508798977058978896613)
                  ·
                    refine ⟨385970399808198558543115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2058508798977058978896613 385970399808198558543115)
                    ·
                      rfl

theorem cell22_1127512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_1127512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127512 prefixEnd_1127512 := by exact prefixLift 1127512
  have htrace : WordTrace (prefixWord ++ tailWord_1127512) baseStart_1127512 baseEnd_1127512 := by
    simpa [prefixWord, tailWord_1127512, baseEnd_1127512] using wordTrace_append hprefix tailTrace_1127512
  have hstable : (prefixWord ++ tailWord_1127512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127512).length < 2 ^ (prefixWord ++ tailWord_1127512).sum := by decide
  have hdescent : baseEnd_1127512 < baseStart_1127512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127527 : List Nat := [1, 1, 5, 1, 1, 3, 3, 7]
def baseStart_1127527 : Nat := 118140960795 + 1127527 * 2 ^ 59
def prefixEnd_1127527 : Nat := 4983230072969 + 3 ^ 40 * 1127527 * 2
def baseEnd_1127527 : Nat := 42886170512749279935341

theorem tailTrace_1127527 : CollatzResearch.WordTrace tailWord_1127527 prefixEnd_1127527 42886170512749279935341 := by
  unfold tailWord_1127527
  simp only [CollatzResearch.WordTrace]
  refine ⟨41124288186169720125724835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27416192124113146750483223 41124288186169720125724835)
  ·
    refine ⟨61686432279254580188587253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41124288186169720125724835 61686432279254580188587253)
    ·
      refine ⟨5783103026180116892680055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61686432279254580188587253 5783103026180116892680055)
      ·
        refine ⟨8674654539270175339020083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5783103026180116892680055 8674654539270175339020083)
        ·
          refine ⟨13011981808905263008530125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8674654539270175339020083 13011981808905263008530125)
          ·
            refine ⟨4879493178339473628198797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13011981808905263008530125 4879493178339473628198797)
            ·
              refine ⟨1829809941877302610574549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4879493178339473628198797 1829809941877302610574549)
              ·
                refine ⟨42886170512749279935341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1829809941877302610574549 42886170512749279935341)
                ·
                  rfl

theorem cell22_1127527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 7].length) (baseStart_1127527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127527 prefixEnd_1127527 := by exact prefixLift 1127527
  have htrace : WordTrace (prefixWord ++ tailWord_1127527) baseStart_1127527 baseEnd_1127527 := by
    simpa [prefixWord, tailWord_1127527, baseEnd_1127527] using wordTrace_append hprefix tailTrace_1127527
  have hstable : (prefixWord ++ tailWord_1127527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127527).length < 2 ^ (prefixWord ++ tailWord_1127527).sum := by decide
  have hdescent : baseEnd_1127527 < baseStart_1127527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127576 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 3, 3]
def baseStart_1127576 : Nat := 118140960795 + 1127576 * 2 ^ 59
def prefixEnd_1127576 : Nat := 4983230072969 + 3 ^ 40 * 1127576 * 2
def baseEnd_1127576 : Nat := 385992308316123724942919

theorem tailTrace_1127576 : CollatzResearch.WordTrace tailWord_1127576 prefixEnd_1127576 385992308316123724942919 := by
  unfold tailWord_1127576
  simp only [CollatzResearch.WordTrace]
  refine ⟨20563037681496100747129291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27417383575328134329505721 20563037681496100747129291)
  ·
    refine ⟨30844556522244151120693937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20563037681496100747129291 30844556522244151120693937)
    ·
      refine ⟨23133417391683113340520453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30844556522244151120693937 23133417391683113340520453)
      ·
        refine ⟨4337515760940583751347585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23133417391683113340520453 4337515760940583751347585)
        ·
          refine ⟨3253136820705437813510689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4337515760940583751347585 3253136820705437813510689)
          ·
            refine ⟨2439852615529078360133017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3253136820705437813510689 2439852615529078360133017)
            ·
              refine ⟨1829889461646808770099763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2439852615529078360133017 1829889461646808770099763)
              ·
                refine ⟨2744834192470213155149645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829889461646808770099763 2744834192470213155149645)
                ·
                  refine ⟨1029312822176329933181117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2744834192470213155149645 1029312822176329933181117)
                  ·
                    refine ⟨385992308316123724942919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1029312822176329933181117 385992308316123724942919)
                    ·
                      rfl

theorem cell22_1127576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_1127576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127576 prefixEnd_1127576 := by exact prefixLift 1127576
  have htrace : WordTrace (prefixWord ++ tailWord_1127576) baseStart_1127576 baseEnd_1127576 := by
    simpa [prefixWord, tailWord_1127576, baseEnd_1127576] using wordTrace_append hprefix tailTrace_1127576
  have hstable : (prefixWord ++ tailWord_1127576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127576).length < 2 ^ (prefixWord ++ tailWord_1127576).sum := by decide
  have hdescent : baseEnd_1127576 < baseStart_1127576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127647 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 3, 6]
def baseStart_1127647 : Nat := 118140960795 + 1127647 * 2 ^ 59
def prefixEnd_1127647 : Nat := 4983230072969 + 3 ^ 40 * 1127647 * 2
def baseEnd_1127647 : Nat := 386016613067103206417701

theorem tailTrace_1127647 : CollatzResearch.WordTrace tailWord_1127647 prefixEnd_1127647 386016613067103206417701 := by
  unfold tailWord_1127647
  simp only [CollatzResearch.WordTrace]
  refine ⟨41128664945734980620093195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27419109963823320413395463 41128664945734980620093195)
  ·
    refine ⟨61692997418602470930139793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41128664945734980620093195 61692997418602470930139793)
    ·
      refine ⟨46269748063951853197604845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61692997418602470930139793 46269748063951853197604845)
      ·
        refine ⟨17351155523981944949101817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46269748063951853197604845 17351155523981944949101817)
        ·
          refine ⟨13013366642986458711826363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17351155523981944949101817 13013366642986458711826363)
          ·
            refine ⟨19520049964479688067739545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13013366642986458711826363 19520049964479688067739545)
            ·
              refine ⟨14640037473359766050804659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19520049964479688067739545 14640037473359766050804659)
              ·
                refine ⟨21960056210039649076206989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14640037473359766050804659 21960056210039649076206989)
                ·
                  refine ⟨8235021078764868403577621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21960056210039649076206989 8235021078764868403577621)
                  ·
                    refine ⟨386016613067103206417701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8235021078764868403577621 386016613067103206417701)
                    ·
                      rfl

theorem cell22_1127647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_1127647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127647 prefixEnd_1127647 := by exact prefixLift 1127647
  have htrace : WordTrace (prefixWord ++ tailWord_1127647) baseStart_1127647 baseEnd_1127647 := by
    simpa [prefixWord, tailWord_1127647, baseEnd_1127647] using wordTrace_append hprefix tailTrace_1127647
  have hstable : (prefixWord ++ tailWord_1127647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127647).length < 2 ^ (prefixWord ++ tailWord_1127647).sum := by decide
  have hdescent : baseEnd_1127647 < baseStart_1127647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127653 : List Nat := [1, 3, 1, 4, 3, 2, 1, 2, 1, 4]
def baseStart_1127653 : Nat := 118140960795 + 1127653 * 2 ^ 59
def prefixEnd_1127653 : Nat := 4983230072969 + 3 ^ 40 * 1127653 * 2
def baseEnd_1127653 : Nat := 386018666989721190767683

theorem tailTrace_1127653 : CollatzResearch.WordTrace tailWord_1127653 prefixEnd_1127653 386018666989721190767683 := by
  unfold tailWord_1127653
  simp only [CollatzResearch.WordTrace]
  refine ⟨41128883783713243644811613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27419255855808829096541075 41128883783713243644811613)
  ·
    refine ⟨15423331418892466366804355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41128883783713243644811613 15423331418892466366804355)
    ·
      refine ⟨23134997128338699550206533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15423331418892466366804355 23134997128338699550206533)
      ·
        refine ⟨4337811961563506165663725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23134997128338699550206533 4337811961563506165663725)
        ·
          refine ⟨1626679485586314812123897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4337811961563506165663725 1626679485586314812123897)
          ·
            refine ⟨1220009614189736109092923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1626679485586314812123897 1220009614189736109092923)
            ·
              refine ⟨1830014421284604163639385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220009614189736109092923 1830014421284604163639385)
              ·
                refine ⟨1372510815963453122729539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1830014421284604163639385 1372510815963453122729539)
                ·
                  refine ⟨2058766223945179684094309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1372510815963453122729539 2058766223945179684094309)
                  ·
                    refine ⟨386018666989721190767683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2058766223945179684094309 386018666989721190767683)
                    ·
                      rfl

theorem cell22_1127653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_1127653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127653 prefixEnd_1127653 := by exact prefixLift 1127653
  have htrace : WordTrace (prefixWord ++ tailWord_1127653) baseStart_1127653 baseEnd_1127653 := by
    simpa [prefixWord, tailWord_1127653, baseEnd_1127653] using wordTrace_append hprefix tailTrace_1127653
  have hstable : (prefixWord ++ tailWord_1127653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127653).length < 2 ^ (prefixWord ++ tailWord_1127653).sum := by decide
  have hdescent : baseEnd_1127653 < baseStart_1127653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127666 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_1127666 : Nat := 118140960795 + 1127666 * 2 ^ 59
def prefixEnd_1127666 : Nat := 4983230072969 + 3 ^ 40 * 1127666 * 2
def baseEnd_1127666 : Nat := 386023117155393490192643

theorem tailTrace_1127666 : CollatzResearch.WordTrace tailWord_1127666 prefixEnd_1127666 386023117155393490192643 := by
  unfold tailWord_1127666
  simp only [CollatzResearch.WordTrace]
  refine ⟨10282339483166536716258713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27419571955110764576689901 10282339483166536716258713)
  ·
    refine ⟨7711754612374902537194035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10282339483166536716258713 7711754612374902537194035)
    ·
      refine ⟨11567631918562353805791053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7711754612374902537194035 11567631918562353805791053)
      ·
        refine ⟨4337861969460882677171645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11567631918562353805791053 4337861969460882677171645)
        ·
          refine ⟨1626698238547831003939367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4337861969460882677171645 1626698238547831003939367)
          ·
            refine ⟨2440047357821746505909051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1626698238547831003939367 2440047357821746505909051)
            ·
              refine ⟨3660071036732619758863577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2440047357821746505909051 3660071036732619758863577)
              ·
                refine ⟨2745053277549464819147683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3660071036732619758863577 2745053277549464819147683)
                ·
                  refine ⟨4117579916324197228721525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2745053277549464819147683 4117579916324197228721525)
                  ·
                    refine ⟨386023117155393490192643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4117579916324197228721525 386023117155393490192643)
                    ·
                      rfl

theorem cell22_1127666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_1127666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127666 prefixEnd_1127666 := by exact prefixLift 1127666
  have htrace : WordTrace (prefixWord ++ tailWord_1127666) baseStart_1127666 baseEnd_1127666 := by
    simpa [prefixWord, tailWord_1127666, baseEnd_1127666] using wordTrace_append hprefix tailTrace_1127666
  have hstable : (prefixWord ++ tailWord_1127666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127666).length < 2 ^ (prefixWord ++ tailWord_1127666).sum := by decide
  have hdescent : baseEnd_1127666 < baseStart_1127666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127707 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 9]
def baseStart_1127707 : Nat := 118140960795 + 1127707 * 2 ^ 59
def prefixEnd_1127707 : Nat := 4983230072969 + 3 ^ 40 * 1127707 * 2
def baseEnd_1127707 : Nat := 128679050764427683305839

theorem tailTrace_1127707 : CollatzResearch.WordTrace tailWord_1127707 prefixEnd_1127707 128679050764427683305839 := by
  unfold tailWord_1127707
  simp only [CollatzResearch.WordTrace]
  refine ⟨41130853325517610867277375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27420568883678407244851583 41130853325517610867277375)
  ·
    refine ⟨61696279988276416300916063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41130853325517610867277375 61696279988276416300916063)
    ·
      refine ⟨92544419982414624451374095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61696279988276416300916063 92544419982414624451374095)
      ·
        refine ⟨138816629973621936677061143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92544419982414624451374095 138816629973621936677061143)
        ·
          refine ⟨208224944960432905015591715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138816629973621936677061143 208224944960432905015591715)
          ·
            refine ⟨312337417440649357523387573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208224944960432905015591715 312337417440649357523387573)
            ·
              refine ⟨29281632885060877267817585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 312337417440649357523387573 29281632885060877267817585)
              ·
                refine ⟨21961224663795657950863189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29281632885060877267817585 21961224663795657950863189)
                ·
                  refine ⟨128679050764427683305839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21961224663795657950863189 128679050764427683305839)
                  ·
                    rfl

theorem cell22_1127707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 9].length) (baseStart_1127707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127707 prefixEnd_1127707 := by exact prefixLift 1127707
  have htrace : WordTrace (prefixWord ++ tailWord_1127707) baseStart_1127707 baseEnd_1127707 := by
    simpa [prefixWord, tailWord_1127707, baseEnd_1127707] using wordTrace_append hprefix tailTrace_1127707
  have hstable : (prefixWord ++ tailWord_1127707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127707).length < 2 ^ (prefixWord ++ tailWord_1127707).sum := by decide
  have hdescent : baseEnd_1127707 < baseStart_1127707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127728 : List Nat := [2, 1, 1, 1, 2, 2, 6, 3, 1, 3]
def baseStart_1127728 : Nat := 118140960795 + 1127728 * 2 ^ 59
def prefixEnd_1127728 : Nat := 4983230072969 + 3 ^ 40 * 1127728 * 2
def baseEnd_1127728 : Nat := 386044341022445995142453

theorem tailTrace_1127728 : CollatzResearch.WordTrace tailWord_1127728 prefixEnd_1127728 386044341022445995142453 := by
  unfold tailWord_1127728
  simp only [CollatzResearch.WordTrace]
  refine ⟨20565809629220765726895919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27421079505627687635861225 20565809629220765726895919)
  ·
    refine ⟨30848714443831148590343879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20565809629220765726895919 30848714443831148590343879)
    ·
      refine ⟨46273071665746722885515819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30848714443831148590343879 46273071665746722885515819)
      ·
        refine ⟨69409607498620084328273729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46273071665746722885515819 69409607498620084328273729)
        ·
          refine ⟨52057205623965063246205297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69409607498620084328273729 52057205623965063246205297)
          ·
            refine ⟨39042904217973797434653973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52057205623965063246205297 39042904217973797434653973)
            ·
              refine ⟨1830136135217521754749405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39042904217973797434653973 1830136135217521754749405)
              ·
                refine ⟨686301050706570658031027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1830136135217521754749405 686301050706570658031027)
                ·
                  refine ⟨1029451576059855987046541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686301050706570658031027 1029451576059855987046541)
                  ·
                    refine ⟨386044341022445995142453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1029451576059855987046541 386044341022445995142453)
                    ·
                      rfl

theorem cell22_1127728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 1, 3].length) (baseStart_1127728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127728 prefixEnd_1127728 := by exact prefixLift 1127728
  have htrace : WordTrace (prefixWord ++ tailWord_1127728) baseStart_1127728 baseEnd_1127728 := by
    simpa [prefixWord, tailWord_1127728, baseEnd_1127728] using wordTrace_append hprefix tailTrace_1127728
  have hstable : (prefixWord ++ tailWord_1127728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127728).length < 2 ^ (prefixWord ++ tailWord_1127728).sum := by decide
  have hdescent : baseEnd_1127728 < baseStart_1127728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127734 : List Nat := [5, 1, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_1127734 : Nat := 118140960795 + 1127734 * 2 ^ 59
def prefixEnd_1127734 : Nat := 4983230072969 + 3 ^ 40 * 1127734 * 2
def baseEnd_1127734 : Nat := 386046394945063979492435

theorem tailTrace_1127734 : CollatzResearch.WordTrace tailWord_1127734 prefixEnd_1127734 386046394945063979492435 := by
  unfold tailWord_1127734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2570739881026237154906891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27421225397613196319006837 2570739881026237154906891)
  ·
    refine ⟨3856109821539355732360337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2570739881026237154906891 3856109821539355732360337)
    ·
      refine ⟨2892082366154516799270253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3856109821539355732360337 2892082366154516799270253)
      ·
        refine ⟨1084530887307943799726345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2892082366154516799270253 1084530887307943799726345)
        ·
          refine ⟨813398165480957849794759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1084530887307943799726345 813398165480957849794759)
          ·
            refine ⟨1220097248221436774692139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813398165480957849794759 1220097248221436774692139)
            ·
              refine ⟨1830145872332155162038209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220097248221436774692139 1830145872332155162038209)
              ·
                refine ⟨1372609404249116371528657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1830145872332155162038209 1372609404249116371528657)
                ·
                  refine ⟨1029457053186837278646493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1372609404249116371528657 1029457053186837278646493)
                  ·
                    refine ⟨386046394945063979492435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1029457053186837278646493 386046394945063979492435)
                    ·
                      rfl

theorem cell22_1127734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_1127734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127734 prefixEnd_1127734 := by exact prefixLift 1127734
  have htrace : WordTrace (prefixWord ++ tailWord_1127734) baseStart_1127734 baseEnd_1127734 := by
    simpa [prefixWord, tailWord_1127734, baseEnd_1127734] using wordTrace_append hprefix tailTrace_1127734
  have hstable : (prefixWord ++ tailWord_1127734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127734).length < 2 ^ (prefixWord ++ tailWord_1127734).sum := by decide
  have hdescent : baseEnd_1127734 < baseStart_1127734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127745 : List Nat := [1, 2, 5, 2, 1, 1, 2, 4, 1, 3]
def baseStart_1127745 : Nat := 118140960795 + 1127745 * 2 ^ 59
def prefixEnd_1127745 : Nat := 4983230072969 + 3 ^ 40 * 1127745 * 2
def baseEnd_1127745 : Nat := 386050160469863617467401

theorem tailTrace_1127745 : CollatzResearch.WordTrace tailWord_1127745 prefixEnd_1127745 386050160469863617467401 := by
  unfold tailWord_1127745
  simp only [CollatzResearch.WordTrace]
  refine ⟨41132239299379943357160689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27421492866253295571440459 41132239299379943357160689)
  ·
    refine ⟨30849179474534957517870517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41132239299379943357160689 30849179474534957517870517)
    ·
      refine ⟨2892110575737652267300361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30849179474534957517870517 2892110575737652267300361)
      ·
        refine ⟨2169082931803239200475271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2892110575737652267300361 2169082931803239200475271)
        ·
          refine ⟨3253624397704858800712907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2169082931803239200475271 3253624397704858800712907)
          ·
            refine ⟨4880436596557288201069361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253624397704858800712907 4880436596557288201069361)
            ·
              refine ⟨3660327447417966150802021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4880436596557288201069361 3660327447417966150802021)
              ·
                refine ⟨686311396390868653275379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3660327447417966150802021 686311396390868653275379)
                ·
                  refine ⟨1029467094586302979913069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686311396390868653275379 1029467094586302979913069)
                  ·
                    refine ⟨386050160469863617467401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1029467094586302979913069 386050160469863617467401)
                    ·
                      rfl

theorem cell22_1127745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_1127745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127745 prefixEnd_1127745 := by exact prefixLift 1127745
  have htrace : WordTrace (prefixWord ++ tailWord_1127745) baseStart_1127745 baseEnd_1127745 := by
    simpa [prefixWord, tailWord_1127745, baseEnd_1127745] using wordTrace_append hprefix tailTrace_1127745
  have hstable : (prefixWord ++ tailWord_1127745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127745).length < 2 ^ (prefixWord ++ tailWord_1127745).sum := by decide
  have hdescent : baseEnd_1127745 < baseStart_1127745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127754 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_1127754 : Nat := 118140960795 + 1127754 * 2 ^ 59
def prefixEnd_1127754 : Nat := 4983230072969 + 3 ^ 40 * 1127754 * 2
def baseEnd_1127754 : Nat := 386053241353790593992373

theorem tailTrace_1127754 : CollatzResearch.WordTrace tailWord_1127754 prefixEnd_1127754 386053241353790593992373 := by
  unfold tailWord_1127754
  simp only [CollatzResearch.WordTrace]
  refine ⟨10283141889086834473559579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27421711704231558596158877 10283141889086834473559579)
  ·
    refine ⟨15424712833630251710339369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10283141889086834473559579 15424712833630251710339369)
    ·
      refine ⟨11568534625222688782754527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15424712833630251710339369 11568534625222688782754527)
      ·
        refine ⟨17352801937834033174131791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11568534625222688782754527 17352801937834033174131791)
        ·
          refine ⟨26029202906751049761197687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17352801937834033174131791 26029202906751049761197687)
          ·
            refine ⟨39043804360126574641796531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26029202906751049761197687 39043804360126574641796531)
            ·
              refine ⟨58565706540189861962694797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39043804360126574641796531 58565706540189861962694797)
              ·
                refine ⟨21962139952571198236010549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58565706540189861962694797 21962139952571198236010549)
                ·
                  refine ⟨2058950620553549834625989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21962139952571198236010549 2058950620553549834625989)
                  ·
                    refine ⟨386053241353790593992373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2058950620553549834625989 386053241353790593992373)
                    ·
                      rfl

theorem cell22_1127754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_1127754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127754 prefixEnd_1127754 := by exact prefixLift 1127754
  have htrace : WordTrace (prefixWord ++ tailWord_1127754) baseStart_1127754 baseEnd_1127754 := by
    simpa [prefixWord, tailWord_1127754, baseEnd_1127754] using wordTrace_append hprefix tailTrace_1127754
  have hstable : (prefixWord ++ tailWord_1127754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127754).length < 2 ^ (prefixWord ++ tailWord_1127754).sum := by decide
  have hdescent : baseEnd_1127754 < baseStart_1127754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127769 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 6]
def baseStart_1127769 : Nat := 118140960795 + 1127769 * 2 ^ 59
def prefixEnd_1127769 : Nat := 4983230072969 + 3 ^ 40 * 1127769 * 2
def baseEnd_1127769 : Nat := 128686125386778518289109

theorem tailTrace_1127769 : CollatzResearch.WordTrace tailWord_1127769 prefixEnd_1127769 128686125386778518289109 := by
  unfold tailWord_1127769
  simp only [CollatzResearch.WordTrace]
  refine ⟨41133114651292995456034361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27422076434195330304022907 41133114651292995456034361)
  ·
    refine ⟨30849835988469746592025771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41133114651292995456034361 30849835988469746592025771)
    ·
      refine ⟨46274753982704619888038657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30849835988469746592025771 46274753982704619888038657)
      ·
        refine ⟨34706065487028464916028993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46274753982704619888038657 34706065487028464916028993)
        ·
          refine ⟨26029549115271348687021745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34706065487028464916028993 26029549115271348687021745)
          ·
            refine ⟨19522161836453511515266309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26029549115271348687021745 19522161836453511515266309)
            ·
              refine ⟨3660405344335033409112433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19522161836453511515266309 3660405344335033409112433)
              ·
                refine ⟨2745304008251275056834325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3660405344335033409112433 2745304008251275056834325)
                ·
                  refine ⟨128686125386778518289109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2745304008251275056834325 128686125386778518289109)
                  ·
                    rfl

theorem cell22_1127769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 6].length) (baseStart_1127769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127769 prefixEnd_1127769 := by exact prefixLift 1127769
  have htrace : WordTrace (prefixWord ++ tailWord_1127769) baseStart_1127769 baseEnd_1127769 := by
    simpa [prefixWord, tailWord_1127769, baseEnd_1127769] using wordTrace_append hprefix tailTrace_1127769
  have hstable : (prefixWord ++ tailWord_1127769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127769).length < 2 ^ (prefixWord ++ tailWord_1127769).sum := by decide
  have hdescent : baseEnd_1127769 < baseStart_1127769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127801 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 4, 3]
def baseStart_1127801 : Nat := 118140960795 + 1127801 * 2 ^ 59
def prefixEnd_1127801 : Nat := 4983230072969 + 3 ^ 40 * 1127801 * 2
def baseEnd_1127801 : Nat := 386069330414298138067229

theorem tailTrace_1127801 : CollatzResearch.WordTrace tailWord_1127801 prefixEnd_1127801 386069330414298138067229 := by
  unfold tailWord_1127801
  simp only [CollatzResearch.WordTrace]
  refine ⟨41134281787177064921199257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27422854524784709947466171 41134281787177064921199257)
  ·
    refine ⟨30850711340382798690899443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41134281787177064921199257 30850711340382798690899443)
    ·
      refine ⟨46276067010574198036349165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30850711340382798690899443 46276067010574198036349165)
      ·
        refine ⟨17353525128965324263630937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46276067010574198036349165 17353525128965324263630937)
        ·
          refine ⟨13015143846723993197723203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17353525128965324263630937 13015143846723993197723203)
          ·
            refine ⟨19522715770085989796584805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13015143846723993197723203 19522715770085989796584805)
            ·
              refine ⟨3660509206891123086859651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19522715770085989796584805 3660509206891123086859651)
              ·
                refine ⟨5490763810336684630289477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3660509206891123086859651 5490763810336684630289477)
                ·
                  refine ⟨1029518214438128368179277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5490763810336684630289477 1029518214438128368179277)
                  ·
                    refine ⟨386069330414298138067229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1029518214438128368179277 386069330414298138067229)
                    ·
                      rfl

theorem cell22_1127801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 3].length) (baseStart_1127801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127801 prefixEnd_1127801 := by exact prefixLift 1127801
  have htrace : WordTrace (prefixWord ++ tailWord_1127801) baseStart_1127801 baseEnd_1127801 := by
    simpa [prefixWord, tailWord_1127801, baseEnd_1127801] using wordTrace_append hprefix tailTrace_1127801
  have hstable : (prefixWord ++ tailWord_1127801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127801).length < 2 ^ (prefixWord ++ tailWord_1127801).sum := by decide
  have hdescent : baseEnd_1127801 < baseStart_1127801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127803 : List Nat := [1, 1, 1, 1, 1, 6, 5, 2, 4]
def baseStart_1127803 : Nat := 118140960795 + 1127803 * 2 ^ 59
def prefixEnd_1127803 : Nat := 4983230072969 + 3 ^ 40 * 1127803 * 2
def baseEnd_1127803 : Nat := 128690005018390266505741

theorem tailTrace_1127803 : CollatzResearch.WordTrace tailWord_1127803 prefixEnd_1127803 128690005018390266505741 := by
  unfold tailWord_1127803
  simp only [CollatzResearch.WordTrace]
  refine ⟨41134354733169819262772063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27422903155446546175181375 41134354733169819262772063)
  ·
    refine ⟨61701532099754728894158095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41134354733169819262772063 61701532099754728894158095)
    ·
      refine ⟨92552298149632093341237143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61701532099754728894158095 92552298149632093341237143)
      ·
        refine ⟨138828447224448140011855715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92552298149632093341237143 138828447224448140011855715)
        ·
          refine ⟨208242670836672210017783573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138828447224448140011855715 208242670836672210017783573)
          ·
            refine ⟨9761375195469009844583605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 208242670836672210017783573 9761375195469009844583605)
            ·
              refine ⟨915128924575219672929713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9761375195469009844583605 915128924575219672929713)
              ·
                refine ⟨686346693431414754697285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 915128924575219672929713 686346693431414754697285)
                ·
                  refine ⟨128690005018390266505741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 686346693431414754697285 128690005018390266505741)
                  ·
                    rfl

theorem cell22_1127803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 4].length) (baseStart_1127803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127803 prefixEnd_1127803 := by exact prefixLift 1127803
  have htrace : WordTrace (prefixWord ++ tailWord_1127803) baseStart_1127803 baseEnd_1127803 := by
    simpa [prefixWord, tailWord_1127803, baseEnd_1127803] using wordTrace_append hprefix tailTrace_1127803
  have hstable : (prefixWord ++ tailWord_1127803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127803).length < 2 ^ (prefixWord ++ tailWord_1127803).sum := by decide
  have hdescent : baseEnd_1127803 < baseStart_1127803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127822 : List Nat := [4, 1, 1, 4, 3, 1, 1, 2, 1, 4]
def baseStart_1127822 : Nat := 118140960795 + 1127822 * 2 ^ 59
def prefixEnd_1127822 : Nat := 4983230072969 + 3 ^ 40 * 1127822 * 2
def baseEnd_1127822 : Nat := 386076519143461083292165

theorem tailTrace_1127822 : CollatzResearch.WordTrace tailWord_1127822 prefixEnd_1127822 386076519143461083292165 := by
  unfold tailWord_1127822
  simp only [CollatzResearch.WordTrace]
  refine ⟨5141880965012623188464215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27423365146733990338475813 5141880965012623188464215)
  ·
    refine ⟨7712821447518934782696323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5141880965012623188464215 7712821447518934782696323)
    ·
      refine ⟨11569232171278402174044485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7712821447518934782696323 11569232171278402174044485)
      ·
        refine ⟨2169231032114700407633341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11569232171278402174044485 2169231032114700407633341)
        ·
          refine ⟨813461637043012652862503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2169231032114700407633341 813461637043012652862503)
          ·
            refine ⟨1220192455564518979293755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813461637043012652862503 1220192455564518979293755)
            ·
              refine ⟨1830288683346778468940633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220192455564518979293755 1830288683346778468940633)
              ·
                refine ⟨1372716512510083851705475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1830288683346778468940633 1372716512510083851705475)
                ·
                  refine ⟨2059074768765125777558213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1372716512510083851705475 2059074768765125777558213)
                  ·
                    refine ⟨386076519143461083292165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2059074768765125777558213 386076519143461083292165)
                    ·
                      rfl

theorem cell22_1127822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_1127822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127822 prefixEnd_1127822 := by exact prefixLift 1127822
  have htrace : WordTrace (prefixWord ++ tailWord_1127822) baseStart_1127822 baseEnd_1127822 := by
    simpa [prefixWord, tailWord_1127822, baseEnd_1127822] using wordTrace_append hprefix tailTrace_1127822
  have hstable : (prefixWord ++ tailWord_1127822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127822).length < 2 ^ (prefixWord ++ tailWord_1127822).sum := by decide
  have hdescent : baseEnd_1127822 < baseStart_1127822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127829 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_1127829 : Nat := 118140960795 + 1127829 * 2 ^ 59
def prefixEnd_1127829 : Nat := 4983230072969 + 3 ^ 40 * 1127829 * 2
def baseEnd_1127829 : Nat := 386078915386515398367143

theorem tailTrace_1127829 : CollatzResearch.WordTrace tailWord_1127829 prefixEnd_1127829 386078915386515398367143 := by
  unfold tailWord_1127829
  simp only [CollatzResearch.WordTrace]
  refine ⟨41135303031075625703218541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27423535354050417135479027 41135303031075625703218541)
  ·
    refine ⟨15425738636653359638706953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41135303031075625703218541 15425738636653359638706953)
    ·
      refine ⟨11569303977490019729030215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15425738636653359638706953 11569303977490019729030215)
      ·
        refine ⟨17353955966235029593545323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11569303977490019729030215 17353955966235029593545323)
        ·
          refine ⟨26030933949352544390317985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17353955966235029593545323 26030933949352544390317985)
          ·
            refine ⟨19523200462014408292738489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26030933949352544390317985 19523200462014408292738489)
            ·
              refine ⟨14642400346510806219553867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19523200462014408292738489 14642400346510806219553867)
              ·
                refine ⟨21963600519766209329330801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14642400346510806219553867 21963600519766209329330801)
                ·
                  refine ⟨16472700389824656996998101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21963600519766209329330801 16472700389824656996998101)
                  ·
                    refine ⟨386078915386515398367143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16472700389824656996998101 386078915386515398367143)
                    ·
                      rfl

theorem cell22_1127829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_1127829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127829 prefixEnd_1127829 := by exact prefixLift 1127829
  have htrace : WordTrace (prefixWord ++ tailWord_1127829) baseStart_1127829 baseEnd_1127829 := by
    simpa [prefixWord, tailWord_1127829, baseEnd_1127829] using wordTrace_append hprefix tailTrace_1127829
  have hstable : (prefixWord ++ tailWord_1127829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127829).length < 2 ^ (prefixWord ++ tailWord_1127829).sum := by decide
  have hdescent : baseEnd_1127829 < baseStart_1127829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127848 : List Nat := [2, 1, 6, 1, 3, 9]
def baseStart_1127848 : Nat := 118140960795 + 1127848 * 2 ^ 59
def prefixEnd_1127848 : Nat := 4983230072969 + 3 ^ 40 * 1127848 * 2
def baseEnd_1127848 : Nat := 4766486660182786199285

theorem tailTrace_1127848 : CollatzResearch.WordTrace tailWord_1127848 prefixEnd_1127848 4766486660182786199285 := by
  unfold tailWord_1127848
  simp only [CollatzResearch.WordTrace]
  refine ⟨20567998009003395974080099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27423997345337861298773465 20567998009003395974080099)
  ·
    refine ⟨30851997013505093961120149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20567998009003395974080099 30851997013505093961120149)
    ·
      refine ⟨1446187360008051279427507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30851997013505093961120149 1446187360008051279427507)
      ·
        refine ⟨2169281040012076919141261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1446187360008051279427507 2169281040012076919141261)
        ·
          refine ⟨813480390004528844677973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2169281040012076919141261 813480390004528844677973)
          ·
            refine ⟨4766486660182786199285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 813480390004528844677973 4766486660182786199285)
            ·
              rfl

theorem cell22_1127848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 9].length) (baseStart_1127848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1127848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1127848 prefixEnd_1127848 := by exact prefixLift 1127848
  have htrace : WordTrace (prefixWord ++ tailWord_1127848) baseStart_1127848 baseEnd_1127848 := by
    simpa [prefixWord, tailWord_1127848, baseEnd_1127848] using wordTrace_append hprefix tailTrace_1127848
  have hstable : (prefixWord ++ tailWord_1127848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127848).length < 2 ^ (prefixWord ++ tailWord_1127848).sum := by decide
  have hdescent : baseEnd_1127848 < baseStart_1127848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
