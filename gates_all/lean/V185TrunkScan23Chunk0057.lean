import V185TrunkScan23Chunk0056

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_336630 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3]
def baseStart_336630 : Nat := 118140960795 + 336630 * 2 ^ 59
def prefixEnd_336630 : Nat := 4983230072969 + 3 ^ 40 * 336630 * 2
def baseEnd_336630 : Nat := 172852992723123167276873

theorem tailTrace_336630 : CollatzResearch.WordTrace tailWord_336630 prefixEnd_336630 172852992723123167276873 := by
  unfold tailWord_336630
  simp only [CollatzResearch.WordTrace]
  refine ⟨767369048153404791996959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8185269846969651114634229 767369048153404791996959)
  ·
    refine ⟨1151053572230107187995439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 767369048153404791996959 1151053572230107187995439)
    ·
      refine ⟨1726580358345160781993159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1151053572230107187995439 1726580358345160781993159)
      ·
        refine ⟨2589870537517741172989739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1726580358345160781993159 2589870537517741172989739)
        ·
          refine ⟨3884805806276611759484609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2589870537517741172989739 3884805806276611759484609)
          ·
            refine ⟨2913604354707458819613457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3884805806276611759484609 2913604354707458819613457)
            ·
              refine ⟨2185203266030594114710093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2913604354707458819613457 2185203266030594114710093)
              ·
                refine ⟨819451224761472793016285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2185203266030594114710093 819451224761472793016285)
                ·
                  refine ⟨307294209285552297381107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819451224761472793016285 307294209285552297381107)
                  ·
                    refine ⟨460941313928328446071661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 307294209285552297381107 460941313928328446071661)
                    ·
                      refine ⟨172852992723123167276873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 460941313928328446071661 172852992723123167276873)
                      ·
                        rfl

theorem cell23_336630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_336630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336630 prefixEnd_336630 := by exact prefixLift 336630
  have htrace : WordTrace (prefixWord ++ tailWord_336630) baseStart_336630 baseEnd_336630 := by
    simpa [prefixWord, tailWord_336630, baseEnd_336630] using wordTrace_append hprefix tailTrace_336630
  have hstable : (prefixWord ++ tailWord_336630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336630).length < 2 ^ (prefixWord ++ tailWord_336630).sum := by decide
  have hdescent : baseEnd_336630 < baseStart_336630 := by decide
  rcases family_descends (prefixWord ++ tailWord_336630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336721 : List Nat := [1, 2, 2, 1, 6, 2, 1, 3, 1, 2, 2]
def baseStart_336721 : Nat := 118140960795 + 336721 * 2 ^ 59
def prefixEnd_336721 : Nat := 4983230072969 + 3 ^ 40 * 336721 * 2
def baseEnd_336721 : Nat := 172899719462682311238955

theorem tailTrace_336721 : CollatzResearch.WordTrace tailWord_336721 prefixEnd_336721 172899719462682311238955 := by
  unfold tailWord_336721
  simp only [CollatzResearch.WordTrace]
  refine ⟨12281223813124799213514017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8187482542083199475676011 12281223813124799213514017)
  ·
    refine ⟨9210917859843599410135513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12281223813124799213514017 9210917859843599410135513)
    ·
      refine ⟨6908188394882699557601635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9210917859843599410135513 6908188394882699557601635)
      ·
        refine ⟨10362282592324049336402453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6908188394882699557601635 10362282592324049336402453)
        ·
          refine ⟨485731996515189812643865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10362282592324049336402453 485731996515189812643865)
          ·
            refine ⟨364298997386392359482899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 485731996515189812643865 364298997386392359482899)
            ·
              refine ⟨546448496079588539224349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364298997386392359482899 546448496079588539224349)
              ·
                refine ⟨204918186029845702209131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 546448496079588539224349 204918186029845702209131)
                ·
                  refine ⟨307377279044768553313697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204918186029845702209131 307377279044768553313697)
                  ·
                    refine ⟨230532959283576414985273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 307377279044768553313697 230532959283576414985273)
                    ·
                      refine ⟨172899719462682311238955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 230532959283576414985273 172899719462682311238955)
                      ·
                        rfl

theorem cell23_336721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 1, 2, 2].length) (baseStart_336721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336721 prefixEnd_336721 := by exact prefixLift 336721
  have htrace : WordTrace (prefixWord ++ tailWord_336721) baseStart_336721 baseEnd_336721 := by
    simpa [prefixWord, tailWord_336721, baseEnd_336721] using wordTrace_append hprefix tailTrace_336721
  have hstable : (prefixWord ++ tailWord_336721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336721).length < 2 ^ (prefixWord ++ tailWord_336721).sum := by decide
  have hdescent : baseEnd_336721 < baseStart_336721 := by decide
  rcases family_descends (prefixWord ++ tailWord_336721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336738 : List Nat := [3, 3, 2, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_336738 : Nat := 118140960795 + 336738 * 2 ^ 59
def prefixEnd_336738 : Nat := 4983230072969 + 3 ^ 40 * 336738 * 2
def baseEnd_336738 : Nat := 172908448633808744726377

theorem tailTrace_336738 : CollatzResearch.WordTrace tailWord_336738 prefixEnd_336738 172908448633808744726377 := by
  unfold tailWord_336738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3070460963515802779220717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8187895902708807411255245 3070460963515802779220717)
  ·
    refine ⟨1151422861318426042207769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3070460963515802779220717 1151422861318426042207769)
    ·
      refine ⟨863567145988819531655827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1151422861318426042207769 863567145988819531655827)
      ·
        refine ⟨1295350718983229297483741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 863567145988819531655827 1295350718983229297483741)
        ·
          refine ⟨485756519618710986556403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1295350718983229297483741 485756519618710986556403)
          ·
            refine ⟨728634779428066479834605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485756519618710986556403 728634779428066479834605)
            ·
              refine ⟨273238042285524929937977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 728634779428066479834605 273238042285524929937977)
              ·
                refine ⟨204928531714143697453483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273238042285524929937977 204928531714143697453483)
                ·
                  refine ⟨307392797571215546180225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204928531714143697453483 307392797571215546180225)
                  ·
                    refine ⟨230544598178411659635169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 307392797571215546180225 230544598178411659635169)
                    ·
                      refine ⟨172908448633808744726377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 230544598178411659635169 172908448633808744726377)
                      ·
                        rfl

theorem cell23_336738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_336738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336738 prefixEnd_336738 := by exact prefixLift 336738
  have htrace : WordTrace (prefixWord ++ tailWord_336738) baseStart_336738 baseEnd_336738 := by
    simpa [prefixWord, tailWord_336738, baseEnd_336738] using wordTrace_append hprefix tailTrace_336738
  have hstable : (prefixWord ++ tailWord_336738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336738).length < 2 ^ (prefixWord ++ tailWord_336738).sum := by decide
  have hdescent : baseEnd_336738 < baseStart_336738 := by decide
  rcases family_descends (prefixWord ++ tailWord_336738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336760 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 6, 2, 2]
def baseStart_336760 : Nat := 118140960795 + 336760 * 2 ^ 59
def prefixEnd_336760 : Nat := 4983230072969 + 3 ^ 40 * 336760 * 2
def baseEnd_336760 : Nat := 172919745208207658651275

theorem tailTrace_336760 : CollatzResearch.WordTrace tailWord_336760 prefixEnd_336760 172919745208207658651275 := by
  unfold tailWord_336760
  simp only [CollatzResearch.WordTrace]
  refine ⟨6141323129991754437091867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8188430839989005916122489 6141323129991754437091867)
  ·
    refine ⟨9211984694987631655637801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6141323129991754437091867 9211984694987631655637801)
    ·
      refine ⟨6908988521240723741728351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9211984694987631655637801 6908988521240723741728351)
      ·
        refine ⟨10363482781861085612592527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6908988521240723741728351 10363482781861085612592527)
        ·
          refine ⟨15545224172791628418888791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10363482781861085612592527 15545224172791628418888791)
          ·
            refine ⟨23317836259187442628333187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15545224172791628418888791 23317836259187442628333187)
            ·
              refine ⟨34976754388781163942499781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23317836259187442628333187 34976754388781163942499781)
              ·
                refine ⟨6558141447896468239218709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34976754388781163942499781 6558141447896468239218709)
                ·
                  refine ⟨307412880370146948713377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6558141447896468239218709 307412880370146948713377)
                  ·
                    refine ⟨230559660277610211535033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 307412880370146948713377 230559660277610211535033)
                    ·
                      refine ⟨172919745208207658651275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 230559660277610211535033 172919745208207658651275)
                      ·
                        rfl

theorem cell23_336760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 6, 2, 2].length) (baseStart_336760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336760 prefixEnd_336760 := by exact prefixLift 336760
  have htrace : WordTrace (prefixWord ++ tailWord_336760) baseStart_336760 baseEnd_336760 := by
    simpa [prefixWord, tailWord_336760, baseEnd_336760] using wordTrace_append hprefix tailTrace_336760
  have hstable : (prefixWord ++ tailWord_336760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336760).length < 2 ^ (prefixWord ++ tailWord_336760).sum := by decide
  have hdescent : baseEnd_336760 < baseStart_336760 := by decide
  rcases family_descends (prefixWord ++ tailWord_336760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336793 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 2, 3, 3]
def baseStart_336793 : Nat := 118140960795 + 336793 * 2 ^ 59
def prefixEnd_336793 : Nat := 4983230072969 + 3 ^ 40 * 336793 * 2
def baseEnd_336793 : Nat := 172936690069806029538623

theorem tailTrace_336793 : CollatzResearch.WordTrace tailWord_336793 prefixEnd_336793 172936690069806029538623 := by
  unfold tailWord_336793
  simp only [CollatzResearch.WordTrace]
  refine ⟨12283849868863955510135033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8189233245909303673423355 12283849868863955510135033)
  ·
    refine ⟨9212887401647966632601275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12283849868863955510135033 9212887401647966632601275)
    ·
      refine ⟨13819331102471949948901913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9212887401647966632601275 13819331102471949948901913)
      ·
        refine ⟨10364498326853962461676435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13819331102471949948901913 10364498326853962461676435)
        ·
          refine ⟨15546747490280943692514653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10364498326853962461676435 15546747490280943692514653)
          ·
            refine ⟨5830030308855353884692995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15546747490280943692514653 5830030308855353884692995)
            ·
              refine ⟨8745045463283030827039493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5830030308855353884692995 8745045463283030827039493)
              ·
                refine ⟨1639696024365568280069905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8745045463283030827039493 1639696024365568280069905)
                ·
                  refine ⟨1229772018274176210052429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1639696024365568280069905 1229772018274176210052429)
                  ·
                    refine ⟨461164506852816078769661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1229772018274176210052429 461164506852816078769661)
                    ·
                      refine ⟨172936690069806029538623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 461164506852816078769661 172936690069806029538623)
                      ·
                        rfl

theorem cell23_336793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_336793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336793 prefixEnd_336793 := by exact prefixLift 336793
  have htrace : WordTrace (prefixWord ++ tailWord_336793) baseStart_336793 baseEnd_336793 := by
    simpa [prefixWord, tailWord_336793, baseEnd_336793] using wordTrace_append hprefix tailTrace_336793
  have hstable : (prefixWord ++ tailWord_336793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336793).length < 2 ^ (prefixWord ++ tailWord_336793).sum := by decide
  have hdescent : baseEnd_336793 < baseStart_336793 := by decide
  rcases family_descends (prefixWord ++ tailWord_336793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336924 : List Nat := [2, 2, 3, 1, 4, 2, 2, 1, 6]
def baseStart_336924 : Nat := 118140960795 + 336924 * 2 ^ 59
def prefixEnd_336924 : Nat := 4983230072969 + 3 ^ 40 * 336924 * 2
def baseEnd_336924 : Nat := 19222661781727224111169

theorem tailTrace_336924 : CollatzResearch.WordTrace tailWord_336924 prefixEnd_336924 19222661781727224111169 := by
  unfold tailWord_336924
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144313915694682441576913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8192418554259576588769217 6144313915694682441576913)
  ·
    refine ⟨4608235436771011831182685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6144313915694682441576913 4608235436771011831182685)
    ·
      refine ⟨1728088288789129436693507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4608235436771011831182685 1728088288789129436693507)
      ·
        refine ⟨2592132433183694155040261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1728088288789129436693507 2592132433183694155040261)
        ·
          refine ⟨486024831221942654070049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2592132433183694155040261 486024831221942654070049)
          ·
            refine ⟨364518623416456990552537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 486024831221942654070049 364518623416456990552537)
            ·
              refine ⟨273388967562342742914403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364518623416456990552537 273388967562342742914403)
              ·
                refine ⟨410083451343514114371605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273388967562342742914403 410083451343514114371605)
                ·
                  refine ⟨19222661781727224111169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 410083451343514114371605 19222661781727224111169)
                  ·
                    rfl

theorem cell23_336924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 6].length) (baseStart_336924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336924 prefixEnd_336924 := by exact prefixLift 336924
  have htrace : WordTrace (prefixWord ++ tailWord_336924) baseStart_336924 baseEnd_336924 := by
    simpa [prefixWord, tailWord_336924, baseEnd_336924] using wordTrace_append hprefix tailTrace_336924
  have hstable : (prefixWord ++ tailWord_336924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336924).length < 2 ^ (prefixWord ++ tailWord_336924).sum := by decide
  have hdescent : baseEnd_336924 < baseStart_336924 := by decide
  rcases family_descends (prefixWord ++ tailWord_336924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336940 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 4]
def baseStart_336940 : Nat := 118140960795 + 336940 * 2 ^ 59
def prefixEnd_336940 : Nat := 4983230072969 + 3 ^ 40 * 336940 * 2
def baseEnd_336940 : Nat := 173012171726016954400447

theorem tailTrace_336940 : CollatzResearch.WordTrace tailWord_336940 prefixEnd_336940 173012171726016954400447 := by
  unfold tailWord_336940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144605699665699807868137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8192807599554266410490849 6144605699665699807868137)
  ·
    refine ⟨4608454274749274855901103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6144605699665699807868137 4608454274749274855901103)
    ·
      refine ⟨6912681412123912283851655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4608454274749274855901103 6912681412123912283851655)
      ·
        refine ⟨10369022118185868425777483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6912681412123912283851655 10369022118185868425777483)
        ·
          refine ⟨15553533177278802638666225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10369022118185868425777483 15553533177278802638666225)
          ·
            refine ⟨11665149882959101978999669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15553533177278802638666225 11665149882959101978999669)
            ·
              refine ⟨1093607801527415810531219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11665149882959101978999669 1093607801527415810531219)
              ·
                refine ⟨1640411702291123715796829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093607801527415810531219 1640411702291123715796829)
                ·
                  refine ⟨615154388359171393423811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1640411702291123715796829 615154388359171393423811)
                  ·
                    refine ⟨922731582538757090135717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 615154388359171393423811 922731582538757090135717)
                    ·
                      refine ⟨173012171726016954400447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 922731582538757090135717 173012171726016954400447)
                      ·
                        rfl

theorem cell23_336940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_336940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336940 prefixEnd_336940 := by exact prefixLift 336940
  have htrace : WordTrace (prefixWord ++ tailWord_336940) baseStart_336940 baseEnd_336940 := by
    simpa [prefixWord, tailWord_336940, baseEnd_336940] using wordTrace_append hprefix tailTrace_336940
  have hstable : (prefixWord ++ tailWord_336940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336940).length < 2 ^ (prefixWord ++ tailWord_336940).sum := by decide
  have hdescent : baseEnd_336940 < baseStart_336940 := by decide
  rcases family_descends (prefixWord ++ tailWord_336940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336967 : List Nat := [1, 1, 4, 1, 3, 2, 1, 4, 2, 4]
def baseStart_336967 : Nat := 118140960795 + 336967 * 2 ^ 59
def prefixEnd_336967 : Nat := 4983230072969 + 3 ^ 40 * 336967 * 2
def baseEnd_336967 : Nat := 57675345234562782920941

theorem tailTrace_336967 : CollatzResearch.WordTrace tailWord_336967 prefixEnd_336967 57675345234562782920941 := by
  unfold tailWord_336967
  simp only [CollatzResearch.WordTrace]
  refine ⟨12290196170233583226969155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8193464113489055484646103 12290196170233583226969155)
  ·
    refine ⟨18435294255350374840453733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12290196170233583226969155 18435294255350374840453733)
    ·
      refine ⟨3456617672878195282585075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18435294255350374840453733 3456617672878195282585075)
      ·
        refine ⟨5184926509317292923877613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3456617672878195282585075 5184926509317292923877613)
        ·
          refine ⟨1944347440993984846454105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5184926509317292923877613 1944347440993984846454105)
          ·
            refine ⟨1458260580745488634840579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1944347440993984846454105 1458260580745488634840579)
            ·
              refine ⟨2187390871118232952260869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458260580745488634840579 2187390871118232952260869)
              ·
                refine ⟨410135788334668678548913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2187390871118232952260869 410135788334668678548913)
                ·
                  refine ⟨307601841251001508911685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410135788334668678548913 307601841251001508911685)
                  ·
                    refine ⟨57675345234562782920941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 307601841251001508911685 57675345234562782920941)
                    ·
                      rfl

theorem cell23_336967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_336967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336967 prefixEnd_336967 := by exact prefixLift 336967
  have htrace : WordTrace (prefixWord ++ tailWord_336967) baseStart_336967 baseEnd_336967 := by
    simpa [prefixWord, tailWord_336967, baseEnd_336967] using wordTrace_append hprefix tailTrace_336967
  have hstable : (prefixWord ++ tailWord_336967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336967).length < 2 ^ (prefixWord ++ tailWord_336967).sum := by decide
  have hdescent : baseEnd_336967 < baseStart_336967 := by decide
  rcases family_descends (prefixWord ++ tailWord_336967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336974 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2]
def baseStart_336974 : Nat := 118140960795 + 336974 * 2 ^ 59
def prefixEnd_336974 : Nat := 4983230072969 + 3 ^ 40 * 336974 * 2
def baseEnd_336974 : Nat := 173029630068269821375291

theorem tailTrace_336974 : CollatzResearch.WordTrace tailWord_336974 prefixEnd_336974 173029630068269821375291 := by
  unfold tailWord_336974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536306435151027927809247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8193634320805482281649317 1536306435151027927809247)
  ·
    refine ⟨2304459652726541891713871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1536306435151027927809247 2304459652726541891713871)
    ·
      refine ⟨3456689479089812837570807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2304459652726541891713871 3456689479089812837570807)
      ·
        refine ⟨5185034218634719256356211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3456689479089812837570807 5185034218634719256356211)
        ·
          refine ⟨7777551327952078884534317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5185034218634719256356211 7777551327952078884534317)
          ·
            refine ⟨2916581747982029581700369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7777551327952078884534317 2916581747982029581700369)
            ·
              refine ⟨2187436310986522186275277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2916581747982029581700369 2187436310986522186275277)
              ·
                refine ⟨820288616619945819853229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2187436310986522186275277 820288616619945819853229)
                ·
                  refine ⟨307608231232479682444961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 820288616619945819853229 307608231232479682444961)
                  ·
                    refine ⟨230706173424359761833721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 307608231232479682444961 230706173424359761833721)
                    ·
                      refine ⟨173029630068269821375291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 230706173424359761833721 173029630068269821375291)
                      ·
                        rfl

theorem cell23_336974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_336974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336974 prefixEnd_336974 := by exact prefixLift 336974
  have htrace : WordTrace (prefixWord ++ tailWord_336974) baseStart_336974 baseEnd_336974 := by
    simpa [prefixWord, tailWord_336974, baseEnd_336974] using wordTrace_append hprefix tailTrace_336974
  have hstable : (prefixWord ++ tailWord_336974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336974).length < 2 ^ (prefixWord ++ tailWord_336974).sum := by decide
  have hdescent : baseEnd_336974 < baseStart_336974 := by decide
  rcases family_descends (prefixWord ++ tailWord_336974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336980 : List Nat := [2, 4, 1, 1, 1, 1, 5, 8]
def baseStart_336980 : Nat := 118140960795 + 336980 * 2 ^ 59
def prefixEnd_336980 : Nat := 4983230072969 + 3 ^ 40 * 336980 * 2
def baseEnd_336980 : Nat := 6408618924155436959269

theorem tailTrace_336980 : CollatzResearch.WordTrace tailWord_336980 prefixEnd_336980 6408618924155436959269 := by
  unfold tailWord_336980
  simp only [CollatzResearch.WordTrace]
  refine ⟨6145335159593243223596197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8193780212790990964794929 6145335159593243223596197)
  ·
    refine ⟨1152250342423733104424287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6145335159593243223596197 1152250342423733104424287)
    ·
      refine ⟨1728375513635599656636431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1152250342423733104424287 1728375513635599656636431)
      ·
        refine ⟨2592563270453399484954647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1728375513635599656636431 2592563270453399484954647)
        ·
          refine ⟨3888844905680099227431971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2592563270453399484954647 3888844905680099227431971)
          ·
            refine ⟨5833267358520148841147957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3888844905680099227431971 5833267358520148841147957)
            ·
              refine ⟨546868814861263953857621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5833267358520148841147957 546868814861263953857621)
              ·
                refine ⟨6408618924155436959269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 546868814861263953857621 6408618924155436959269)
                ·
                  rfl

theorem cell23_336980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 8].length) (baseStart_336980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336980 prefixEnd_336980 := by exact prefixLift 336980
  have htrace : WordTrace (prefixWord ++ tailWord_336980) baseStart_336980 baseEnd_336980 := by
    simpa [prefixWord, tailWord_336980, baseEnd_336980] using wordTrace_append hprefix tailTrace_336980
  have hstable : (prefixWord ++ tailWord_336980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336980).length < 2 ^ (prefixWord ++ tailWord_336980).sum := by decide
  have hdescent : baseEnd_336980 < baseStart_336980 := by decide
  rcases family_descends (prefixWord ++ tailWord_336980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_336994 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_336994 : Nat := 118140960795 + 336994 * 2 ^ 59
def prefixEnd_336994 : Nat := 4983230072969 + 3 ^ 40 * 336994 * 2
def baseEnd_336994 : Nat := 173039899681359743125199

theorem tailTrace_336994 : CollatzResearch.WordTrace tailWord_336994 prefixEnd_336994 173039899681359743125199 := by
  unfold tailWord_336994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3072795235283941709550509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8194120627423844558801357 3072795235283941709550509)
  ·
    refine ⟨1152298213231478141081441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3072795235283941709550509 1152298213231478141081441)
    ·
      refine ⟨864223659923608605811081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1152298213231478141081441 864223659923608605811081)
      ·
        refine ⟨648167744942706454358311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 864223659923608605811081 648167744942706454358311)
        ·
          refine ⟨972251617414059681537467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648167744942706454358311 972251617414059681537467)
          ·
            refine ⟨1458377426121089522306201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972251617414059681537467 1458377426121089522306201)
            ·
              refine ⟨1093783069590817141729651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1458377426121089522306201 1093783069590817141729651)
              ·
                refine ⟨1640674604386225712594477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093783069590817141729651 1640674604386225712594477)
                ·
                  refine ⟨615252976644834642222929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1640674604386225712594477 615252976644834642222929)
                  ·
                    refine ⟨461439732483625981667197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 615252976644834642222929 461439732483625981667197)
                    ·
                      refine ⟨173039899681359743125199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 461439732483625981667197 173039899681359743125199)
                      ·
                        rfl

theorem cell23_336994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_336994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_336994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_336994 prefixEnd_336994 := by exact prefixLift 336994
  have htrace : WordTrace (prefixWord ++ tailWord_336994) baseStart_336994 baseEnd_336994 := by
    simpa [prefixWord, tailWord_336994, baseEnd_336994] using wordTrace_append hprefix tailTrace_336994
  have hstable : (prefixWord ++ tailWord_336994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_336994).length < 2 ^ (prefixWord ++ tailWord_336994).sum := by decide
  have hdescent : baseEnd_336994 < baseStart_336994 := by decide
  rcases family_descends (prefixWord ++ tailWord_336994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337007 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 4, 1, 3]
def baseStart_337007 : Nat := 118140960795 + 337007 * 2 ^ 59
def prefixEnd_337007 : Nat := 4983230072969 + 3 ^ 40 * 337007 * 2
def baseEnd_337007 : Nat := 173046574929868192262639

theorem tailTrace_337007 : CollatzResearch.WordTrace tailWord_337007 prefixEnd_337007 173046574929868192262639 := by
  unfold tailWord_337007
  simp only [CollatzResearch.WordTrace]
  refine ⟨12291655090088670058425275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8194436726725780038950183 12291655090088670058425275)
  ·
    refine ⟨18437482635133005087637913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12291655090088670058425275 18437482635133005087637913)
    ·
      refine ⟨13828111976349753815728435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18437482635133005087637913 13828111976349753815728435)
      ·
        refine ⟨20742167964524630723592653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13828111976349753815728435 20742167964524630723592653)
        ·
          refine ⟨7778312986696736521347245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20742167964524630723592653 7778312986696736521347245)
          ·
            refine ⟨2916867370011276195505217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7778312986696736521347245 2916867370011276195505217)
            ·
              refine ⟨2187650527508457146628913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2916867370011276195505217 2187650527508457146628913)
              ·
                refine ⟨1640737895631342859971685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187650527508457146628913 1640737895631342859971685)
                ·
                  refine ⟨307638355430876786244691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640737895631342859971685 307638355430876786244691)
                  ·
                    refine ⟨461457533146315179367037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 307638355430876786244691 461457533146315179367037)
                    ·
                      refine ⟨173046574929868192262639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 461457533146315179367037 173046574929868192262639)
                      ·
                        rfl

theorem cell23_337007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 4, 1, 3].length) (baseStart_337007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337007 prefixEnd_337007 := by exact prefixLift 337007
  have htrace : WordTrace (prefixWord ++ tailWord_337007) baseStart_337007 baseEnd_337007 := by
    simpa [prefixWord, tailWord_337007, baseEnd_337007] using wordTrace_append hprefix tailTrace_337007
  have hstable : (prefixWord ++ tailWord_337007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337007).length < 2 ^ (prefixWord ++ tailWord_337007).sum := by decide
  have hdescent : baseEnd_337007 < baseStart_337007 := by decide
  rcases family_descends (prefixWord ++ tailWord_337007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337024 : List Nat := [2, 1, 1, 2, 1, 3, 5, 2, 2, 1, 3]
def baseStart_337024 : Nat := 118140960795 + 337024 * 2 ^ 59
def prefixEnd_337024 : Nat := 4983230072969 + 3 ^ 40 * 337024 * 2
def baseEnd_337024 : Nat := 173055304100994625750061

theorem tailTrace_337024 : CollatzResearch.WordTrace tailWord_337024 prefixEnd_337024 173055304100994625750061 := by
  unfold tailWord_337024
  simp only [CollatzResearch.WordTrace]
  refine ⟨6146137565513540980897063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8194850087351387974529417 6146137565513540980897063)
  ·
    refine ⟨9219206348270311471345595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6146137565513540980897063 9219206348270311471345595)
    ·
      refine ⟨13828809522405467207018393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9219206348270311471345595 13828809522405467207018393)
      ·
        refine ⟨10371607141804100405263795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13828809522405467207018393 10371607141804100405263795)
        ·
          refine ⟨15557410712706150607895693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10371607141804100405263795 15557410712706150607895693)
          ·
            refine ⟨5834029017264806477960885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15557410712706150607895693 5834029017264806477960885)
            ·
              refine ⟨546940220368575607308833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5834029017264806477960885 546940220368575607308833)
              ·
                refine ⟨410205165276431705481625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546940220368575607308833 410205165276431705481625)
                ·
                  refine ⟨307653873957323779111219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410205165276431705481625 307653873957323779111219)
                  ·
                    refine ⟨461480810935985668666829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 307653873957323779111219 461480810935985668666829)
                    ·
                      refine ⟨173055304100994625750061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 461480810935985668666829 173055304100994625750061)
                      ·
                        rfl

theorem cell23_337024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_337024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337024 prefixEnd_337024 := by exact prefixLift 337024
  have htrace : WordTrace (prefixWord ++ tailWord_337024) baseStart_337024 baseEnd_337024 := by
    simpa [prefixWord, tailWord_337024, baseEnd_337024] using wordTrace_append hprefix tailTrace_337024
  have hstable : (prefixWord ++ tailWord_337024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337024).length < 2 ^ (prefixWord ++ tailWord_337024).sum := by decide
  have hdescent : baseEnd_337024 < baseStart_337024 := by decide
  rcases family_descends (prefixWord ++ tailWord_337024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337087 : List Nat := [1, 1, 2, 2, 2, 2, 2, 6, 5]
def baseStart_337087 : Nat := 118140960795 + 337087 * 2 ^ 59
def prefixEnd_337087 : Nat := 4983230072969 + 3 ^ 40 * 337087 * 2
def baseEnd_337087 : Nat := 19231961486914208806919

theorem tailTrace_337087 : CollatzResearch.WordTrace tailWord_337087 prefixEnd_337087 19231961486914208806919 := by
  unfold tailWord_337087
  simp only [CollatzResearch.WordTrace]
  refine ⟨12294572929798843721337515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8196381953199229147558343 12294572929798843721337515)
  ·
    refine ⟨18441859394698265582006273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12294572929798843721337515 18441859394698265582006273)
    ·
      refine ⟨13831394546023699186504705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18441859394698265582006273 13831394546023699186504705)
      ·
        refine ⟨10373545909517774389878529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13831394546023699186504705 10373545909517774389878529)
        ·
          refine ⟨7780159432138330792408897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10373545909517774389878529 7780159432138330792408897)
          ·
            refine ⟨5835119574103748094306673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7780159432138330792408897 5835119574103748094306673)
            ·
              refine ⟨4376339680577811070730005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5835119574103748094306673 4376339680577811070730005)
              ·
                refine ⟨205140922527084893940469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4376339680577811070730005 205140922527084893940469)
                ·
                  refine ⟨19231961486914208806919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205140922527084893940469 19231961486914208806919)
                  ·
                    rfl

theorem cell23_337087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 5].length) (baseStart_337087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337087 prefixEnd_337087 := by exact prefixLift 337087
  have htrace : WordTrace (prefixWord ++ tailWord_337087) baseStart_337087 baseEnd_337087 := by
    simpa [prefixWord, tailWord_337087, baseEnd_337087] using wordTrace_append hprefix tailTrace_337087
  have hstable : (prefixWord ++ tailWord_337087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337087).length < 2 ^ (prefixWord ++ tailWord_337087).sum := by decide
  have hdescent : baseEnd_337087 < baseStart_337087 := by decide
  rcases family_descends (prefixWord ++ tailWord_337087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337098 : List Nat := [3, 1, 2, 1, 3, 2, 4, 1, 2, 2, 2]
def baseStart_337098 : Nat := 118140960795 + 337098 * 2 ^ 59
def prefixEnd_337098 : Nat := 4983230072969 + 3 ^ 40 * 337098 * 2
def baseEnd_337098 : Nat := 173093301669427336224721

theorem tailTrace_337098 : CollatzResearch.WordTrace tailWord_337098 prefixEnd_337098 173093301669427336224721 := by
  unfold tailWord_337098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3073743533189748149996987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8196649421839328399991965 3073743533189748149996987)
  ·
    refine ⟨4610615299784622224995481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3073743533189748149996987 4610615299784622224995481)
    ·
      refine ⟨3457961474838466668746611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4610615299784622224995481 3457961474838466668746611)
      ·
        refine ⟨5186942212257700003119917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3457961474838466668746611 5186942212257700003119917)
        ·
          refine ⟨1945103329596637501169969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5186942212257700003119917 1945103329596637501169969)
          ·
            refine ⟨1458827497197478125877477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1945103329596637501169969 1458827497197478125877477)
            ·
              refine ⟨273530155724527148602027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1458827497197478125877477 273530155724527148602027)
              ·
                refine ⟨410295233586790722903041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273530155724527148602027 410295233586790722903041)
                ·
                  refine ⟨307721425190093042177281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410295233586790722903041 307721425190093042177281)
                  ·
                    refine ⟨230791068892569781632961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 307721425190093042177281 230791068892569781632961)
                    ·
                      refine ⟨173093301669427336224721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 230791068892569781632961 173093301669427336224721)
                      ·
                        rfl

theorem cell23_337098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_337098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337098 prefixEnd_337098 := by exact prefixLift 337098
  have htrace : WordTrace (prefixWord ++ tailWord_337098) baseStart_337098 baseEnd_337098 := by
    simpa [prefixWord, tailWord_337098, baseEnd_337098] using wordTrace_append hprefix tailTrace_337098
  have hstable : (prefixWord ++ tailWord_337098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337098).length < 2 ^ (prefixWord ++ tailWord_337098).sum := by decide
  have hdescent : baseEnd_337098 < baseStart_337098 := by decide
  rcases family_descends (prefixWord ++ tailWord_337098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337107 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 2, 5, 2]
def baseStart_337107 : Nat := 118140960795 + 337107 * 2 ^ 59
def prefixEnd_337107 : Nat := 4983230072969 + 3 ^ 40 * 337107 * 2
def baseEnd_337107 : Nat := 173097922995317801012179

theorem tailTrace_337107 : CollatzResearch.WordTrace tailWord_337107 prefixEnd_337107 173097922995317801012179 := by
  unfold tailWord_337107
  simp only [CollatzResearch.WordTrace]
  refine ⟨12295302389726387137065575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8196868259817591424710383 12295302389726387137065575)
  ·
    refine ⟨18442953584589580705598363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12295302389726387137065575 18442953584589580705598363)
    ·
      refine ⟨27664430376884371058397545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18442953584589580705598363 27664430376884371058397545)
      ·
        refine ⟨20748322782663278293798159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27664430376884371058397545 20748322782663278293798159)
        ·
          refine ⟨31122484173994917440697239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20748322782663278293798159 31122484173994917440697239)
          ·
            refine ⟨46683726260992376161045859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31122484173994917440697239 46683726260992376161045859)
            ·
              refine ⟨70025589391488564241568789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46683726260992376161045859 70025589391488564241568789)
              ·
                refine ⟨3282449502726026448823537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70025589391488564241568789 3282449502726026448823537)
                ·
                  refine ⟨2461837127044519836617653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3282449502726026448823537 2461837127044519836617653)
                  ·
                    refine ⟨230797230660423734682905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2461837127044519836617653 230797230660423734682905)
                    ·
                      refine ⟨173097922995317801012179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 230797230660423734682905 173097922995317801012179)
                      ·
                        rfl

theorem cell23_337107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 5, 2].length) (baseStart_337107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337107 prefixEnd_337107 := by exact prefixLift 337107
  have htrace : WordTrace (prefixWord ++ tailWord_337107) baseStart_337107 baseEnd_337107 := by
    simpa [prefixWord, tailWord_337107, baseEnd_337107] using wordTrace_append hprefix tailTrace_337107
  have hstable : (prefixWord ++ tailWord_337107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337107).length < 2 ^ (prefixWord ++ tailWord_337107).sum := by decide
  have hdescent : baseEnd_337107 < baseStart_337107 := by decide
  rcases family_descends (prefixWord ++ tailWord_337107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337138 : List Nat := [3, 2, 1, 3, 3, 2, 2, 2, 5]
def baseStart_337138 : Nat := 118140960795 + 337138 * 2 ^ 59
def prefixEnd_337138 : Nat := 4983230072969 + 3 ^ 40 * 337138 * 2
def baseEnd_337138 : Nat := 19234871210623019969393

theorem tailTrace_337138 : CollatzResearch.WordTrace tailWord_337138 prefixEnd_337138 19234871210623019969393 := by
  unfold tailWord_337138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3074108263153519857861017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8197622035076052954296045 3074108263153519857861017)
  ·
    refine ⟨2305581197365139893395763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3074108263153519857861017 2305581197365139893395763)
    ·
      refine ⟨3458371796047709840093645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2305581197365139893395763 3458371796047709840093645)
      ·
        refine ⟨1296889423517891190035117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3458371796047709840093645 1296889423517891190035117)
        ·
          refine ⟨486333533819209196263169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1296889423517891190035117 486333533819209196263169)
          ·
            refine ⟨364750150364406897197377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 486333533819209196263169 364750150364406897197377)
            ·
              refine ⟨273562612773305172898033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364750150364406897197377 273562612773305172898033)
              ·
                refine ⟨205171959579978879673525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273562612773305172898033 205171959579978879673525)
                ·
                  refine ⟨19234871210623019969393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205171959579978879673525 19234871210623019969393)
                  ·
                    rfl

theorem cell23_337138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_337138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337138 prefixEnd_337138 := by exact prefixLift 337138
  have htrace : WordTrace (prefixWord ++ tailWord_337138) baseStart_337138 baseEnd_337138 := by
    simpa [prefixWord, tailWord_337138, baseEnd_337138] using wordTrace_append hprefix tailTrace_337138
  have hstable : (prefixWord ++ tailWord_337138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337138).length < 2 ^ (prefixWord ++ tailWord_337138).sum := by decide
  have hdescent : baseEnd_337138 < baseStart_337138 := by decide
  rcases family_descends (prefixWord ++ tailWord_337138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337157 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 1, 4, 3]
def baseStart_337157 : Nat := 118140960795 + 337157 * 2 ^ 59
def prefixEnd_337157 : Nat := 4983230072969 + 3 ^ 40 * 337157 * 2
def baseEnd_337157 : Nat := 173123597028042605386949

theorem tailTrace_337157 : CollatzResearch.WordTrace tailWord_337157 prefixEnd_337157 173123597028042605386949 := by
  unfold tailWord_337157
  simp only [CollatzResearch.WordTrace]
  refine ⟨12297126039545245676385725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8198084026363497117590483 12297126039545245676385725)
  ·
    refine ⟨4611422264829467128644647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12297126039545245676385725 4611422264829467128644647)
    ·
      refine ⟨6917133397244200692966971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4611422264829467128644647 6917133397244200692966971)
      ·
        refine ⟨10375700095866301039450457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6917133397244200692966971 10375700095866301039450457)
        ·
          refine ⟨7781775071899725779587843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10375700095866301039450457 7781775071899725779587843)
          ·
            refine ⟨11672662607849588669381765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7781775071899725779587843 11672662607849588669381765)
            ·
              refine ⟨2188624238971797875509081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11672662607849588669381765 2188624238971797875509081)
              ·
                refine ⟨1641468179228848406631811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2188624238971797875509081 1641468179228848406631811)
                ·
                  refine ⟨2462202268843272609947717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641468179228848406631811 2462202268843272609947717)
                  ·
                    refine ⟨461662925408113614365197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2462202268843272609947717 461662925408113614365197)
                    ·
                      refine ⟨173123597028042605386949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 461662925408113614365197 173123597028042605386949)
                      ·
                        rfl

theorem cell23_337157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 4, 3].length) (baseStart_337157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337157 prefixEnd_337157 := by exact prefixLift 337157
  have htrace : WordTrace (prefixWord ++ tailWord_337157) baseStart_337157 baseEnd_337157 := by
    simpa [prefixWord, tailWord_337157, baseEnd_337157] using wordTrace_append hprefix tailTrace_337157
  have hstable : (prefixWord ++ tailWord_337157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337157).length < 2 ^ (prefixWord ++ tailWord_337157).sum := by decide
  have hdescent : baseEnd_337157 < baseStart_337157 := by decide
  rcases family_descends (prefixWord ++ tailWord_337157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337164 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 3, 4]
def baseStart_337164 : Nat := 118140960795 + 337164 * 2 ^ 59
def prefixEnd_337164 : Nat := 4983230072969 + 3 ^ 40 * 337164 * 2
def baseEnd_337164 : Nat := 57709063797541359333139

theorem tailTrace_337164 : CollatzResearch.WordTrace tailWord_337164 prefixEnd_337164 57709063797541359333139 := by
  unfold tailWord_337164
  simp only [CollatzResearch.WordTrace]
  refine ⟨6148690675259942935945273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8198254233679923914593697 6148690675259942935945273)
  ·
    refine ⟨4611518006444957201958955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6148690675259942935945273 4611518006444957201958955)
    ·
      refine ⟨6917277009667435802938433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4611518006444957201958955 6917277009667435802938433)
      ·
        refine ⟨5187957757250576852203825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6917277009667435802938433 5187957757250576852203825)
        ·
          refine ⟨3890968317937932639152869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5187957757250576852203825 3890968317937932639152869)
          ·
            refine ⟨729556559613362369841163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3890968317937932639152869 729556559613362369841163)
            ·
              refine ⟨1094334839420043554761745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729556559613362369841163 1094334839420043554761745)
              ·
                refine ⟨820751129565032666071309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1094334839420043554761745 820751129565032666071309)
                ·
                  refine ⟨307781673586887249776741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 820751129565032666071309 307781673586887249776741)
                  ·
                    refine ⟨57709063797541359333139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 307781673586887249776741 57709063797541359333139)
                    ·
                      rfl

theorem cell23_337164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_337164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337164 prefixEnd_337164 := by exact prefixLift 337164
  have htrace : WordTrace (prefixWord ++ tailWord_337164) baseStart_337164 baseEnd_337164 := by
    simpa [prefixWord, tailWord_337164, baseEnd_337164] using wordTrace_append hprefix tailTrace_337164
  have hstable : (prefixWord ++ tailWord_337164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337164).length < 2 ^ (prefixWord ++ tailWord_337164).sum := by decide
  have hdescent : baseEnd_337164 < baseStart_337164 := by decide
  rcases family_descends (prefixWord ++ tailWord_337164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337194 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 8]
def baseStart_337194 : Nat := 118140960795 + 337194 * 2 ^ 59
def prefixEnd_337194 : Nat := 4983230072969 + 3 ^ 40 * 337194 * 2
def baseEnd_337194 : Nat := 19238066201362106736031

theorem tailTrace_337194 : CollatzResearch.WordTrace tailWord_337194 prefixEnd_337194 19238066201362106736031 := by
  unfold tailWord_337194
  simp only [CollatzResearch.WordTrace]
  refine ⟨3074618885102800248870659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8198983693607467330321757 3074618885102800248870659)
  ·
    refine ⟨4611928327654200373305989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3074618885102800248870659 4611928327654200373305989)
    ·
      refine ⟨864736561435162569994873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4611928327654200373305989 864736561435162569994873)
      ·
        refine ⟨648552421076371927496155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 864736561435162569994873 648552421076371927496155)
        ·
          refine ⟨972828631614557891244233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648552421076371927496155 972828631614557891244233)
          ·
            refine ⟨729621473710918418433175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 972828631614557891244233 729621473710918418433175)
            ·
              refine ⟨1094432210566377627649763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729621473710918418433175 1094432210566377627649763)
              ·
                refine ⟨1641648315849566441474645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094432210566377627649763 1641648315849566441474645)
                ·
                  refine ⟨19238066201362106736031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1641648315849566441474645 19238066201362106736031)
                  ·
                    rfl

theorem cell23_337194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_337194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337194 prefixEnd_337194 := by exact prefixLift 337194
  have htrace : WordTrace (prefixWord ++ tailWord_337194) baseStart_337194 baseEnd_337194 := by
    simpa [prefixWord, tailWord_337194, baseEnd_337194] using wordTrace_append hprefix tailTrace_337194
  have hstable : (prefixWord ++ tailWord_337194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337194).length < 2 ^ (prefixWord ++ tailWord_337194).sum := by decide
  have hdescent : baseEnd_337194 < baseStart_337194 := by decide
  rcases family_descends (prefixWord ++ tailWord_337194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337227 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 4]
def baseStart_337227 : Nat := 118140960795 + 337227 * 2 ^ 59
def prefixEnd_337227 : Nat := 4983230072969 + 3 ^ 40 * 337227 * 2
def baseEnd_337227 : Nat := 173159540673857331511627

theorem tailTrace_337227 : CollatzResearch.WordTrace tailWord_337227 prefixEnd_337227 173159540673857331511627 := by
  unfold tailWord_337227
  simp only [CollatzResearch.WordTrace]
  refine ⟨12299679149291647631433935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8199786099527765087622623 12299679149291647631433935)
  ·
    refine ⟨18449518723937471447150903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12299679149291647631433935 18449518723937471447150903)
    ·
      refine ⟨27674278085906207170726355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18449518723937471447150903 27674278085906207170726355)
      ·
        refine ⟨41511417128859310756089533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27674278085906207170726355 41511417128859310756089533)
        ·
          refine ⟨15566781423322241533533575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41511417128859310756089533 15566781423322241533533575)
          ·
            refine ⟨23350172134983362300300363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15566781423322241533533575 23350172134983362300300363)
            ·
              refine ⟨35025258202475043450450545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23350172134983362300300363 35025258202475043450450545)
              ·
                refine ⟨26268943651856282587837909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35025258202475043450450545 26268943651856282587837909)
                ·
                  refine ⟨615678366840381623152451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 26268943651856282587837909 615678366840381623152451)
                  ·
                    refine ⟨923517550260572434728677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 615678366840381623152451 923517550260572434728677)
                    ·
                      refine ⟨173159540673857331511627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 923517550260572434728677 173159540673857331511627)
                      ·
                        rfl

theorem cell23_337227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 4].length) (baseStart_337227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337227 prefixEnd_337227 := by exact prefixLift 337227
  have htrace : WordTrace (prefixWord ++ tailWord_337227) baseStart_337227 baseEnd_337227 := by
    simpa [prefixWord, tailWord_337227, baseEnd_337227] using wordTrace_append hprefix tailTrace_337227
  have hstable : (prefixWord ++ tailWord_337227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337227).length < 2 ^ (prefixWord ++ tailWord_337227).sum := by decide
  have hdescent : baseEnd_337227 < baseStart_337227 := by decide
  rcases family_descends (prefixWord ++ tailWord_337227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337255 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_337255 : Nat := 118140960795 + 337255 * 2 ^ 59
def prefixEnd_337255 : Nat := 4983230072969 + 3 ^ 40 * 337255 * 2
def baseEnd_337255 : Nat := 173173918132183221961499

theorem tailTrace_337255 : CollatzResearch.WordTrace tailWord_337255 prefixEnd_337255 173173918132183221961499 := by
  unfold tailWord_337255
  simp only [CollatzResearch.WordTrace]
  refine ⟨12300700393190208413453219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8200466928793472275635479 12300700393190208413453219)
  ·
    refine ⟨18451050589785312620179829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12300700393190208413453219 18451050589785312620179829)
    ·
      refine ⟨1729785992792373058141859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18451050589785312620179829 1729785992792373058141859)
      ·
        refine ⟨2594678989188559587212789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1729785992792373058141859 2594678989188559587212789)
        ·
          refine ⟨243251155236427461301199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2594678989188559587212789 243251155236427461301199)
          ·
            refine ⟨364876732854641191951799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243251155236427461301199 364876732854641191951799)
            ·
              refine ⟨547315099281961787927699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364876732854641191951799 547315099281961787927699)
              ·
                refine ⟨820972648922942681891549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547315099281961787927699 820972648922942681891549)
                ·
                  refine ⟨307864743346103505709331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 820972648922942681891549 307864743346103505709331)
                  ·
                    refine ⟨461797115019155258563997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 307864743346103505709331 461797115019155258563997)
                    ·
                      refine ⟨173173918132183221961499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 461797115019155258563997 173173918132183221961499)
                      ·
                        rfl

theorem cell23_337255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_337255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337255 prefixEnd_337255 := by exact prefixLift 337255
  have htrace : WordTrace (prefixWord ++ tailWord_337255) baseStart_337255 baseEnd_337255 := by
    simpa [prefixWord, tailWord_337255, baseEnd_337255] using wordTrace_append hprefix tailTrace_337255
  have hstable : (prefixWord ++ tailWord_337255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337255).length < 2 ^ (prefixWord ++ tailWord_337255).sum := by decide
  have hdescent : baseEnd_337255 < baseStart_337255 := by decide
  rcases family_descends (prefixWord ++ tailWord_337255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337257 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 5, 2, 4]
def baseStart_337257 : Nat := 118140960795 + 337257 * 2 ^ 59
def prefixEnd_337257 : Nat := 4983230072969 + 3 ^ 40 * 337257 * 2
def baseEnd_337257 : Nat := 173174945093492214136489

theorem tailTrace_337257 : CollatzResearch.WordTrace tailWord_337257 prefixEnd_337257 173174945093492214136489 := by
  unfold tailWord_337257
  simp only [CollatzResearch.WordTrace]
  refine ⟨12300773339182962755026025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8200515559455308503350683 12300773339182962755026025)
  ·
    refine ⟨9225580004387222066269519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12300773339182962755026025 9225580004387222066269519)
    ·
      refine ⟨13838370006580833099404279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9225580004387222066269519 13838370006580833099404279)
      ·
        refine ⟨20757555009871249649106419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13838370006580833099404279 20757555009871249649106419)
        ·
          refine ⟨31136332514806874473659629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20757555009871249649106419 31136332514806874473659629)
          ·
            refine ⟨11676124693052577927622361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31136332514806874473659629 11676124693052577927622361)
            ·
              refine ⟨8757093519789433445716771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11676124693052577927622361 8757093519789433445716771)
              ·
                refine ⟨13135640279684150168575157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8757093519789433445716771 13135640279684150168575157)
                ·
                  refine ⟨1231466276220389078303921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13135640279684150168575157 1231466276220389078303921)
                  ·
                    refine ⟨923599707165291808727941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1231466276220389078303921 923599707165291808727941)
                    ·
                      refine ⟨173174945093492214136489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 923599707165291808727941 173174945093492214136489)
                      ·
                        rfl

theorem cell23_337257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_337257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337257 prefixEnd_337257 := by exact prefixLift 337257
  have htrace : WordTrace (prefixWord ++ tailWord_337257) baseStart_337257 baseEnd_337257 := by
    simpa [prefixWord, tailWord_337257, baseEnd_337257] using wordTrace_append hprefix tailTrace_337257
  have hstable : (prefixWord ++ tailWord_337257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337257).length < 2 ^ (prefixWord ++ tailWord_337257).sum := by decide
  have hdescent : baseEnd_337257 < baseStart_337257 := by decide
  rcases family_descends (prefixWord ++ tailWord_337257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337264 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 3]
def baseStart_337264 : Nat := 118140960795 + 337264 * 2 ^ 59
def prefixEnd_337264 : Nat := 4983230072969 + 3 ^ 40 * 337264 * 2
def baseEnd_337264 : Nat := 173178539458073686748957

theorem tailTrace_337264 : CollatzResearch.WordTrace tailWord_337264 prefixEnd_337264 173178539458073686748957 := by
  unfold tailWord_337264
  simp only [CollatzResearch.WordTrace]
  refine ⟨6150514325078801475265423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8200685766771735300353897 6150514325078801475265423)
  ·
    refine ⟨9225771487618202212898135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6150514325078801475265423 9225771487618202212898135)
    ·
      refine ⟨13838657231427303319347203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9225771487618202212898135 13838657231427303319347203)
      ·
        refine ⟨20757985847140954979020805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13838657231427303319347203 20757985847140954979020805)
        ·
          refine ⟨3892122346338929058566401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20757985847140954979020805 3892122346338929058566401)
          ·
            refine ⟨2919091759754196793924801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3892122346338929058566401 2919091759754196793924801)
            ·
              refine ⟨2189318819815647595443601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2919091759754196793924801 2189318819815647595443601)
              ·
                refine ⟨1641989114861735696582701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2189318819815647595443601 1641989114861735696582701)
                ·
                  refine ⟨615745918073150886218513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1641989114861735696582701 615745918073150886218513)
                  ·
                    refine ⟨461809438554863164663885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 615745918073150886218513 461809438554863164663885)
                    ·
                      refine ⟨173178539458073686748957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 461809438554863164663885 173178539458073686748957)
                      ·
                        rfl

theorem cell23_337264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 3].length) (baseStart_337264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337264 prefixEnd_337264 := by exact prefixLift 337264
  have htrace : WordTrace (prefixWord ++ tailWord_337264) baseStart_337264 baseEnd_337264 := by
    simpa [prefixWord, tailWord_337264, baseEnd_337264] using wordTrace_append hprefix tailTrace_337264
  have hstable : (prefixWord ++ tailWord_337264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337264).length < 2 ^ (prefixWord ++ tailWord_337264).sum := by decide
  have hdescent : baseEnd_337264 < baseStart_337264 := by decide
  rcases family_descends (prefixWord ++ tailWord_337264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337314 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_337314 : Nat := 118140960795 + 337314 * 2 ^ 59
def prefixEnd_337314 : Nat := 4983230072969 + 3 ^ 40 * 337314 * 2
def baseEnd_337314 : Nat := 57734737830266163707909

theorem tailTrace_337314 : CollatzResearch.WordTrace tailWord_337314 prefixEnd_337314 57734737830266163707909 := by
  unfold tailWord_337314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3075713074994115372462749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8201901533317640993233997 3075713074994115372462749)
  ·
    refine ⟨1153392403122793264673531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3075713074994115372462749 1153392403122793264673531)
    ·
      refine ⟨1730088604684189897010297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1153392403122793264673531 1730088604684189897010297)
      ·
        refine ⟨1297566453513142422757723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1730088604684189897010297 1297566453513142422757723)
        ·
          refine ⟨1946349680269713634136585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1297566453513142422757723 1946349680269713634136585)
          ·
            refine ⟨1459762260202285225602439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1946349680269713634136585 1459762260202285225602439)
            ·
              refine ⟨2189643390303427838403659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459762260202285225602439 2189643390303427838403659)
              ·
                refine ⟨3284465085455141757605489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2189643390303427838403659 3284465085455141757605489)
                ·
                  refine ⟨2463348814091356318204117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3284465085455141757605489 2463348814091356318204117)
                  ·
                    refine ⟨57734737830266163707909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2463348814091356318204117 57734737830266163707909)
                    ·
                      rfl

theorem cell23_337314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_337314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337314 prefixEnd_337314 := by exact prefixLift 337314
  have htrace : WordTrace (prefixWord ++ tailWord_337314) baseStart_337314 baseEnd_337314 := by
    simpa [prefixWord, tailWord_337314, baseEnd_337314] using wordTrace_append hprefix tailTrace_337314
  have hstable : (prefixWord ++ tailWord_337314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337314).length < 2 ^ (prefixWord ++ tailWord_337314).sum := by decide
  have hdescent : baseEnd_337314 < baseStart_337314 := by decide
  rcases family_descends (prefixWord ++ tailWord_337314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337346 : List Nat := [3, 5, 2, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_337346 : Nat := 118140960795 + 337346 * 2 ^ 59
def prefixEnd_337346 : Nat := 4983230072969 + 3 ^ 40 * 337346 * 2
def baseEnd_337346 : Nat := 173220644871742365923581

theorem tailTrace_337346 : CollatzResearch.WordTrace tailWord_337346 prefixEnd_337346 173220644871742365923581 := by
  unfold tailWord_337346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3076004858965132738753973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8202679623907020636677261 3076004858965132738753973)
  ·
    refine ⟨288375455527981194258185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3076004858965132738753973 288375455527981194258185)
    ·
      refine ⟨216281591645985895693639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 288375455527981194258185 216281591645985895693639)
      ·
        refine ⟨324422387468978843540459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216281591645985895693639 324422387468978843540459)
        ·
          refine ⟨486633581203468265310689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324422387468978843540459 486633581203468265310689)
          ·
            refine ⟨364975185902601198983017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 486633581203468265310689 364975185902601198983017)
            ·
              refine ⟨273731389426950899237263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364975185902601198983017 273731389426950899237263)
              ·
                refine ⟨410597084140426348855895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273731389426950899237263 410597084140426348855895)
                ·
                  refine ⟨615895626210639523283843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410597084140426348855895 615895626210639523283843)
                  ·
                    refine ⟨923843439315959284925765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 615895626210639523283843 923843439315959284925765)
                    ·
                      refine ⟨173220644871742365923581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 923843439315959284925765 173220644871742365923581)
                      ·
                        rfl

theorem cell23_337346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_337346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337346 prefixEnd_337346 := by exact prefixLift 337346
  have htrace : WordTrace (prefixWord ++ tailWord_337346) baseStart_337346 baseEnd_337346 := by
    simpa [prefixWord, tailWord_337346, baseEnd_337346] using wordTrace_append hprefix tailTrace_337346
  have hstable : (prefixWord ++ tailWord_337346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337346).length < 2 ^ (prefixWord ++ tailWord_337346).sum := by decide
  have hdescent : baseEnd_337346 < baseStart_337346 := by decide
  rcases family_descends (prefixWord ++ tailWord_337346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337351 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 1, 4, 2]
def baseStart_337351 : Nat := 118140960795 + 337351 * 2 ^ 59
def prefixEnd_337351 : Nat := 4983230072969 + 3 ^ 40 * 337351 * 2
def baseEnd_337351 : Nat := 173223212275014846361057

theorem tailTrace_337351 : CollatzResearch.WordTrace tailWord_337351 prefixEnd_337351 173223212275014846361057 := by
  unfold tailWord_337351
  simp only [CollatzResearch.WordTrace]
  refine ⟨12304201800842416808947907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8202801200561611205965271 12304201800842416808947907)
  ·
    refine ⟨18456302701263625213421861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12304201800842416808947907 18456302701263625213421861)
    ·
      refine ⟨3460556756486929727516599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18456302701263625213421861 3460556756486929727516599)
      ·
        refine ⟨5190835134730394591274899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3460556756486929727516599 5190835134730394591274899)
        ·
          refine ⟨7786252702095591886912349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5190835134730394591274899 7786252702095591886912349)
          ·
            refine ⟨2919844763285846957592131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7786252702095591886912349 2919844763285846957592131)
            ·
              refine ⟨4379767144928770436388197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919844763285846957592131 4379767144928770436388197)
              ·
                refine ⟨821206339674144456822787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4379767144928770436388197 821206339674144456822787)
                ·
                  refine ⟨1231809509511216685234181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821206339674144456822787 1231809509511216685234181)
                  ·
                    refine ⟨230964283033353128481409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1231809509511216685234181 230964283033353128481409)
                    ·
                      refine ⟨173223212275014846361057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 230964283033353128481409 173223212275014846361057)
                      ·
                        rfl

theorem cell23_337351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_337351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337351 prefixEnd_337351 := by exact prefixLift 337351
  have htrace : WordTrace (prefixWord ++ tailWord_337351) baseStart_337351 baseEnd_337351 := by
    simpa [prefixWord, tailWord_337351, baseEnd_337351] using wordTrace_append hprefix tailTrace_337351
  have hstable : (prefixWord ++ tailWord_337351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337351).length < 2 ^ (prefixWord ++ tailWord_337351).sum := by decide
  have hdescent : baseEnd_337351 < baseStart_337351 := by decide
  rcases family_descends (prefixWord ++ tailWord_337351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337381 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 2, 2, 4]
def baseStart_337381 : Nat := 118140960795 + 337381 * 2 ^ 59
def prefixEnd_337381 : Nat := 4983230072969 + 3 ^ 40 * 337381 * 2
def baseEnd_337381 : Nat := 173238616694649728985919

theorem tailTrace_337381 : CollatzResearch.WordTrace tailWord_337381 prefixEnd_337381 173238616694649728985919 := by
  unfold tailWord_337381
  simp only [CollatzResearch.WordTrace]
  refine ⟨12305295990733731932539997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8203530660489154621693331 12305295990733731932539997)
  ·
    refine ⟨4614485996525149474702499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12305295990733731932539997 4614485996525149474702499)
    ·
      refine ⟨6921728994787724212053749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4614485996525149474702499 6921728994787724212053749)
      ·
        refine ⟨648912093261349144880039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6921728994787724212053749 648912093261349144880039)
        ·
          refine ⟨973368139892023717320059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648912093261349144880039 973368139892023717320059)
          ·
            refine ⟨1460052209838035575980089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973368139892023717320059 1460052209838035575980089)
            ·
              refine ⟨1095039157378526681985067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1460052209838035575980089 1095039157378526681985067)
              ·
                refine ⟨1642558736067790022977601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095039157378526681985067 1642558736067790022977601)
                ·
                  refine ⟨1231919052050842517233201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1642558736067790022977601 1231919052050842517233201)
                  ·
                    refine ⟨923939289038131887924901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1231919052050842517233201 923939289038131887924901)
                    ·
                      refine ⟨173238616694649728985919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 923939289038131887924901 173238616694649728985919)
                      ·
                        rfl

theorem cell23_337381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_337381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337381 prefixEnd_337381 := by exact prefixLift 337381
  have htrace : WordTrace (prefixWord ++ tailWord_337381) baseStart_337381 baseEnd_337381 := by
    simpa [prefixWord, tailWord_337381, baseEnd_337381] using wordTrace_append hprefix tailTrace_337381
  have hstable : (prefixWord ++ tailWord_337381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337381).length < 2 ^ (prefixWord ++ tailWord_337381).sum := by decide
  have hdescent : baseEnd_337381 < baseStart_337381 := by decide
  rcases family_descends (prefixWord ++ tailWord_337381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337404 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 1, 7]
def baseStart_337404 : Nat := 118140960795 + 337404 * 2 ^ 59
def prefixEnd_337404 : Nat := 4983230072969 + 3 ^ 40 * 337404 * 2
def baseEnd_337404 : Nat := 57750142249901046332771

theorem tailTrace_337404 : CollatzResearch.WordTrace tailWord_337404 prefixEnd_337404 57750142249901046332771 := by
  unfold tailWord_337404
  simp only [CollatzResearch.WordTrace]
  refine ⟨6153067434825203430313633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8204089913100271240418177 6153067434825203430313633)
  ·
    refine ⟨4614800576118902572735225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6153067434825203430313633 4614800576118902572735225)
    ·
      refine ⟨3461100432089176929551419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4614800576118902572735225 3461100432089176929551419)
      ·
        refine ⟨5191650648133765394327129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3461100432089176929551419 5191650648133765394327129)
        ·
          refine ⟨3893737986100324045745347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5191650648133765394327129 3893737986100324045745347)
          ·
            refine ⟨5840606979150486068618021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3893737986100324045745347 5840606979150486068618021)
            ·
              refine ⟨1095113808590716137865879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5840606979150486068618021 1095113808590716137865879)
              ·
                refine ⟨1642670712886074206798819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095113808590716137865879 1642670712886074206798819)
                ·
                  refine ⟨2464006069329111310198229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642670712886074206798819 2464006069329111310198229)
                  ·
                    refine ⟨57750142249901046332771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2464006069329111310198229 57750142249901046332771)
                    ·
                      rfl

theorem cell23_337404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_337404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337404 prefixEnd_337404 := by exact prefixLift 337404
  have htrace : WordTrace (prefixWord ++ tailWord_337404) baseStart_337404 baseEnd_337404 := by
    simpa [prefixWord, tailWord_337404, baseEnd_337404] using wordTrace_append hprefix tailTrace_337404
  have hstable : (prefixWord ++ tailWord_337404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337404).length < 2 ^ (prefixWord ++ tailWord_337404).sum := by decide
  have hdescent : baseEnd_337404 < baseStart_337404 := by decide
  rcases family_descends (prefixWord ++ tailWord_337404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337504 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 7]
def baseStart_337504 : Nat := 118140960795 + 337504 * 2 ^ 59
def prefixEnd_337504 : Nat := 4983230072969 + 3 ^ 40 * 337504 * 2
def baseEnd_337504 : Nat := 173301774815152747747853

theorem tailTrace_337504 : CollatzResearch.WordTrace tailWord_337504 prefixEnd_337504 173301774815152747747853 := by
  unfold tailWord_337504
  simp only [CollatzResearch.WordTrace]
  refine ⟨6154891084644061969633783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8206521446192082626178377 6154891084644061969633783)
  ·
    refine ⟨9232336626966092954450675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6154891084644061969633783 9232336626966092954450675)
    ·
      refine ⟨13848504940449139431676013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9232336626966092954450675 13848504940449139431676013)
      ·
        refine ⟨5193189352668427286878505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13848504940449139431676013 5193189352668427286878505)
        ·
          refine ⟨3894892014501320465158879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5193189352668427286878505 3894892014501320465158879)
          ·
            refine ⟨5842338021751980697738319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3894892014501320465158879 5842338021751980697738319)
            ·
              refine ⟨8763507032627971046607479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5842338021751980697738319 8763507032627971046607479)
              ·
                refine ⟨13145260548941956569911219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8763507032627971046607479 13145260548941956569911219)
                ·
                  refine ⟨19717890823412934854866829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13145260548941956569911219 19717890823412934854866829)
                  ·
                    refine ⟨7394209058779850570575061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19717890823412934854866829 7394209058779850570575061)
                    ·
                      refine ⟨173301774815152747747853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7394209058779850570575061 173301774815152747747853)
                      ·
                        rfl

theorem cell23_337504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_337504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337504 prefixEnd_337504 := by exact prefixLift 337504
  have htrace : WordTrace (prefixWord ++ tailWord_337504) baseStart_337504 baseEnd_337504 := by
    simpa [prefixWord, tailWord_337504, baseEnd_337504] using wordTrace_append hprefix tailTrace_337504
  have hstable : (prefixWord ++ tailWord_337504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337504).length < 2 ^ (prefixWord ++ tailWord_337504).sum := by decide
  have hdescent : baseEnd_337504 < baseStart_337504 := by decide
  rcases family_descends (prefixWord ++ tailWord_337504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337508 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 5, 1, 3]
def baseStart_337508 : Nat := 118140960795 + 337508 * 2 ^ 59
def prefixEnd_337508 : Nat := 4983230072969 + 3 ^ 40 * 337508 * 2
def baseEnd_337508 : Nat := 173303828737770732097835

theorem tailTrace_337508 : CollatzResearch.WordTrace tailWord_337508 prefixEnd_337508 173303828737770732097835 := by
  unfold tailWord_337508
  simp only [CollatzResearch.WordTrace]
  refine ⟨6154964030636816311206589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8206618707515755081608785 6154964030636816311206589)
  ·
    refine ⟨2308111511488806116702471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6154964030636816311206589 2308111511488806116702471)
    ·
      refine ⟨3462167267233209175053707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2308111511488806116702471 3462167267233209175053707)
      ·
        refine ⟨5193250900849813762580561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3462167267233209175053707 5193250900849813762580561)
        ·
          refine ⟨3894938175637360321935421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5193250900849813762580561 3894938175637360321935421)
          ·
            refine ⟨1460601815864010120725783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3894938175637360321935421 1460601815864010120725783)
            ·
              refine ⟨2190902723796015181088675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460601815864010120725783 2190902723796015181088675)
              ·
                refine ⟨3286354085694022771633013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190902723796015181088675 3286354085694022771633013)
                ·
                  refine ⟨308095695533814634840595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3286354085694022771633013 308095695533814634840595)
                  ·
                    refine ⟨462143543300721952260893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 308095695533814634840595 462143543300721952260893)
                    ·
                      refine ⟨173303828737770732097835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 462143543300721952260893 173303828737770732097835)
                      ·
                        rfl

theorem cell23_337508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_337508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337508 prefixEnd_337508 := by exact prefixLift 337508
  have htrace : WordTrace (prefixWord ++ tailWord_337508) baseStart_337508 baseEnd_337508 := by
    simpa [prefixWord, tailWord_337508, baseEnd_337508] using wordTrace_append hprefix tailTrace_337508
  have hstable : (prefixWord ++ tailWord_337508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337508).length < 2 ^ (prefixWord ++ tailWord_337508).sum := by decide
  have hdescent : baseEnd_337508 < baseStart_337508 := by decide
  rcases family_descends (prefixWord ++ tailWord_337508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337511 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 3, 5]
def baseStart_337511 : Nat := 118140960795 + 337511 * 2 ^ 59
def prefixEnd_337511 : Nat := 4983230072969 + 3 ^ 40 * 337511 * 2
def baseEnd_337511 : Nat := 57768456393244740120107

theorem tailTrace_337511 : CollatzResearch.WordTrace tailWord_337511 prefixEnd_337511 57768456393244740120107 := by
  unfold tailWord_337511
  simp only [CollatzResearch.WordTrace]
  refine ⟨12310037480262764134772387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8206691653508509423181591 12310037480262764134772387)
  ·
    refine ⟨18465056220394146202158581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12310037480262764134772387 18465056220394146202158581)
    ·
      refine ⟨1731099020661951206452367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18465056220394146202158581 1731099020661951206452367)
      ·
        refine ⟨2596648530992926809678551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1731099020661951206452367 2596648530992926809678551)
        ·
          refine ⟨3894972796489390214517827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2596648530992926809678551 3894972796489390214517827)
          ·
            refine ⟨5842459194734085321776741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3894972796489390214517827 5842459194734085321776741)
            ·
              refine ⟨1095461099012640997833139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5842459194734085321776741 1095461099012640997833139)
              ·
                refine ⟨1643191648518961496749709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095461099012640997833139 1643191648518961496749709)
                ·
                  refine ⟨616196868194610561281141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1643191648518961496749709 616196868194610561281141)
                  ·
                    refine ⟨57768456393244740120107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 616196868194610561281141 57768456393244740120107)
                    ·
                      rfl

theorem cell23_337511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_337511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337511 prefixEnd_337511 := by exact prefixLift 337511
  have htrace : WordTrace (prefixWord ++ tailWord_337511) baseStart_337511 baseEnd_337511 := by
    simpa [prefixWord, tailWord_337511, baseEnd_337511] using wordTrace_append hprefix tailTrace_337511
  have hstable : (prefixWord ++ tailWord_337511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337511).length < 2 ^ (prefixWord ++ tailWord_337511).sum := by decide
  have hdescent : baseEnd_337511 < baseStart_337511 := by decide
  rcases family_descends (prefixWord ++ tailWord_337511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337561 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 1, 2, 4]
def baseStart_337561 : Nat := 118140960795 + 337561 * 2 ^ 59
def prefixEnd_337561 : Nat := 4983230072969 + 3 ^ 40 * 337561 * 2
def baseEnd_337561 : Nat := 173331043212459024735091

theorem tailTrace_337561 : CollatzResearch.WordTrace tailWord_337561 prefixEnd_337561 173331043212459024735091 := by
  unfold tailWord_337561
  simp only [CollatzResearch.WordTrace]
  refine ⟨12311861130081622674092537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8207907420054415116061691 12311861130081622674092537)
  ·
    refine ⟨9233895847561217005569403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12311861130081622674092537 9233895847561217005569403)
    ·
      refine ⟨13850843771341825508354105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9233895847561217005569403 13850843771341825508354105)
      ·
        refine ⟨10388132828506369131265579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13850843771341825508354105 10388132828506369131265579)
        ·
          refine ⟨15582199242759553696898369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10388132828506369131265579 15582199242759553696898369)
          ·
            refine ⟨11686649432069665272673777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15582199242759553696898369 11686649432069665272673777)
            ·
              refine ⟨8764987074052248954505333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11686649432069665272673777 8764987074052248954505333)
              ·
                refine ⟨821717538192398339484875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8764987074052248954505333 821717538192398339484875)
                ·
                  refine ⟨1232576307288597509227313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821717538192398339484875 1232576307288597509227313)
                  ·
                    refine ⟨924432230466448131920485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1232576307288597509227313 924432230466448131920485)
                    ·
                      refine ⟨173331043212459024735091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 924432230466448131920485 173331043212459024735091)
                      ·
                        rfl

theorem cell23_337561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_337561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337561 prefixEnd_337561 := by exact prefixLift 337561
  have htrace : WordTrace (prefixWord ++ tailWord_337561) baseStart_337561 baseEnd_337561 := by
    simpa [prefixWord, tailWord_337561, baseEnd_337561] using wordTrace_append hprefix tailTrace_337561
  have hstable : (prefixWord ++ tailWord_337561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337561).length < 2 ^ (prefixWord ++ tailWord_337561).sum := by decide
  have hdescent : baseEnd_337561 < baseStart_337561 := by decide
  rcases family_descends (prefixWord ++ tailWord_337561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337599 : List Nat := [1, 1, 2, 2, 2, 3, 5, 2, 1, 2, 2]
def baseStart_337599 : Nat := 118140960795 + 337599 * 2 ^ 59
def prefixEnd_337599 : Nat := 4983230072969 + 3 ^ 40 * 337599 * 2
def baseEnd_337599 : Nat := 173350555477329876059917

theorem tailTrace_337599 : CollatzResearch.WordTrace tailWord_337599 prefixEnd_337599 173350555477329876059917 := by
  unfold tailWord_337599
  simp only [CollatzResearch.WordTrace]
  refine ⟨12313247103943955163975851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8208831402629303442650567 12313247103943955163975851)
  ·
    refine ⟨18469870655915932745963777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12313247103943955163975851 18469870655915932745963777)
    ·
      refine ⟨13852402991936949559472833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18469870655915932745963777 13852402991936949559472833)
      ·
        refine ⟨10389302243952712169604625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13852402991936949559472833 10389302243952712169604625)
        ·
          refine ⟨7791976682964534127203469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10389302243952712169604625 7791976682964534127203469)
          ·
            refine ⟨2921991256111700297701301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7791976682964534127203469 2921991256111700297701301)
            ·
              refine ⟨273936680260471902909497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2921991256111700297701301 273936680260471902909497)
              ·
                refine ⟨205452510195353927182123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273936680260471902909497 205452510195353927182123)
                ·
                  refine ⟨308178765293030890773185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205452510195353927182123 308178765293030890773185)
                  ·
                    refine ⟨231134073969773168079889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 308178765293030890773185 231134073969773168079889)
                    ·
                      refine ⟨173350555477329876059917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 231134073969773168079889 173350555477329876059917)
                      ·
                        rfl

theorem cell23_337599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 2, 1, 2, 2].length) (baseStart_337599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337599 prefixEnd_337599 := by exact prefixLift 337599
  have htrace : WordTrace (prefixWord ++ tailWord_337599) baseStart_337599 baseEnd_337599 := by
    simpa [prefixWord, tailWord_337599, baseEnd_337599] using wordTrace_append hprefix tailTrace_337599
  have hstable : (prefixWord ++ tailWord_337599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337599).length < 2 ^ (prefixWord ++ tailWord_337599).sum := by decide
  have hdescent : baseEnd_337599 < baseStart_337599 := by decide
  rcases family_descends (prefixWord ++ tailWord_337599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337625 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 3, 3, 2]
def baseStart_337625 : Nat := 118140960795 + 337625 * 2 ^ 59
def prefixEnd_337625 : Nat := 4983230072969 + 3 ^ 40 * 337625 * 2
def baseEnd_337625 : Nat := 173363905974346774334797

theorem tailTrace_337625 : CollatzResearch.WordTrace tailWord_337625 prefixEnd_337625 173363905974346774334797 := by
  unfold tailWord_337625
  simp only [CollatzResearch.WordTrace]
  refine ⟨12314195401849761604422329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8209463601233174402948219 12314195401849761604422329)
  ·
    refine ⟨9235646551387321203316747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12314195401849761604422329 9235646551387321203316747)
    ·
      refine ⟨13853469827080981804975121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9235646551387321203316747 13853469827080981804975121)
      ·
        refine ⟨10390102370310736353731341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13853469827080981804975121 10390102370310736353731341)
        ·
          refine ⟨3896288388866526132649253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10390102370310736353731341 3896288388866526132649253)
          ·
            refine ⟨730554072912473649871735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3896288388866526132649253 730554072912473649871735)
            ·
              refine ⟨1095831109368710474807603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730554072912473649871735 1095831109368710474807603)
              ·
                refine ⟨1643746664053065712211405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095831109368710474807603 1643746664053065712211405)
                ·
                  refine ⟨616404999019899642079277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1643746664053065712211405 616404999019899642079277)
                  ·
                    refine ⟨231151874632462365779729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 616404999019899642079277 231151874632462365779729)
                    ·
                      refine ⟨173363905974346774334797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 231151874632462365779729 173363905974346774334797)
                      ·
                        rfl

theorem cell23_337625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 3, 2].length) (baseStart_337625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337625 prefixEnd_337625 := by exact prefixLift 337625
  have htrace : WordTrace (prefixWord ++ tailWord_337625) baseStart_337625 baseEnd_337625 := by
    simpa [prefixWord, tailWord_337625, baseEnd_337625] using wordTrace_append hprefix tailTrace_337625
  have hstable : (prefixWord ++ tailWord_337625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337625).length < 2 ^ (prefixWord ++ tailWord_337625).sum := by decide
  have hdescent : baseEnd_337625 < baseStart_337625 := by decide
  rcases family_descends (prefixWord ++ tailWord_337625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337655 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 4, 2, 2]
def baseStart_337655 : Nat := 118140960795 + 337655 * 2 ^ 59
def prefixEnd_337655 : Nat := 4983230072969 + 3 ^ 40 * 337655 * 2
def baseEnd_337655 : Nat := 173379310393981656959659

theorem tailTrace_337655 : CollatzResearch.WordTrace tailWord_337655 prefixEnd_337655 173379310393981656959659 := by
  unfold tailWord_337655
  simp only [CollatzResearch.WordTrace]
  refine ⟨12315289591741076728014419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8210193061160717818676279 12315289591741076728014419)
  ·
    refine ⟨18472934387611615092021629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12315289591741076728014419 18472934387611615092021629)
    ·
      refine ⟨6927350395354355659508111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18472934387611615092021629 6927350395354355659508111)
      ·
        refine ⟨10391025593031533489262167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6927350395354355659508111 10391025593031533489262167)
        ·
          refine ⟨15586538389547300233893251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10391025593031533489262167 15586538389547300233893251)
          ·
            refine ⟨23379807584320950350839877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15586538389547300233893251 23379807584320950350839877)
            ·
              refine ⟨4383713922060178190782477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23379807584320950350839877 4383713922060178190782477)
              ·
                refine ⟨1643892720772566821543429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4383713922060178190782477 1643892720772566821543429)
                ·
                  refine ⟨308229885144856279039393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1643892720772566821543429 308229885144856279039393)
                  ·
                    refine ⟨231172413858642209279545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 308229885144856279039393 231172413858642209279545)
                    ·
                      refine ⟨173379310393981656959659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 231172413858642209279545 173379310393981656959659)
                      ·
                        rfl

theorem cell23_337655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 2, 2].length) (baseStart_337655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337655 prefixEnd_337655 := by exact prefixLift 337655
  have htrace : WordTrace (prefixWord ++ tailWord_337655) baseStart_337655 baseEnd_337655 := by
    simpa [prefixWord, tailWord_337655, baseEnd_337655] using wordTrace_append hprefix tailTrace_337655
  have hstable : (prefixWord ++ tailWord_337655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337655).length < 2 ^ (prefixWord ++ tailWord_337655).sum := by decide
  have hdescent : baseEnd_337655 < baseStart_337655 := by decide
  rcases family_descends (prefixWord ++ tailWord_337655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337668 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_337668 : Nat := 118140960795 + 337668 * 2 ^ 59
def prefixEnd_337668 : Nat := 4983230072969 + 3 ^ 40 * 337668 * 2
def baseEnd_337668 : Nat := 173385985642490106097099

theorem tailTrace_337668 : CollatzResearch.WordTrace tailWord_337668 prefixEnd_337668 173385985642490106097099 := by
  unfold tailWord_337668
  simp only [CollatzResearch.WordTrace]
  refine ⟨6157881870346989974118829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8210509160462653298825105 6157881870346989974118829)
  ·
    refine ⟨2309205701380121240294561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6157881870346989974118829 2309205701380121240294561)
    ·
      refine ⟨1731904276035090930220921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2309205701380121240294561 1731904276035090930220921)
      ·
        refine ⟨1298928207026318197665691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1731904276035090930220921 1298928207026318197665691)
        ·
          refine ⟨1948392310539477296498537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298928207026318197665691 1948392310539477296498537)
          ·
            refine ⟨1461294232904607972373903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1948392310539477296498537 1461294232904607972373903)
            ·
              refine ⟨2191941349356911958560855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1461294232904607972373903 2191941349356911958560855)
              ·
                refine ⟨3287912024035367937841283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191941349356911958560855 3287912024035367937841283)
                ·
                  refine ⟨4931868036053051906761925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3287912024035367937841283 4931868036053051906761925)
                  ·
                    refine ⟨924725256759947232517861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4931868036053051906761925 924725256759947232517861)
                    ·
                      refine ⟨173385985642490106097099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 924725256759947232517861 173385985642490106097099)
                      ·
                        rfl

theorem cell23_337668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_337668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337668 prefixEnd_337668 := by exact prefixLift 337668
  have htrace : WordTrace (prefixWord ++ tailWord_337668) baseStart_337668 baseEnd_337668 := by
    simpa [prefixWord, tailWord_337668, baseEnd_337668] using wordTrace_append hprefix tailTrace_337668
  have hstable : (prefixWord ++ tailWord_337668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337668).length < 2 ^ (prefixWord ++ tailWord_337668).sum := by decide
  have hdescent : baseEnd_337668 < baseStart_337668 := by decide
  rcases family_descends (prefixWord ++ tailWord_337668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337672 : List Nat := [2, 1, 3, 2, 2, 1, 1, 5, 2, 2, 2]
def baseStart_337672 : Nat := 118140960795 + 337672 * 2 ^ 59
def prefixEnd_337672 : Nat := 4983230072969 + 3 ^ 40 * 337672 * 2
def baseEnd_337672 : Nat := 173388039565108090447081

theorem tailTrace_337672 : CollatzResearch.WordTrace tailWord_337672 prefixEnd_337672 173388039565108090447081 := by
  unfold tailWord_337672
  simp only [CollatzResearch.WordTrace]
  refine ⟨6157954816339744315691635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8210606421786325754255513 6157954816339744315691635)
  ·
    refine ⟨9236932224509616473537453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6157954816339744315691635 9236932224509616473537453)
    ·
      refine ⟨3463849584191106177576545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9236932224509616473537453 3463849584191106177576545)
      ·
        refine ⟨2597887188143329633182409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3463849584191106177576545 2597887188143329633182409)
        ·
          refine ⟨1948415391107497224886807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2597887188143329633182409 1948415391107497224886807)
          ·
            refine ⟨2922623086661245837330211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948415391107497224886807 2922623086661245837330211)
            ·
              refine ⟨4383934629991868755995317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2922623086661245837330211 4383934629991868755995317)
              ·
                refine ⟨410993871561737695874561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4383934629991868755995317 410993871561737695874561)
                ·
                  refine ⟨308245403671303271905921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 410993871561737695874561 308245403671303271905921)
                  ·
                    refine ⟨231184052753477453929441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 308245403671303271905921 231184052753477453929441)
                    ·
                      refine ⟨173388039565108090447081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 231184052753477453929441 173388039565108090447081)
                      ·
                        rfl

theorem cell23_337672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_337672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337672 prefixEnd_337672 := by exact prefixLift 337672
  have htrace : WordTrace (prefixWord ++ tailWord_337672) baseStart_337672 baseEnd_337672 := by
    simpa [prefixWord, tailWord_337672, baseEnd_337672] using wordTrace_append hprefix tailTrace_337672
  have hstable : (prefixWord ++ tailWord_337672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337672).length < 2 ^ (prefixWord ++ tailWord_337672).sum := by decide
  have hdescent : baseEnd_337672 < baseStart_337672 := by decide
  rcases family_descends (prefixWord ++ tailWord_337672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337691 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 1, 7]
def baseStart_337691 : Nat := 118140960795 + 337691 * 2 ^ 59
def prefixEnd_337691 : Nat := 4983230072969 + 3 ^ 40 * 337691 * 2
def baseEnd_337691 : Nat := 57799265232514505369831

theorem tailTrace_337691 : CollatzResearch.WordTrace tailWord_337691 prefixEnd_337691 57799265232514505369831 := by
  unfold tailWord_337691
  simp only [CollatzResearch.WordTrace]
  refine ⟨12316602619610654876324927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8211068413073769917549951 12316602619610654876324927)
  ·
    refine ⟨18474903929415982314487391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12316602619610654876324927 18474903929415982314487391)
    ·
      refine ⟨27712355894123973471731087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18474903929415982314487391 27712355894123973471731087)
      ·
        refine ⟨41568533841185960207596631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27712355894123973471731087 41568533841185960207596631)
        ·
          refine ⟨62352800761778940311394947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41568533841185960207596631 62352800761778940311394947)
          ·
            refine ⟨93529201142668410467092421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62352800761778940311394947 93529201142668410467092421)
            ·
              refine ⟨17536725214250326962579829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93529201142668410467092421 17536725214250326962579829)
              ·
                refine ⟨1644067988835968152741859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17536725214250326962579829 1644067988835968152741859)
                ·
                  refine ⟨2466101983253952229112789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644067988835968152741859 2466101983253952229112789)
                  ·
                    refine ⟨57799265232514505369831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2466101983253952229112789 57799265232514505369831)
                    ·
                      rfl

theorem cell23_337691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 7].length) (baseStart_337691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337691 prefixEnd_337691 := by exact prefixLift 337691
  have htrace : WordTrace (prefixWord ++ tailWord_337691) baseStart_337691 baseEnd_337691 := by
    simpa [prefixWord, tailWord_337691, baseEnd_337691] using wordTrace_append hprefix tailTrace_337691
  have hstable : (prefixWord ++ tailWord_337691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337691).length < 2 ^ (prefixWord ++ tailWord_337691).sum := by decide
  have hdescent : baseEnd_337691 < baseStart_337691 := by decide
  rcases family_descends (prefixWord ++ tailWord_337691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337695 : List Nat := [1, 1, 2, 4, 2, 1, 4, 3, 5]
def baseStart_337695 : Nat := 118140960795 + 337695 * 2 ^ 59
def prefixEnd_337695 : Nat := 4983230072969 + 3 ^ 40 * 337695 * 2
def baseEnd_337695 : Nat := 19266649957795722273275

theorem tailTrace_337695 : CollatzResearch.WordTrace tailWord_337695 prefixEnd_337695 19266649957795722273275 := by
  unfold tailWord_337695
  simp only [CollatzResearch.WordTrace]
  refine ⟨12316748511596163559470539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8211165674397442372980359 12316748511596163559470539)
  ·
    refine ⟨18475122767394245339205809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12316748511596163559470539 18475122767394245339205809)
    ·
      refine ⟨13856342075545684004404357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18475122767394245339205809 13856342075545684004404357)
      ·
        refine ⟨2598064139164815750825817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13856342075545684004404357 2598064139164815750825817)
        ·
          refine ⟨1948548104373611813119363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2598064139164815750825817 1948548104373611813119363)
          ·
            refine ⟨2922822156560417719679045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948548104373611813119363 2922822156560417719679045)
            ·
              refine ⟨548029154355078322439821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2922822156560417719679045 548029154355078322439821)
              ·
                refine ⟨205510932883154370914933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 548029154355078322439821 205510932883154370914933)
                ·
                  refine ⟨19266649957795722273275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205510932883154370914933 19266649957795722273275)
                  ·
                    rfl

theorem cell23_337695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 5].length) (baseStart_337695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337695 prefixEnd_337695 := by exact prefixLift 337695
  have htrace : WordTrace (prefixWord ++ tailWord_337695) baseStart_337695 baseEnd_337695 := by
    simpa [prefixWord, tailWord_337695, baseEnd_337695] using wordTrace_append hprefix tailTrace_337695
  have hstable : (prefixWord ++ tailWord_337695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337695).length < 2 ^ (prefixWord ++ tailWord_337695).sum := by decide
  have hdescent : baseEnd_337695 < baseStart_337695 := by decide
  rcases family_descends (prefixWord ++ tailWord_337695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337762 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_337762 : Nat := 118140960795 + 337762 * 2 ^ 59
def prefixEnd_337762 : Nat := 4983230072969 + 3 ^ 40 * 337762 * 2
def baseEnd_337762 : Nat := 173434252824012738321667

theorem tailTrace_337762 : CollatzResearch.WordTrace tailWord_337762 prefixEnd_337762 173434252824012738321667 := by
  unfold tailWord_337762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3079798050588358500539885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8212794801568956001439693 3079798050588358500539885)
  ·
    refine ⟨1154924268970634437702457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3079798050588358500539885 1154924268970634437702457)
    ·
      refine ⟨866193201727975828276843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1154924268970634437702457 866193201727975828276843)
      ·
        refine ⟨1299289802591963742415265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866193201727975828276843 1299289802591963742415265)
        ·
          refine ⟨974467351943972806811449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1299289802591963742415265 974467351943972806811449)
          ·
            refine ⟨730850513957979605108587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 974467351943972806811449 730850513957979605108587)
            ·
              refine ⟨1096275770936969407662881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730850513957979605108587 1096275770936969407662881)
              ·
                refine ⟨822206828202727055747161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1096275770936969407662881 822206828202727055747161)
                ·
                  refine ⟨616655121152045291810371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 822206828202727055747161 616655121152045291810371)
                  ·
                    refine ⟨924982681728067937715557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 616655121152045291810371 924982681728067937715557)
                    ·
                      refine ⟨173434252824012738321667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 924982681728067937715557 173434252824012738321667)
                      ·
                        rfl

theorem cell23_337762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_337762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337762 prefixEnd_337762 := by exact prefixLift 337762
  have htrace : WordTrace (prefixWord ++ tailWord_337762) baseStart_337762 baseEnd_337762 := by
    simpa [prefixWord, tailWord_337762, baseEnd_337762] using wordTrace_append hprefix tailTrace_337762
  have hstable : (prefixWord ++ tailWord_337762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337762).length < 2 ^ (prefixWord ++ tailWord_337762).sum := by decide
  have hdescent : baseEnd_337762 < baseStart_337762 := by decide
  rcases family_descends (prefixWord ++ tailWord_337762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337768 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 8]
def baseStart_337768 : Nat := 118140960795 + 337768 * 2 ^ 59
def prefixEnd_337768 : Nat := 4983230072969 + 3 ^ 40 * 337768 * 2
def baseEnd_337768 : Nat := 19270814856437746094071

theorem tailTrace_337768 : CollatzResearch.WordTrace tailWord_337768 prefixEnd_337768 19270814856437746094071 := by
  unfold tailWord_337768
  simp only [CollatzResearch.WordTrace]
  refine ⟨6159705520165848513438979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8212940693554464684585305 6159705520165848513438979)
  ·
    refine ⟨9239558280248772770158469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6159705520165848513438979 9239558280248772770158469)
    ·
      refine ⟨1732417177546644894404713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9239558280248772770158469 1732417177546644894404713)
      ·
        refine ⟨1299312883159983670803535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1732417177546644894404713 1299312883159983670803535)
        ·
          refine ⟨1948969324739975506205303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1299312883159983670803535 1948969324739975506205303)
          ·
            refine ⟨2923453987109963259307955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948969324739975506205303 2923453987109963259307955)
            ·
              refine ⟨4385180980664944888961933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923453987109963259307955 4385180980664944888961933)
              ·
                refine ⟨1644442867749354333360725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4385180980664944888961933 1644442867749354333360725)
                ·
                  refine ⟨19270814856437746094071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1644442867749354333360725 19270814856437746094071)
                  ·
                    rfl

theorem cell23_337768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 8].length) (baseStart_337768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337768 prefixEnd_337768 := by exact prefixLift 337768
  have htrace : WordTrace (prefixWord ++ tailWord_337768) baseStart_337768 baseEnd_337768 := by
    simpa [prefixWord, tailWord_337768, baseEnd_337768] using wordTrace_append hprefix tailTrace_337768
  have hstable : (prefixWord ++ tailWord_337768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337768).length < 2 ^ (prefixWord ++ tailWord_337768).sum := by decide
  have hdescent : baseEnd_337768 < baseStart_337768 := by decide
  rcases family_descends (prefixWord ++ tailWord_337768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337772 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 3, 4]
def baseStart_337772 : Nat := 118140960795 + 337772 * 2 ^ 59
def prefixEnd_337772 : Nat := 4983230072969 + 3 ^ 40 * 337772 * 2
def baseEnd_337772 : Nat := 57813129210185899732207

theorem tailTrace_337772 : CollatzResearch.WordTrace tailWord_337772 prefixEnd_337772 57813129210185899732207 := by
  unfold tailWord_337772
  simp only [CollatzResearch.WordTrace]
  refine ⟨6159778466158602855011785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8213037954878137140015713 6159778466158602855011785)
  ·
    refine ⟨4619833849618952141258839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6159778466158602855011785 4619833849618952141258839)
    ·
      refine ⟨6929750774428428211888259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4619833849618952141258839 6929750774428428211888259)
      ·
        refine ⟨10394626161642642317832389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6929750774428428211888259 10394626161642642317832389)
        ·
          refine ⟨1948992405307995434593573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10394626161642642317832389 1948992405307995434593573)
          ·
            refine ⟨365436075995249143986295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1948992405307995434593573 365436075995249143986295)
            ·
              refine ⟨548154113992873715979443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365436075995249143986295 548154113992873715979443)
              ·
                refine ⟨822231170989310573969165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548154113992873715979443 822231170989310573969165)
                ·
                  refine ⟨308336689120991465238437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822231170989310573969165 308336689120991465238437)
                  ·
                    refine ⟨57813129210185899732207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 308336689120991465238437 57813129210185899732207)
                    ·
                      rfl

theorem cell23_337772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_337772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337772 prefixEnd_337772 := by exact prefixLift 337772
  have htrace : WordTrace (prefixWord ++ tailWord_337772) baseStart_337772 baseEnd_337772 := by
    simpa [prefixWord, tailWord_337772, baseEnd_337772] using wordTrace_append hprefix tailTrace_337772
  have hstable : (prefixWord ++ tailWord_337772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337772).length < 2 ^ (prefixWord ++ tailWord_337772).sum := by decide
  have hdescent : baseEnd_337772 < baseStart_337772 := by decide
  rcases family_descends (prefixWord ++ tailWord_337772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337823 : List Nat := [1, 1, 2, 5, 4, 1, 2, 2, 1, 4]
def baseStart_337823 : Nat := 118140960795 + 337823 * 2 ^ 59
def prefixEnd_337823 : Nat := 4983230072969 + 3 ^ 40 * 337823 * 2
def baseEnd_337823 : Nat := 57821858381312333219629

theorem tailTrace_337823 : CollatzResearch.WordTrace tailWord_337823 prefixEnd_337823 57821858381312333219629 := by
  unfold tailWord_337823
  simp only [CollatzResearch.WordTrace]
  refine ⟨12321417055132441420130123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8214278036754960946753415 12321417055132441420130123)
  ·
    refine ⟨18482125582698662130195185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12321417055132441420130123 18482125582698662130195185)
    ·
      refine ⟨13861594187023996597646389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18482125582698662130195185 13861594187023996597646389)
      ·
        refine ⟨1299524455033499681029349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13861594187023996597646389 1299524455033499681029349)
        ·
          refine ⟨243660835318781190193003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1299524455033499681029349 243660835318781190193003)
          ·
            refine ⟨365491252978171785289505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243660835318781190193003 365491252978171785289505)
            ·
              refine ⟨274118439733628838967129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365491252978171785289505 274118439733628838967129)
              ·
                refine ⟨205588829800221629225347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274118439733628838967129 205588829800221629225347)
                ·
                  refine ⟨308383244700332443838021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205588829800221629225347 308383244700332443838021)
                  ·
                    refine ⟨57821858381312333219629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 308383244700332443838021 57821858381312333219629)
                    ·
                      rfl

theorem cell23_337823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 1, 4].length) (baseStart_337823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337823 prefixEnd_337823 := by exact prefixLift 337823
  have htrace : WordTrace (prefixWord ++ tailWord_337823) baseStart_337823 baseEnd_337823 := by
    simpa [prefixWord, tailWord_337823, baseEnd_337823] using wordTrace_append hprefix tailTrace_337823
  have hstable : (prefixWord ++ tailWord_337823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337823).length < 2 ^ (prefixWord ++ tailWord_337823).sum := by decide
  have hdescent : baseEnd_337823 < baseStart_337823 := by decide
  rcases family_descends (prefixWord ++ tailWord_337823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337845 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 1, 6]
def baseStart_337845 : Nat := 118140960795 + 337845 * 2 ^ 59
def prefixEnd_337845 : Nat := 4983230072969 + 3 ^ 40 * 337845 * 2
def baseEnd_337845 : Nat := 57825623906111971194595

theorem tailTrace_337845 : CollatzResearch.WordTrace tailWord_337845 prefixEnd_337845 57825623906111971194595 := by
  unfold tailWord_337845
  simp only [CollatzResearch.WordTrace]
  refine ⟨12322219461052739177430989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8214812974035159451620659 12322219461052739177430989)
  ·
    refine ⟨4620832297894777191536621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12322219461052739177430989 4620832297894777191536621)
    ·
      refine ⟨1732812111710541446826233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4620832297894777191536621 1732812111710541446826233)
      ·
        refine ⟨1299609083782906085119675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1732812111710541446826233 1299609083782906085119675)
        ·
          refine ⟨1949413625674359127679513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1299609083782906085119675 1949413625674359127679513)
          ·
            refine ⟨1462060219255769345759635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1949413625674359127679513 1462060219255769345759635)
            ·
              refine ⟨2193090328883654018639453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462060219255769345759635 2193090328883654018639453)
              ·
                refine ⟨822408873331370256989795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2193090328883654018639453 822408873331370256989795)
                ·
                  refine ⟨1233613309997055385484693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822408873331370256989795 1233613309997055385484693)
                  ·
                    refine ⟨57825623906111971194595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1233613309997055385484693 57825623906111971194595)
                    ·
                      rfl

theorem cell23_337845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_337845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337845 prefixEnd_337845 := by exact prefixLift 337845
  have htrace : WordTrace (prefixWord ++ tailWord_337845) baseStart_337845 baseEnd_337845 := by
    simpa [prefixWord, tailWord_337845, baseEnd_337845] using wordTrace_append hprefix tailTrace_337845
  have hstable : (prefixWord ++ tailWord_337845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337845).length < 2 ^ (prefixWord ++ tailWord_337845).sum := by decide
  have hdescent : baseEnd_337845 < baseStart_337845 := by decide
  rcases family_descends (prefixWord ++ tailWord_337845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337855 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 3]
def baseStart_337855 : Nat := 118140960795 + 337855 * 2 ^ 59
def prefixEnd_337855 : Nat := 4983230072969 + 3 ^ 40 * 337855 * 2
def baseEnd_337855 : Nat := 173482006524880874458739

theorem tailTrace_337855 : CollatzResearch.WordTrace tailWord_337855 prefixEnd_337855 173482006524880874458739 := by
  unfold tailWord_337855
  simp only [CollatzResearch.WordTrace]
  refine ⟨12322584191016510885295019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8215056127344340590196679 12322584191016510885295019)
  ·
    refine ⟨18483876286524766327942529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12322584191016510885295019 18483876286524766327942529)
    ·
      refine ⟨13862907214893574745956897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18483876286524766327942529 13862907214893574745956897)
      ·
        refine ⟨10397180411170181059467673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13862907214893574745956897 10397180411170181059467673)
        ·
          refine ⟨7797885308377635794600755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10397180411170181059467673 7797885308377635794600755)
          ·
            refine ⟨11696827962566453691901133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7797885308377635794600755 11696827962566453691901133)
            ·
              refine ⟨4386310485962420134462925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11696827962566453691901133 4386310485962420134462925)
              ·
                refine ⟨1644866432235907550423597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4386310485962420134462925 1644866432235907550423597)
                ·
                  refine ⟨616824912088465331408849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1644866432235907550423597 616824912088465331408849)
                  ·
                    refine ⟨462618684066348998556637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 616824912088465331408849 462618684066348998556637)
                    ·
                      refine ⟨173482006524880874458739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 462618684066348998556637 173482006524880874458739)
                      ·
                        rfl

theorem cell23_337855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_337855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337855 prefixEnd_337855 := by exact prefixLift 337855
  have htrace : WordTrace (prefixWord ++ tailWord_337855) baseStart_337855 baseEnd_337855 := by
    simpa [prefixWord, tailWord_337855, baseEnd_337855] using wordTrace_append hprefix tailTrace_337855
  have hstable : (prefixWord ++ tailWord_337855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337855).length < 2 ^ (prefixWord ++ tailWord_337855).sum := by decide
  have hdescent : baseEnd_337855 < baseStart_337855 := by decide
  rcases family_descends (prefixWord ++ tailWord_337855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337888 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 1, 9]
def baseStart_337888 : Nat := 118140960795 + 337888 * 2 ^ 59
def prefixEnd_337888 : Nat := 4983230072969 + 3 ^ 40 * 337888 * 2
def baseEnd_337888 : Nat := 57832983795493081782029

theorem tailTrace_337888 : CollatzResearch.WordTrace tailWord_337888 prefixEnd_337888 57832983795493081782029 := by
  unfold tailWord_337888
  simp only [CollatzResearch.WordTrace]
  refine ⟨6161893899948478760623159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8215858533264638347497545 6161893899948478760623159)
  ·
    refine ⟨9242840849922718140934739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6161893899948478760623159 9242840849922718140934739)
    ·
      refine ⟨13864261274884077211402109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9242840849922718140934739 13864261274884077211402109)
      ·
        refine ⟨5199097978081528954275791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13864261274884077211402109 5199097978081528954275791)
        ·
          refine ⟨7798646967122293431413687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5199097978081528954275791 7798646967122293431413687)
          ·
            refine ⟨11697970450683440147120531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7798646967122293431413687 11697970450683440147120531)
            ·
              refine ⟨17546955676025160220680797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11697970450683440147120531 17546955676025160220680797)
              ·
                refine ⟨6580108378509435082755299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17546955676025160220680797 6580108378509435082755299)
                ·
                  refine ⟨9870162567764152624132949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6580108378509435082755299 9870162567764152624132949)
                  ·
                    refine ⟨57832983795493081782029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 9870162567764152624132949 57832983795493081782029)
                    ·
                      rfl

theorem cell23_337888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_337888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337888 prefixEnd_337888 := by exact prefixLift 337888
  have htrace : WordTrace (prefixWord ++ tailWord_337888) baseStart_337888 baseEnd_337888 := by
    simpa [prefixWord, tailWord_337888, baseEnd_337888] using wordTrace_append hprefix tailTrace_337888
  have hstable : (prefixWord ++ tailWord_337888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337888).length < 2 ^ (prefixWord ++ tailWord_337888).sum := by decide
  have hdescent : baseEnd_337888 < baseStart_337888 := by decide
  rcases family_descends (prefixWord ++ tailWord_337888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337912 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 3, 3, 2]
def baseStart_337912 : Nat := 118140960795 + 337912 * 2 ^ 59
def prefixEnd_337912 : Nat := 4983230072969 + 3 ^ 40 * 337912 * 2
def baseEnd_337912 : Nat := 173511274922187151445977

theorem tailTrace_337912 : CollatzResearch.WordTrace tailWord_337912 prefixEnd_337912 173511274922187151445977 := by
  unfold tailWord_337912
  simp only [CollatzResearch.WordTrace]
  refine ⟨6162331575905004810059995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8216442101206673080079993 6162331575905004810059995)
  ·
    refine ⟨9243497363857507215089993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6162331575905004810059995 9243497363857507215089993)
    ·
      refine ⟨6932623022893130411317495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9243497363857507215089993 6932623022893130411317495)
      ·
        refine ⟨10398934534339695616976243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6932623022893130411317495 10398934534339695616976243)
        ·
          refine ⟨15598401801509543425464365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10398934534339695616976243 15598401801509543425464365)
          ·
            refine ⟨5849400675566078784549137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15598401801509543425464365 5849400675566078784549137)
            ·
              refine ⟨4387050506674559088411853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5849400675566078784549137 4387050506674559088411853)
              ·
                refine ⟨1645143940002959658154445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4387050506674559088411853 1645143940002959658154445)
                ·
                  refine ⟨616928977501109871807917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1645143940002959658154445 616928977501109871807917)
                  ·
                    refine ⟨231348366562916201927969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 616928977501109871807917 231348366562916201927969)
                    ·
                      refine ⟨173511274922187151445977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 231348366562916201927969 173511274922187151445977)
                      ·
                        rfl

theorem cell23_337912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 3, 3, 2].length) (baseStart_337912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337912 prefixEnd_337912 := by exact prefixLift 337912
  have htrace : WordTrace (prefixWord ++ tailWord_337912) baseStart_337912 baseEnd_337912 := by
    simpa [prefixWord, tailWord_337912, baseEnd_337912] using wordTrace_append hprefix tailTrace_337912
  have hstable : (prefixWord ++ tailWord_337912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337912).length < 2 ^ (prefixWord ++ tailWord_337912).sum := by decide
  have hdescent : baseEnd_337912 < baseStart_337912 := by decide
  rcases family_descends (prefixWord ++ tailWord_337912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337945 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 2, 4, 3]
def baseStart_337945 : Nat := 118140960795 + 337945 * 2 ^ 59
def prefixEnd_337945 : Nat := 4983230072969 + 3 ^ 40 * 337945 * 2
def baseEnd_337945 : Nat := 173528219783785522333325

theorem tailTrace_337945 : CollatzResearch.WordTrace tailWord_337945 prefixEnd_337945 173528219783785522333325 := by
  unfold tailWord_337945
  simp only [CollatzResearch.WordTrace]
  refine ⟨12325866760690456256071289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8217244507126970837380859 12325866760690456256071289)
  ·
    refine ⟨9244400070517842192053467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12325866760690456256071289 9244400070517842192053467)
    ·
      refine ⟨13866600105776763288080201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9244400070517842192053467 13866600105776763288080201)
      ·
        refine ⟨10399950079332572466060151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13866600105776763288080201 10399950079332572466060151)
        ·
          refine ⟨15599925118998858699090227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10399950079332572466060151 15599925118998858699090227)
          ·
            refine ⟨23399887678498288048635341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15599925118998858699090227 23399887678498288048635341)
            ·
              refine ⟨8774957879436858018238253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23399887678498288048635341 8774957879436858018238253)
              ·
                refine ⟨3290609204788821756839345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8774957879436858018238253 3290609204788821756839345)
                ·
                  refine ⟨2467956903591616317629509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3290609204788821756839345 2467956903591616317629509)
                  ·
                    refine ⟨462741919423428059555533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2467956903591616317629509 462741919423428059555533)
                    ·
                      refine ⟨173528219783785522333325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 462741919423428059555533 173528219783785522333325)
                      ·
                        rfl

theorem cell23_337945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_337945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337945 prefixEnd_337945 := by exact prefixLift 337945
  have htrace : WordTrace (prefixWord ++ tailWord_337945) baseStart_337945 baseEnd_337945 := by
    simpa [prefixWord, tailWord_337945, baseEnd_337945] using wordTrace_append hprefix tailTrace_337945
  have hstable : (prefixWord ++ tailWord_337945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337945).length < 2 ^ (prefixWord ++ tailWord_337945).sum := by decide
  have hdescent : baseEnd_337945 < baseStart_337945 := by decide
  rcases family_descends (prefixWord ++ tailWord_337945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337953 : List Nat := [1, 2, 3, 2, 4, 2, 2, 1, 2, 1, 3]
def baseStart_337953 : Nat := 118140960795 + 337953 * 2 ^ 59
def prefixEnd_337953 : Nat := 4983230072969 + 3 ^ 40 * 337953 * 2
def baseEnd_337953 : Nat := 173532327629021491033289

theorem tailTrace_337953 : CollatzResearch.WordTrace tailWord_337953 prefixEnd_337953 173532327629021491033289 := by
  unfold tailWord_337953
  simp only [CollatzResearch.WordTrace]
  refine ⟨12326158544661473622362513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8217439029774315748241675 12326158544661473622362513)
  ·
    refine ⟨9244618908496105216771885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12326158544661473622362513 9244618908496105216771885)
    ·
      refine ⟨3466732090686039456289457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9244618908496105216771885 3466732090686039456289457)
      ·
        refine ⟨2600049068014529592217093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3466732090686039456289457 2600049068014529592217093)
        ·
          refine ⟨487509200252724298540705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2600049068014529592217093 487509200252724298540705)
          ·
            refine ⟨365631900189543223905529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487509200252724298540705 365631900189543223905529)
            ·
              refine ⟨274223925142157417929147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365631900189543223905529 274223925142157417929147)
              ·
                refine ⟨411335887713236126893721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274223925142157417929147 411335887713236126893721)
                ·
                  refine ⟨308501915784927095170291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 411335887713236126893721 308501915784927095170291)
                  ·
                    refine ⟨462752873677390642755437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 308501915784927095170291 462752873677390642755437)
                    ·
                      refine ⟨173532327629021491033289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 462752873677390642755437 173532327629021491033289)
                      ·
                        rfl

theorem cell23_337953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_337953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337953 prefixEnd_337953 := by exact prefixLift 337953
  have htrace : WordTrace (prefixWord ++ tailWord_337953) baseStart_337953 baseEnd_337953 := by
    simpa [prefixWord, tailWord_337953, baseEnd_337953] using wordTrace_append hprefix tailTrace_337953
  have hstable : (prefixWord ++ tailWord_337953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337953).length < 2 ^ (prefixWord ++ tailWord_337953).sum := by decide
  have hdescent : baseEnd_337953 < baseStart_337953 := by decide
  rcases family_descends (prefixWord ++ tailWord_337953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337955 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 4]
def baseStart_337955 : Nat := 118140960795 + 337955 * 2 ^ 59
def prefixEnd_337955 : Nat := 4983230072969 + 3 ^ 40 * 337955 * 2
def baseEnd_337955 : Nat := 173533354590330483208279

theorem tailTrace_337955 : CollatzResearch.WordTrace tailWord_337955 prefixEnd_337955 173533354590330483208279 := by
  unfold tailWord_337955
  simp only [CollatzResearch.WordTrace]
  refine ⟨12326231490654227963935319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8217487660436151975956879 12326231490654227963935319)
  ·
    refine ⟨18489347235981341945902979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12326231490654227963935319 18489347235981341945902979)
    ·
      refine ⟨27734020853972012918854469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18489347235981341945902979 27734020853972012918854469)
      ·
        refine ⟨5200128910119752422285213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27734020853972012918854469 5200128910119752422285213)
        ·
          refine ⟨1950048341294907158356955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5200128910119752422285213 1950048341294907158356955)
          ·
            refine ⟨2925072511942360737535433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1950048341294907158356955 2925072511942360737535433)
            ·
              refine ⟨2193804383956770553151575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2925072511942360737535433 2193804383956770553151575)
              ·
                refine ⟨3290706575935155829727363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193804383956770553151575 3290706575935155829727363)
                ·
                  refine ⟨4936059863902733744591045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3290706575935155829727363 4936059863902733744591045)
                  ·
                    refine ⟨925511224481762577110821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4936059863902733744591045 925511224481762577110821)
                    ·
                      refine ⟨173533354590330483208279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 925511224481762577110821 173533354590330483208279)
                      ·
                        rfl

theorem cell23_337955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_337955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337955 prefixEnd_337955 := by exact prefixLift 337955
  have htrace : WordTrace (prefixWord ++ tailWord_337955) baseStart_337955 baseEnd_337955 := by
    simpa [prefixWord, tailWord_337955, baseEnd_337955] using wordTrace_append hprefix tailTrace_337955
  have hstable : (prefixWord ++ tailWord_337955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337955).length < 2 ^ (prefixWord ++ tailWord_337955).sum := by decide
  have hdescent : baseEnd_337955 < baseStart_337955 := by decide
  rcases family_descends (prefixWord ++ tailWord_337955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_337962 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_337962 : Nat := 118140960795 + 337962 * 2 ^ 59
def prefixEnd_337962 : Nat := 4983230072969 + 3 ^ 40 * 337962 * 2
def baseEnd_337962 : Nat := 173536948954911955820747

theorem tailTrace_337962 : CollatzResearch.WordTrace tailWord_337962 prefixEnd_337962 173536948954911955820747 := by
  unfold tailWord_337962
  simp only [CollatzResearch.WordTrace]
  refine ⟨3081621700407217039860035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8217657867752578772960093 3081621700407217039860035)
  ·
    refine ⟨4622432550610825559790053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3081621700407217039860035 4622432550610825559790053)
    ·
      refine ⟨866706103239529792460635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4622432550610825559790053 866706103239529792460635)
      ·
        refine ⟨1300059154859294688690953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866706103239529792460635 1300059154859294688690953)
        ·
          refine ⟨975044366144471016518215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1300059154859294688690953 975044366144471016518215)
          ·
            refine ⟨1462566549216706524777323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975044366144471016518215 1462566549216706524777323)
            ·
              refine ⟨2193849823825059787165985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462566549216706524777323 2193849823825059787165985)
              ·
                refine ⟨1645387367868794840374489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2193849823825059787165985 1645387367868794840374489)
                ·
                  refine ⟨1234040525901596130280867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1645387367868794840374489 1234040525901596130280867)
                  ·
                    refine ⟨1851060788852394195421301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1234040525901596130280867 1851060788852394195421301)
                    ·
                      refine ⟨173536948954911955820747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1851060788852394195421301 173536948954911955820747)
                      ·
                        rfl

theorem cell23_337962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_337962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_337962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_337962 prefixEnd_337962 := by exact prefixLift 337962
  have htrace : WordTrace (prefixWord ++ tailWord_337962) baseStart_337962 baseEnd_337962 := by
    simpa [prefixWord, tailWord_337962, baseEnd_337962] using wordTrace_append hprefix tailTrace_337962
  have hstable : (prefixWord ++ tailWord_337962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_337962).length < 2 ^ (prefixWord ++ tailWord_337962).sum := by decide
  have hdescent : baseEnd_337962 < baseStart_337962 := by decide
  rcases family_descends (prefixWord ++ tailWord_337962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338006 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_338006 : Nat := 118140960795 + 338006 * 2 ^ 59
def prefixEnd_338006 : Nat := 4983230072969 + 3 ^ 40 * 338006 * 2
def baseEnd_338006 : Nat := 173559542103709783670545

theorem tailTrace_338006 : CollatzResearch.WordTrace tailWord_338006 prefixEnd_338006 173559542103709783670545 := by
  unfold tailWord_338006
  simp only [CollatzResearch.WordTrace]
  refine ⟨770505725841841479627617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8218727742312975782694581 770505725841841479627617)
  ·
    refine ⟨577879294381381109720713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 770505725841841479627617 577879294381381109720713)
    ·
      refine ⟨433409470786035832290535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 577879294381381109720713 433409470786035832290535)
      ·
        refine ⟨650114206179053748435803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433409470786035832290535 650114206179053748435803)
        ·
          refine ⟨975171309268580622653705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650114206179053748435803 975171309268580622653705)
          ·
            refine ⟨731378481951435466990279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 975171309268580622653705 731378481951435466990279)
            ·
              refine ⟨1097067722927153200485419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731378481951435466990279 1097067722927153200485419)
              ·
                refine ⟨1645601584390729800728129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097067722927153200485419 1645601584390729800728129)
                ·
                  refine ⟨1234201188293047350546097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1645601584390729800728129 1234201188293047350546097)
                  ·
                    refine ⟨925650891219785512909573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1234201188293047350546097 925650891219785512909573)
                    ·
                      refine ⟨173559542103709783670545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 925650891219785512909573 173559542103709783670545)
                      ·
                        rfl

theorem cell23_338006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_338006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338006 prefixEnd_338006 := by exact prefixLift 338006
  have htrace : WordTrace (prefixWord ++ tailWord_338006) baseStart_338006 baseEnd_338006 := by
    simpa [prefixWord, tailWord_338006, baseEnd_338006] using wordTrace_append hprefix tailTrace_338006
  have hstable : (prefixWord ++ tailWord_338006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338006).length < 2 ^ (prefixWord ++ tailWord_338006).sum := by decide
  have hdescent : baseEnd_338006 < baseStart_338006 := by decide
  rcases family_descends (prefixWord ++ tailWord_338006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338032 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 4]
def baseStart_338032 : Nat := 118140960795 + 338032 * 2 ^ 59
def prefixEnd_338032 : Nat := 4983230072969 + 3 ^ 40 * 338032 * 2
def baseEnd_338032 : Nat := 173572892600726681945425

theorem tailTrace_338032 : CollatzResearch.WordTrace tailWord_338032 prefixEnd_338032 173572892600726681945425 := by
  unfold tailWord_338032
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164519955687635057244175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8219359940916846742992233 6164519955687635057244175)
  ·
    refine ⟨9246779933531452585866263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6164519955687635057244175 9246779933531452585866263)
    ·
      refine ⟨13870169900297178878799395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9246779933531452585866263 13870169900297178878799395)
      ·
        refine ⟨20805254850445768318199093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13870169900297178878799395 20805254850445768318199093)
        ·
          refine ⟨1950492642229290779831165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20805254850445768318199093 1950492642229290779831165)
          ·
            refine ⟨731434740835984042436687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1950492642229290779831165 731434740835984042436687)
            ·
              refine ⟨1097152111253976063655031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731434740835984042436687 1097152111253976063655031)
              ·
                refine ⟨1645728166880964095482547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097152111253976063655031 1645728166880964095482547)
                ·
                  refine ⟨2468592250321446143223821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1645728166880964095482547 2468592250321446143223821)
                  ·
                    refine ⟨925722093870542303708933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2468592250321446143223821 925722093870542303708933)
                    ·
                      refine ⟨173572892600726681945425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 925722093870542303708933 173572892600726681945425)
                      ·
                        rfl

theorem cell23_338032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_338032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338032 prefixEnd_338032 := by exact prefixLift 338032
  have htrace : WordTrace (prefixWord ++ tailWord_338032) baseStart_338032 baseEnd_338032 := by
    simpa [prefixWord, tailWord_338032, baseEnd_338032] using wordTrace_append hprefix tailTrace_338032
  have hstable : (prefixWord ++ tailWord_338032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338032).length < 2 ^ (prefixWord ++ tailWord_338032).sum := by decide
  have hdescent : baseEnd_338032 < baseStart_338032 := by decide
  rcases family_descends (prefixWord ++ tailWord_338032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338075 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 6]
def baseStart_338075 : Nat := 118140960795 + 338075 * 2 ^ 59
def prefixEnd_338075 : Nat := 4983230072969 + 3 ^ 40 * 338075 * 2
def baseEnd_338075 : Nat := 173594972268870013707727

theorem tailTrace_338075 : CollatzResearch.WordTrace tailWord_338075 prefixEnd_338075 173594972268870013707727 := by
  unfold tailWord_338075
  simp only [CollatzResearch.WordTrace]
  refine ⟨12330608250219488458303679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8220405500146325638869119 12330608250219488458303679)
  ·
    refine ⟨18495912375329232687455519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12330608250219488458303679 18495912375329232687455519)
    ·
      refine ⟨27743868562993849031183279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18495912375329232687455519 27743868562993849031183279)
      ·
        refine ⟨41615802844490773546774919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27743868562993849031183279 41615802844490773546774919)
        ·
          refine ⟨62423704266736160320162379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41615802844490773546774919 62423704266736160320162379)
          ·
            refine ⟨93635556400104240480243569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62423704266736160320162379 93635556400104240480243569)
            ·
              refine ⟨70226667300078180360182677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93635556400104240480243569 70226667300078180360182677)
              ·
                refine ⟨3291875029691164704383563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70226667300078180360182677 3291875029691164704383563)
                ·
                  refine ⟨4937812544536747056575345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291875029691164704383563 4937812544536747056575345)
                  ·
                    refine ⟨3703359408402560292431509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4937812544536747056575345 3703359408402560292431509)
                    ·
                      refine ⟨173594972268870013707727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3703359408402560292431509 173594972268870013707727)
                      ·
                        rfl

theorem cell23_338075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 6].length) (baseStart_338075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338075 prefixEnd_338075 := by exact prefixLift 338075
  have htrace : WordTrace (prefixWord ++ tailWord_338075) baseStart_338075 baseEnd_338075 := by
    simpa [prefixWord, tailWord_338075, baseEnd_338075] using wordTrace_append hprefix tailTrace_338075
  have hstable : (prefixWord ++ tailWord_338075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338075).length < 2 ^ (prefixWord ++ tailWord_338075).sum := by decide
  have hdescent : baseEnd_338075 < baseStart_338075 := by decide
  rcases family_descends (prefixWord ++ tailWord_338075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338093 : List Nat := [1, 5, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_338093 : Nat := 118140960795 + 338093 * 2 ^ 59
def prefixEnd_338093 : Nat := 4983230072969 + 3 ^ 40 * 338093 * 2
def baseEnd_338093 : Nat := 57868071640216981094215

theorem tailTrace_338093 : CollatzResearch.WordTrace tailWord_338093 prefixEnd_338093 57868071640216981094215 := by
  unfold tailWord_338093
  simp only [CollatzResearch.WordTrace]
  refine ⟨12331264764154277532458933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8220843176102851688305955 12331264764154277532458933)
  ·
    refine ⟨1156056071639463518668025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12331264764154277532458933 1156056071639463518668025)
    ·
      refine ⟨867042053729597639001019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1156056071639463518668025 867042053729597639001019)
      ·
        refine ⟨1300563080594396458501529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867042053729597639001019 1300563080594396458501529)
        ·
          refine ⟨975422310445797343876147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1300563080594396458501529 975422310445797343876147)
          ·
            refine ⟨1463133465668696015814221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975422310445797343876147 1463133465668696015814221)
            ·
              refine ⟨548675049625761005930333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1463133465668696015814221 548675049625761005930333)
              ·
                refine ⟨205753143609660377223875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 548675049625761005930333 205753143609660377223875)
                ·
                  refine ⟨308629715414490565835813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205753143609660377223875 308629715414490565835813)
                  ·
                    refine ⟨57868071640216981094215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 308629715414490565835813 57868071640216981094215)
                    ·
                      rfl

theorem cell23_338093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_338093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338093 prefixEnd_338093 := by exact prefixLift 338093
  have htrace : WordTrace (prefixWord ++ tailWord_338093) baseStart_338093 baseEnd_338093 := by
    simpa [prefixWord, tailWord_338093, baseEnd_338093] using wordTrace_append hprefix tailTrace_338093
  have hstable : (prefixWord ++ tailWord_338093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338093).length < 2 ^ (prefixWord ++ tailWord_338093).sum := by decide
  have hdescent : baseEnd_338093 < baseStart_338093 := by decide
  rcases family_descends (prefixWord ++ tailWord_338093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338100 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_338100 : Nat := 118140960795 + 338100 * 2 ^ 59
def prefixEnd_338100 : Nat := 4983230072969 + 3 ^ 40 * 338100 * 2
def baseEnd_338100 : Nat := 173607809285232415895113

theorem tailTrace_338100 : CollatzResearch.WordTrace tailWord_338100 prefixEnd_338100 173607809285232415895113 := by
  unfold tailWord_338100
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165760037564458863981877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8221013383419278485309169 6165760037564458863981877)
  ·
    refine ⟨578040003521668018498301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6165760037564458863981877 578040003521668018498301)
    ·
      refine ⟨216765001320625506936863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 578040003521668018498301 216765001320625506936863)
      ·
        refine ⟨325147501980938260405295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216765001320625506936863 325147501980938260405295)
        ·
          refine ⟨487721252971407390607943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325147501980938260405295 487721252971407390607943)
          ·
            refine ⟨731581879457111085911915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487721252971407390607943 731581879457111085911915)
            ·
              refine ⟨1097372819185666628867873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731581879457111085911915 1097372819185666628867873)
              ·
                refine ⟨823029614389249971650905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097372819185666628867873 823029614389249971650905)
                ·
                  refine ⟨617272210791937478738179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 823029614389249971650905 617272210791937478738179)
                  ·
                    refine ⟨925908316187906218107269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 617272210791937478738179 925908316187906218107269)
                    ·
                      refine ⟨173607809285232415895113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 925908316187906218107269 173607809285232415895113)
                      ·
                        rfl

theorem cell23_338100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_338100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338100 prefixEnd_338100 := by exact prefixLift 338100
  have htrace : WordTrace (prefixWord ++ tailWord_338100) baseStart_338100 baseEnd_338100 := by
    simpa [prefixWord, tailWord_338100, baseEnd_338100] using wordTrace_append hprefix tailTrace_338100
  have hstable : (prefixWord ++ tailWord_338100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338100).length < 2 ^ (prefixWord ++ tailWord_338100).sum := by decide
  have hdescent : baseEnd_338100 < baseStart_338100 := by decide
  rcases family_descends (prefixWord ++ tailWord_338100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338110 : List Nat := [4, 2, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_338110 : Nat := 118140960795 + 338110 * 2 ^ 59
def prefixEnd_338110 : Nat := 4983230072969 + 3 ^ 40 * 338110 * 2
def baseEnd_338110 : Nat := 57870981363925792256689

theorem tailTrace_338110 : CollatzResearch.WordTrace tailWord_338110 prefixEnd_338110 57870981363925792256689 := by
  unfold tailWord_338110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1541485600636586179478473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8221256536728459623885189 1541485600636586179478473)
  ·
    refine ⟨1156114200477439634608855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1541485600636586179478473 1156114200477439634608855)
    ·
      refine ⟨1734171300716159451913283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1156114200477439634608855 1734171300716159451913283)
      ·
        refine ⟨2601256951074239177869925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734171300716159451913283 2601256951074239177869925)
        ·
          refine ⟨487735678326419845850611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2601256951074239177869925 487735678326419845850611)
          ·
            refine ⟨731603517489629768775917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487735678326419845850611 731603517489629768775917)
            ·
              refine ⟨274351319058611163290969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 731603517489629768775917 274351319058611163290969)
              ·
                refine ⟨205763489293958372468227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274351319058611163290969 205763489293958372468227)
                ·
                  refine ⟨308645233940937558702341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205763489293958372468227 308645233940937558702341)
                  ·
                    refine ⟨57870981363925792256689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 308645233940937558702341 57870981363925792256689)
                    ·
                      rfl

theorem cell23_338110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_338110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338110 prefixEnd_338110 := by exact prefixLift 338110
  have htrace : WordTrace (prefixWord ++ tailWord_338110) baseStart_338110 baseEnd_338110 := by
    simpa [prefixWord, tailWord_338110, baseEnd_338110] using wordTrace_append hprefix tailTrace_338110
  have hstable : (prefixWord ++ tailWord_338110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338110).length < 2 ^ (prefixWord ++ tailWord_338110).sum := by decide
  have hdescent : baseEnd_338110 < baseStart_338110 := by decide
  rcases family_descends (prefixWord ++ tailWord_338110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338136 : List Nat := [2, 1, 2, 2, 4, 3, 1, 2, 1, 5]
def baseStart_338136 : Nat := 118140960795 + 338136 * 2 ^ 59
def prefixEnd_338136 : Nat := 4983230072969 + 3 ^ 40 * 338136 * 2
def baseEnd_338136 : Nat := 57875431529598091681649

theorem tailTrace_338136 : CollatzResearch.WordTrace tailWord_338136 prefixEnd_338136 57875431529598091681649 := by
  unfold tailWord_338136
  simp only [CollatzResearch.WordTrace]
  refine ⟨6166416551499247938137131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8221888735332330584182841 6166416551499247938137131)
  ·
    refine ⟨9249624827248871907205697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6166416551499247938137131 9249624827248871907205697)
    ·
      refine ⟨6937218620436653930404273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9249624827248871907205697 6937218620436653930404273)
      ·
        refine ⟨5202913965327490447803205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6937218620436653930404273 5202913965327490447803205)
        ·
          refine ⟨975546368498904458963101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5202913965327490447803205 975546368498904458963101)
          ·
            refine ⟨365829888187089172111163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 975546368498904458963101 365829888187089172111163)
            ·
              refine ⟨548744832280633758166745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365829888187089172111163 548744832280633758166745)
              ·
                refine ⟨411558624210475318625059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 548744832280633758166745 411558624210475318625059)
                ·
                  refine ⟨617337936315712977937589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411558624210475318625059 617337936315712977937589)
                  ·
                    refine ⟨57875431529598091681649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 617337936315712977937589 57875431529598091681649)
                    ·
                      rfl

theorem cell23_338136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_338136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338136 prefixEnd_338136 := by exact prefixLift 338136
  have htrace : WordTrace (prefixWord ++ tailWord_338136) baseStart_338136 baseEnd_338136 := by
    simpa [prefixWord, tailWord_338136, baseEnd_338136] using wordTrace_append hprefix tailTrace_338136
  have hstable : (prefixWord ++ tailWord_338136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338136).length < 2 ^ (prefixWord ++ tailWord_338136).sum := by decide
  have hdescent : baseEnd_338136 < baseStart_338136 := by decide
  rcases family_descends (prefixWord ++ tailWord_338136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338149 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 1, 6]
def baseStart_338149 : Nat := 118140960795 + 338149 * 2 ^ 59
def prefixEnd_338149 : Nat := 4983230072969 + 3 ^ 40 * 338149 * 2
def baseEnd_338149 : Nat := 57877656612434241394129

theorem tailTrace_338149 : CollatzResearch.WordTrace tailWord_338149 prefixEnd_338149 57877656612434241394129 := by
  unfold tailWord_338149
  simp only [CollatzResearch.WordTrace]
  refine ⟨12333307251951399096497501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8222204834634266064331667 12333307251951399096497501)
  ·
    refine ⟨4624990219481774661186563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12333307251951399096497501 4624990219481774661186563)
    ·
      refine ⟨6937485329222661991779845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4624990219481774661186563 6937485329222661991779845)
      ·
        refine ⟨1300778499229249123458721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6937485329222661991779845 1300778499229249123458721)
        ·
          refine ⟨975583874421936842594041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1300778499229249123458721 975583874421936842594041)
          ·
            refine ⟨731687905816452631945531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 975583874421936842594041 731687905816452631945531)
            ·
              refine ⟨1097531858724678947918297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 731687905816452631945531 1097531858724678947918297)
              ·
                refine ⟨823148894043509210938723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097531858724678947918297 823148894043509210938723)
                ·
                  refine ⟨1234723341065263816408085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 823148894043509210938723 1234723341065263816408085)
                  ·
                    refine ⟨57877656612434241394129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1234723341065263816408085 57877656612434241394129)
                    ·
                      rfl

theorem cell23_338149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_338149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338149 prefixEnd_338149 := by exact prefixLift 338149
  have htrace : WordTrace (prefixWord ++ tailWord_338149) baseStart_338149 baseEnd_338149 := by
    simpa [prefixWord, tailWord_338149, baseEnd_338149] using wordTrace_append hprefix tailTrace_338149
  have hstable : (prefixWord ++ tailWord_338149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338149).length < 2 ^ (prefixWord ++ tailWord_338149).sum := by decide
  have hdescent : baseEnd_338149 < baseStart_338149 := by decide
  rcases family_descends (prefixWord ++ tailWord_338149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338156 : List Nat := [2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 4]
def baseStart_338156 : Nat := 118140960795 + 338156 * 2 ^ 59
def prefixEnd_338156 : Nat := 4983230072969 + 3 ^ 40 * 338156 * 2
def baseEnd_338156 : Nat := 173636564201884196794855

theorem tailTrace_338156 : CollatzResearch.WordTrace tailWord_338156 prefixEnd_338156 173636564201884196794855 := by
  unfold tailWord_338156
  simp only [CollatzResearch.WordTrace]
  refine ⟨6166781281463019646001161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8222375041950692861334881 6166781281463019646001161)
  ·
    refine ⟨4625085961097264734500871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6166781281463019646001161 4625085961097264734500871)
    ·
      refine ⟨6937628941645897101751307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4625085961097264734500871 6937628941645897101751307)
      ·
        refine ⟨10406443412468845652626961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6937628941645897101751307 10406443412468845652626961)
        ·
          refine ⟨7804832559351634239470221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10406443412468845652626961 7804832559351634239470221)
          ·
            refine ⟨2926812209756862839801333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7804832559351634239470221 2926812209756862839801333)
            ·
              refine ⟨274388644664705891231375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2926812209756862839801333 274388644664705891231375)
              ·
                refine ⟨411582966997058836847063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274388644664705891231375 411582966997058836847063)
                ·
                  refine ⟨617374450495588255270595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411582966997058836847063 617374450495588255270595)
                  ·
                    refine ⟨926061675743382382905893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 617374450495588255270595 926061675743382382905893)
                    ·
                      refine ⟨173636564201884196794855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 926061675743382382905893 173636564201884196794855)
                      ·
                        rfl

theorem cell23_338156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 4].length) (baseStart_338156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338156 prefixEnd_338156 := by exact prefixLift 338156
  have htrace : WordTrace (prefixWord ++ tailWord_338156) baseStart_338156 baseEnd_338156 := by
    simpa [prefixWord, tailWord_338156, baseEnd_338156] using wordTrace_append hprefix tailTrace_338156
  have hstable : (prefixWord ++ tailWord_338156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338156).length < 2 ^ (prefixWord ++ tailWord_338156).sum := by decide
  have hdescent : baseEnd_338156 < baseStart_338156 := by decide
  rcases family_descends (prefixWord ++ tailWord_338156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338159 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 5]
def baseStart_338159 : Nat := 118140960795 + 338159 * 2 ^ 59
def prefixEnd_338159 : Nat := 4983230072969 + 3 ^ 40 * 338159 * 2
def baseEnd_338159 : Nat := 173638104643847685057341

theorem tailTrace_338159 : CollatzResearch.WordTrace tailWord_338159 prefixEnd_338159 173638104643847685057341 := by
  unfold tailWord_338159
  simp only [CollatzResearch.WordTrace]
  refine ⟨12333671981915170804361531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8222447987943447202907687 12333671981915170804361531)
  ·
    refine ⟨18500507972872756206542297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12333671981915170804361531 18500507972872756206542297)
    ·
      refine ⟨13875380979654567154906723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18500507972872756206542297 13875380979654567154906723)
      ·
        refine ⟨20813071469481850732360085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13875380979654567154906723 20813071469481850732360085)
        ·
          refine ⟨975612725131961753079379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20813071469481850732360085 975612725131961753079379)
          ·
            refine ⟨1463419087697942629619069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975612725131961753079379 1463419087697942629619069)
            ·
              refine ⟨548782157886728486107151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1463419087697942629619069 548782157886728486107151)
              ·
                refine ⟨823173236830092729160727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 548782157886728486107151 823173236830092729160727)
                ·
                  refine ⟨1234759855245139093741091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 823173236830092729160727 1234759855245139093741091)
                  ·
                    refine ⟨1852139782867708640611637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1234759855245139093741091 1852139782867708640611637)
                    ·
                      refine ⟨173638104643847685057341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1852139782867708640611637 173638104643847685057341)
                      ·
                        rfl

theorem cell23_338159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 5].length) (baseStart_338159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338159 prefixEnd_338159 := by exact prefixLift 338159
  have htrace : WordTrace (prefixWord ++ tailWord_338159) baseStart_338159 baseEnd_338159 := by
    simpa [prefixWord, tailWord_338159, baseEnd_338159] using wordTrace_append hprefix tailTrace_338159
  have hstable : (prefixWord ++ tailWord_338159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338159).length < 2 ^ (prefixWord ++ tailWord_338159).sum := by decide
  have hdescent : baseEnd_338159 < baseStart_338159 := by decide
  rcases family_descends (prefixWord ++ tailWord_338159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338162 : List Nat := [3, 2, 1, 3, 2, 12]
def baseStart_338162 : Nat := 118140960795 + 338162 * 2 ^ 59
def prefixEnd_338162 : Nat := 4983230072969 + 3 ^ 40 * 338162 * 2
def baseEnd_338162 : Nat := 714566440682350507489

theorem tailTrace_338162 : CollatzResearch.WordTrace tailWord_338162 prefixEnd_338162 714566440682350507489 := by
  unfold tailWord_338162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3083445350226075579180185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8222520933936201544480493 3083445350226075579180185)
  ·
    refine ⟨2312584012669556684385139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3083445350226075579180185 2312584012669556684385139)
    ·
      refine ⟨3468876019004335026577709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2312584012669556684385139 3468876019004335026577709)
      ·
        refine ⟨1300828507126625634966641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3468876019004335026577709 1300828507126625634966641)
        ·
          refine ⟨975621380344969226224981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1300828507126625634966641 975621380344969226224981)
          ·
            refine ⟨714566440682350507489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 975621380344969226224981 714566440682350507489)
            ·
              rfl

theorem cell23_338162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 12].length) (baseStart_338162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338162 prefixEnd_338162 := by exact prefixLift 338162
  have htrace : WordTrace (prefixWord ++ tailWord_338162) baseStart_338162 baseEnd_338162 := by
    simpa [prefixWord, tailWord_338162, baseEnd_338162] using wordTrace_append hprefix tailTrace_338162
  have hstable : (prefixWord ++ tailWord_338162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338162).length < 2 ^ (prefixWord ++ tailWord_338162).sum := by decide
  have hdescent : baseEnd_338162 < baseStart_338162 := by decide
  rcases family_descends (prefixWord ++ tailWord_338162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338166 : List Nat := [5, 1, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_338166 : Nat := 118140960795 + 338166 * 2 ^ 59
def prefixEnd_338166 : Nat := 4983230072969 + 3 ^ 40 * 338166 * 2
def baseEnd_338166 : Nat := 57880566336143052556603

theorem tailTrace_338166 : CollatzResearch.WordTrace tailWord_338166 prefixEnd_338166 57880566336143052556603 := by
  unfold tailWord_338166
  simp only [CollatzResearch.WordTrace]
  refine ⟨770870455805613187491647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8222618195259873999910901 770870455805613187491647)
  ·
    refine ⟨1156305683708419781237471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 770870455805613187491647 1156305683708419781237471)
    ·
      refine ⟨1734458525562629671856207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1156305683708419781237471 1734458525562629671856207)
      ·
        refine ⟨2601687788343944507784311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734458525562629671856207 2601687788343944507784311)
        ·
          refine ⟨3902531682515916761676467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601687788343944507784311 3902531682515916761676467)
          ·
            refine ⟨5853797523773875142514701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902531682515916761676467 5853797523773875142514701)
            ·
              refine ⟨2195174071415203178443013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5853797523773875142514701 2195174071415203178443013)
              ·
                refine ⟨411595138390350595958065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2195174071415203178443013 411595138390350595958065)
                ·
                  refine ⟨308696353792762946968549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 411595138390350595958065 308696353792762946968549)
                  ·
                    refine ⟨57880566336143052556603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 308696353792762946968549 57880566336143052556603)
                    ·
                      rfl

theorem cell23_338166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_338166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338166 prefixEnd_338166 := by exact prefixLift 338166
  have htrace : WordTrace (prefixWord ++ tailWord_338166) baseStart_338166 baseEnd_338166 := by
    simpa [prefixWord, tailWord_338166, baseEnd_338166] using wordTrace_append hprefix tailTrace_338166
  have hstable : (prefixWord ++ tailWord_338166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338166).length < 2 ^ (prefixWord ++ tailWord_338166).sum := by decide
  have hdescent : baseEnd_338166 < baseStart_338166 := by decide
  rcases family_descends (prefixWord ++ tailWord_338166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338210 : List Nat := [3, 3, 1, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_338210 : Nat := 118140960795 + 338210 * 2 ^ 59
def prefixEnd_338210 : Nat := 4983230072969 + 3 ^ 40 * 338210 * 2
def baseEnd_338210 : Nat := 173664292157226985519607

theorem tailTrace_338210 : CollatzResearch.WordTrace tailWord_338210 prefixEnd_338210 173664292157226985519607 := by
  unfold tailWord_338210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3083883026182601628617021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8223688069820271009645389 3083883026182601628617021)
  ·
    refine ⟨1156456134818475610731383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3083883026182601628617021 1156456134818475610731383)
    ·
      refine ⟨1734684202227713416097075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1156456134818475610731383 1734684202227713416097075)
      ·
        refine ⟨2602026303341570124145613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734684202227713416097075 2602026303341570124145613)
        ·
          refine ⟨975759863753088796554605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2602026303341570124145613 975759863753088796554605)
          ·
            refine ⟨365909948907408298707977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 975759863753088796554605 365909948907408298707977)
            ·
              refine ⟨274432461680556224030983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365909948907408298707977 274432461680556224030983)
              ·
                refine ⟨411648692520834336046475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274432461680556224030983 411648692520834336046475)
                ·
                  refine ⟨617473038781251504069713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411648692520834336046475 617473038781251504069713)
                  ·
                    refine ⟨463104779085938628052285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 617473038781251504069713 463104779085938628052285)
                    ·
                      refine ⟨173664292157226985519607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 463104779085938628052285 173664292157226985519607)
                      ·
                        rfl

theorem cell23_338210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_338210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338210 prefixEnd_338210 := by exact prefixLift 338210
  have htrace : WordTrace (prefixWord ++ tailWord_338210) baseStart_338210 baseEnd_338210 := by
    simpa [prefixWord, tailWord_338210, baseEnd_338210] using wordTrace_append hprefix tailTrace_338210
  have hstable : (prefixWord ++ tailWord_338210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338210).length < 2 ^ (prefixWord ++ tailWord_338210).sum := by decide
  have hdescent : baseEnd_338210 < baseStart_338210 := by decide
  rcases family_descends (prefixWord ++ tailWord_338210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338316 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 2, 5]
def baseStart_338316 : Nat := 118140960795 + 338316 * 2 ^ 59
def prefixEnd_338316 : Nat := 4983230072969 + 3 ^ 40 * 338316 * 2
def baseEnd_338316 : Nat := 57906240368867856931373

theorem tailTrace_338316 : CollatzResearch.WordTrace tailWord_338316 prefixEnd_338316 57906240368867856931373 := by
  unfold tailWord_338316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6169699121173193308913401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8226265494897591078551201 6169699121173193308913401)
  ·
    refine ⟨4627274340879894981685051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6169699121173193308913401 4627274340879894981685051)
    ·
      refine ⟨6940911511319842472527577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4627274340879894981685051 6940911511319842472527577)
      ·
        refine ⟨5205683633489881854395683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6940911511319842472527577 5205683633489881854395683)
        ·
          refine ⟨7808525450234822781593525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5205683633489881854395683 7808525450234822781593525)
          ·
            refine ⟨732049260959514635774393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7808525450234822781593525 732049260959514635774393)
            ·
              refine ⟨549036945719635976830795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 732049260959514635774393 549036945719635976830795)
              ·
                refine ⟨823555418579453965246193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549036945719635976830795 823555418579453965246193)
                ·
                  refine ⟨617666563934590473934645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 823555418579453965246193 617666563934590473934645)
                  ·
                    refine ⟨57906240368867856931373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 617666563934590473934645 57906240368867856931373)
                    ·
                      rfl

theorem cell23_338316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_338316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338316 prefixEnd_338316 := by exact prefixLift 338316
  have htrace : WordTrace (prefixWord ++ tailWord_338316) baseStart_338316 baseEnd_338316 := by
    simpa [prefixWord, tailWord_338316, baseEnd_338316] using wordTrace_append hprefix tailTrace_338316
  have hstable : (prefixWord ++ tailWord_338316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338316).length < 2 ^ (prefixWord ++ tailWord_338316).sum := by decide
  have hdescent : baseEnd_338316 < baseStart_338316 := by decide
  rcases family_descends (prefixWord ++ tailWord_338316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338336 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 4]
def baseStart_338336 : Nat := 118140960795 + 338336 * 2 ^ 59
def prefixEnd_338336 : Nat := 4983230072969 + 3 ^ 40 * 338336 * 2
def baseEnd_338336 : Nat := 173728990719693492544027

theorem tailTrace_338336 : CollatzResearch.WordTrace tailWord_338336 prefixEnd_338336 173728990719693492544027 := by
  unfold tailWord_338336
  simp only [CollatzResearch.WordTrace]
  refine ⟨6170063851136965016777431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8226751801515953355703241 6170063851136965016777431)
  ·
    refine ⟨9255095776705447525166147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6170063851136965016777431 9255095776705447525166147)
    ·
      refine ⟨13882643665058171287749221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9255095776705447525166147 13882643665058171287749221)
      ·
        refine ⟨2602995687198407116452979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13882643665058171287749221 2602995687198407116452979)
        ·
          refine ⟨3904493530797610674679469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602995687198407116452979 3904493530797610674679469)
          ·
            refine ⟨1464185074049104003004801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3904493530797610674679469 1464185074049104003004801)
            ·
              refine ⟨1098138805536828002253601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1464185074049104003004801 1098138805536828002253601)
              ·
                refine ⟨823604104152621001690201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1098138805536828002253601 823604104152621001690201)
                ·
                  refine ⟨617703078114465751267651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 823604104152621001690201 617703078114465751267651)
                  ·
                    refine ⟨926554617171698626901477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 617703078114465751267651 926554617171698626901477)
                    ·
                      refine ⟨173728990719693492544027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 926554617171698626901477 173728990719693492544027)
                      ·
                        rfl

theorem cell23_338336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_338336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338336 prefixEnd_338336 := by exact prefixLift 338336
  have htrace : WordTrace (prefixWord ++ tailWord_338336) baseStart_338336 baseEnd_338336 := by
    simpa [prefixWord, tailWord_338336, baseEnd_338336] using wordTrace_append hprefix tailTrace_338336
  have hstable : (prefixWord ++ tailWord_338336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338336).length < 2 ^ (prefixWord ++ tailWord_338336).sum := by decide
  have hdescent : baseEnd_338336 < baseStart_338336 := by decide
  rcases family_descends (prefixWord ++ tailWord_338336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338337 : List Nat := [1, 2, 3, 5, 1, 2, 2, 2, 5]
def baseStart_338337 : Nat := 118140960795 + 338337 * 2 ^ 59
def prefixEnd_338337 : Nat := 4983230072969 + 3 ^ 40 * 338337 * 2
def baseEnd_338337 : Nat := 19303278244483109847947

theorem tailTrace_338337 : CollatzResearch.WordTrace tailWord_338337 prefixEnd_338337 19303278244483109847947 := by
  unfold tailWord_338337
  simp only [CollatzResearch.WordTrace]
  refine ⟨12340164175270307204341265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8226776116846871469560843 12340164175270307204341265)
  ·
    refine ⟨9255123131452730403255949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12340164175270307204341265 9255123131452730403255949)
    ·
      refine ⟨3470671174294773901220981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9255123131452730403255949 3470671174294773901220981)
      ·
        refine ⟨325375422590135053239467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3470671174294773901220981 325375422590135053239467)
        ·
          refine ⟨488063133885202579859201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325375422590135053239467 488063133885202579859201)
          ·
            refine ⟨366047350413901934894401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488063133885202579859201 366047350413901934894401)
            ·
              refine ⟨274535512810426451170801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366047350413901934894401 274535512810426451170801)
              ·
                refine ⟨205901634607819838378101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274535512810426451170801 205901634607819838378101)
                ·
                  refine ⟨19303278244483109847947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205901634607819838378101 19303278244483109847947)
                  ·
                    rfl

theorem cell23_338337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 5].length) (baseStart_338337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338337 prefixEnd_338337 := by exact prefixLift 338337
  have htrace : WordTrace (prefixWord ++ tailWord_338337) baseStart_338337 baseEnd_338337 := by
    simpa [prefixWord, tailWord_338337, baseEnd_338337] using wordTrace_append hprefix tailTrace_338337
  have hstable : (prefixWord ++ tailWord_338337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338337).length < 2 ^ (prefixWord ++ tailWord_338337).sum := by decide
  have hdescent : baseEnd_338337 < baseStart_338337 := by decide
  rcases family_descends (prefixWord ++ tailWord_338337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338353 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 2, 4, 2]
def baseStart_338353 : Nat := 118140960795 + 338353 * 2 ^ 59
def prefixEnd_338353 : Nat := 4983230072969 + 3 ^ 40 * 338353 * 2
def baseEnd_338353 : Nat := 173737719890819926031449

theorem tailTrace_338353 : CollatzResearch.WordTrace tailWord_338353 prefixEnd_338353 173737719890819926031449 := by
  unfold tailWord_338353
  simp only [CollatzResearch.WordTrace]
  refine ⟨12340747743212341936923713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8227165162141561291282475 12340747743212341936923713)
  ·
    refine ⟨9255560807409256452692785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12340747743212341936923713 9255560807409256452692785)
    ·
      refine ⟨6941670605556942339519589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9255560807409256452692785 6941670605556942339519589)
      ·
        refine ⟨1301563238541926688659923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6941670605556942339519589 1301563238541926688659923)
        ·
          refine ⟨1952344857812890032989885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1301563238541926688659923 1952344857812890032989885)
          ·
            refine ⟨732129321679833762371207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1952344857812890032989885 732129321679833762371207)
            ·
              refine ⟨1098193982519750643556811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732129321679833762371207 1098193982519750643556811)
              ·
                refine ⟨1647290973779625965335217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098193982519750643556811 1647290973779625965335217)
                ·
                  refine ⟨1235468230334719474001413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1647290973779625965335217 1235468230334719474001413)
                  ·
                    refine ⟨231650293187759901375265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1235468230334719474001413 231650293187759901375265)
                    ·
                      refine ⟨173737719890819926031449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 231650293187759901375265 173737719890819926031449)
                      ·
                        rfl

theorem cell23_338353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_338353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338353 prefixEnd_338353 := by exact prefixLift 338353
  have htrace : WordTrace (prefixWord ++ tailWord_338353) baseStart_338353 baseEnd_338353 := by
    simpa [prefixWord, tailWord_338353, baseEnd_338353] using wordTrace_append hprefix tailTrace_338353
  have hstable : (prefixWord ++ tailWord_338353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338353).length < 2 ^ (prefixWord ++ tailWord_338353).sum := by decide
  have hdescent : baseEnd_338353 < baseStart_338353 := by decide
  rcases family_descends (prefixWord ++ tailWord_338353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338409 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 2, 5, 4]
def baseStart_338409 : Nat := 118140960795 + 338409 * 2 ^ 59
def prefixEnd_338409 : Nat := 4983230072969 + 3 ^ 40 * 338409 * 2
def baseEnd_338409 : Nat := 173766474807471706931191

theorem tailTrace_338409 : CollatzResearch.WordTrace tailWord_338409 prefixEnd_338409 173766474807471706931191 := by
  unfold tailWord_338409
  simp only [CollatzResearch.WordTrace]
  refine ⟨12342790231009463500962281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8228526820672975667308187 12342790231009463500962281)
  ·
    refine ⟨9257092673257097625721711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12342790231009463500962281 9257092673257097625721711)
    ·
      refine ⟨13885639009885646438582567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9257092673257097625721711 13885639009885646438582567)
      ·
        refine ⟨20828458514828469657873851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13885639009885646438582567 20828458514828469657873851)
        ·
          refine ⟨31242687772242704486810777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20828458514828469657873851 31242687772242704486810777)
          ·
            refine ⟨23432015829182028365108083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31242687772242704486810777 23432015829182028365108083)
            ·
              refine ⟨35148023743773042547662125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23432015829182028365108083 35148023743773042547662125)
              ·
                refine ⟨13180508903914890955373297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35148023743773042547662125 13180508903914890955373297)
                ·
                  refine ⟨9885381677936168216529973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13180508903914890955373297 9885381677936168216529973)
                  ·
                    refine ⟨926754532306515770299685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9885381677936168216529973 926754532306515770299685)
                    ·
                      refine ⟨173766474807471706931191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 926754532306515770299685 173766474807471706931191)
                      ·
                        rfl

theorem cell23_338409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_338409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338409 prefixEnd_338409 := by exact prefixLift 338409
  have htrace : WordTrace (prefixWord ++ tailWord_338409) baseStart_338409 baseEnd_338409 := by
    simpa [prefixWord, tailWord_338409, baseEnd_338409] using wordTrace_append hprefix tailTrace_338409
  have hstable : (prefixWord ++ tailWord_338409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338409).length < 2 ^ (prefixWord ++ tailWord_338409).sum := by decide
  have hdescent : baseEnd_338409 < baseStart_338409 := by decide
  rcases family_descends (prefixWord ++ tailWord_338409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338443 : List Nat := [1, 1, 1, 1, 7, 1, 2, 3, 1, 1, 4]
def baseStart_338443 : Nat := 118140960795 + 338443 * 2 ^ 59
def prefixEnd_338443 : Nat := 4983230072969 + 3 ^ 40 * 338443 * 2
def baseEnd_338443 : Nat := 173783933149724573906035

theorem tailTrace_338443 : CollatzResearch.WordTrace tailWord_338443 prefixEnd_338443 173783933149724573906035 := by
  unfold tailWord_338443
  simp only [CollatzResearch.WordTrace]
  refine ⟨12344030312886287307699983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8229353541924191538466655 12344030312886287307699983)
  ·
    refine ⟨18516045469329430961549975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12344030312886287307699983 18516045469329430961549975)
    ·
      refine ⟨27774068203994146442324963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18516045469329430961549975 27774068203994146442324963)
      ·
        refine ⟨41661102305991219663487445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27774068203994146442324963 41661102305991219663487445)
        ·
          refine ⟨976432085296669210862987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 41661102305991219663487445 976432085296669210862987)
          ·
            refine ⟨1464648127945003816294481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976432085296669210862987 1464648127945003816294481)
            ·
              refine ⟨1098486095958752862220861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1464648127945003816294481 1098486095958752862220861)
              ·
                refine ⟨411932285984532323332823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1098486095958752862220861 411932285984532323332823)
                ·
                  refine ⟨617898428976798484999235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411932285984532323332823 617898428976798484999235)
                  ·
                    refine ⟨926847643465197727498853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 617898428976798484999235 926847643465197727498853)
                    ·
                      refine ⟨173783933149724573906035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 926847643465197727498853 173783933149724573906035)
                      ·
                        rfl

theorem cell23_338443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 1, 4].length) (baseStart_338443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338443 prefixEnd_338443 := by exact prefixLift 338443
  have htrace : WordTrace (prefixWord ++ tailWord_338443) baseStart_338443 baseEnd_338443 := by
    simpa [prefixWord, tailWord_338443, baseEnd_338443] using wordTrace_append hprefix tailTrace_338443
  have hstable : (prefixWord ++ tailWord_338443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338443).length < 2 ^ (prefixWord ++ tailWord_338443).sum := by decide
  have hdescent : baseEnd_338443 < baseStart_338443 := by decide
  rcases family_descends (prefixWord ++ tailWord_338443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338453 : List Nat := [1, 3, 2, 1, 3, 1, 2, 4, 2, 4]
def baseStart_338453 : Nat := 118140960795 + 338453 * 2 ^ 59
def prefixEnd_338453 : Nat := 4983230072969 + 3 ^ 40 * 338453 * 2
def baseEnd_338453 : Nat := 57929689318756511593663

theorem tailTrace_338453 : CollatzResearch.WordTrace tailWord_338453 prefixEnd_338453 57929689318756511593663 := by
  unfold tailWord_338453
  simp only [CollatzResearch.WordTrace]
  refine ⟨12344395042850059015564013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8229596695233372677042675 12344395042850059015564013)
  ·
    refine ⟨4629148141068772130836505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12344395042850059015564013 4629148141068772130836505)
    ·
      refine ⟨3471861105801579098127379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4629148141068772130836505 3471861105801579098127379)
      ·
        refine ⟨5207791658702368647191069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3471861105801579098127379 5207791658702368647191069)
        ·
          refine ⟨1952921872013388242696651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5207791658702368647191069 1952921872013388242696651)
          ·
            refine ⟨2929382808020082364044977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1952921872013388242696651 2929382808020082364044977)
            ·
              refine ⟨2197037106015061773033733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2929382808020082364044977 2197037106015061773033733)
              ·
                refine ⟨411944457377824082443825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2197037106015061773033733 411944457377824082443825)
                ·
                  refine ⟨308958343033368061832869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 411944457377824082443825 308958343033368061832869)
                  ·
                    refine ⟨57929689318756511593663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 308958343033368061832869 57929689318756511593663)
                    ·
                      rfl

theorem cell23_338453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_338453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338453 prefixEnd_338453 := by exact prefixLift 338453
  have htrace : WordTrace (prefixWord ++ tailWord_338453) baseStart_338453 baseEnd_338453 := by
    simpa [prefixWord, tailWord_338453, baseEnd_338453] using wordTrace_append hprefix tailTrace_338453
  have hstable : (prefixWord ++ tailWord_338453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338453).length < 2 ^ (prefixWord ++ tailWord_338453).sum := by decide
  have hdescent : baseEnd_338453 < baseStart_338453 := by decide
  rcases family_descends (prefixWord ++ tailWord_338453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338456 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_338456 : Nat := 118140960795 + 338456 * 2 ^ 59
def prefixEnd_338456 : Nat := 4983230072969 + 3 ^ 40 * 338456 * 2
def baseEnd_338456 : Nat := 173790608398233023043475

theorem tailTrace_338456 : CollatzResearch.WordTrace tailWord_338456 prefixEnd_338456 173790608398233023043475 := by
  unfold tailWord_338456
  simp only [CollatzResearch.WordTrace]
  refine ⟨6172252230919595263961611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8229669641226127018615481 6172252230919595263961611)
  ·
    refine ⟨9258378346379392895942417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6172252230919595263961611 9258378346379392895942417)
    ·
      refine ⟨6943783759784544671956813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9258378346379392895942417 6943783759784544671956813)
      ·
        refine ⟨2603918909919204251983805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6943783759784544671956813 2603918909919204251983805)
        ·
          refine ⟨976469591219701594493927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2603918909919204251983805 976469591219701594493927)
          ·
            refine ⟨1464704386829552391740891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976469591219701594493927 1464704386829552391740891)
            ·
              refine ⟨2197056580244328587611337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464704386829552391740891 2197056580244328587611337)
              ·
                refine ⟨1647792435183246440708503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2197056580244328587611337 1647792435183246440708503)
                ·
                  refine ⟨2471688652774869661062755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647792435183246440708503 2471688652774869661062755)
                  ·
                    refine ⟨3707532979162304491594133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2471688652774869661062755 3707532979162304491594133)
                    ·
                      refine ⟨173790608398233023043475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3707532979162304491594133 173790608398233023043475)
                      ·
                        rfl

theorem cell23_338456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_338456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338456 prefixEnd_338456 := by exact prefixLift 338456
  have htrace : WordTrace (prefixWord ++ tailWord_338456) baseStart_338456 baseEnd_338456 := by
    simpa [prefixWord, tailWord_338456, baseEnd_338456] using wordTrace_append hprefix tailTrace_338456
  have hstable : (prefixWord ++ tailWord_338456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338456).length < 2 ^ (prefixWord ++ tailWord_338456).sum := by decide
  have hdescent : baseEnd_338456 < baseStart_338456 := by decide
  rcases family_descends (prefixWord ++ tailWord_338456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338476 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 3]
def baseStart_338476 : Nat := 118140960795 + 338476 * 2 ^ 59
def prefixEnd_338476 : Nat := 4983230072969 + 3 ^ 40 * 338476 * 2
def baseEnd_338476 : Nat := 173800878011322944793383

theorem tailTrace_338476 : CollatzResearch.WordTrace tailWord_338476 prefixEnd_338476 173800878011322944793383 := by
  unfold tailWord_338476
  simp only [CollatzResearch.WordTrace]
  refine ⟨6172616960883366971825641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8230155947844489295767521 6172616960883366971825641)
  ·
    refine ⟨4629462720662525228869231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6172616960883366971825641 4629462720662525228869231)
    ·
      refine ⟨6944194080993787843303847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4629462720662525228869231 6944194080993787843303847)
      ·
        refine ⟨10416291121490681764955771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6944194080993787843303847 10416291121490681764955771)
        ·
          refine ⟨15624436682236022647433657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10416291121490681764955771 15624436682236022647433657)
          ·
            refine ⟨11718327511677016985575243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15624436682236022647433657 11718327511677016985575243)
            ·
              refine ⟨17577491267515525478362865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11718327511677016985575243 17577491267515525478362865)
              ·
                refine ⟨13183118450636644108772149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17577491267515525478362865 13183118450636644108772149)
                ·
                  refine ⟨1235917354747185385197389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13183118450636644108772149 1235917354747185385197389)
                  ·
                    refine ⟨463469008030194519449021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1235917354747185385197389 463469008030194519449021)
                    ·
                      refine ⟨173800878011322944793383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 463469008030194519449021 173800878011322944793383)
                      ·
                        rfl

theorem cell23_338476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_338476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338476 prefixEnd_338476 := by exact prefixLift 338476
  have htrace : WordTrace (prefixWord ++ tailWord_338476) baseStart_338476 baseEnd_338476 := by
    simpa [prefixWord, tailWord_338476, baseEnd_338476] using wordTrace_append hprefix tailTrace_338476
  have hstable : (prefixWord ++ tailWord_338476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338476).length < 2 ^ (prefixWord ++ tailWord_338476).sum := by decide
  have hdescent : baseEnd_338476 < baseStart_338476 := by decide
  rcases family_descends (prefixWord ++ tailWord_338476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338493 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_338493 : Nat := 118140960795 + 338493 * 2 ^ 59
def prefixEnd_338493 : Nat := 4983230072969 + 3 ^ 40 * 338493 * 2
def baseEnd_338493 : Nat := 173809607182449378280805

theorem tailTrace_338493 : CollatzResearch.WordTrace tailWord_338493 prefixEnd_338493 173809607182449378280805 := by
  unfold tailWord_338493
  simp only [CollatzResearch.WordTrace]
  refine ⟨12345853962705145847020133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8230569308470097231346755 12345853962705145847020133)
  ·
    refine ⟨2314847618007214846316275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12345853962705145847020133 2314847618007214846316275)
    ·
      refine ⟨3472271427010822269474413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2314847618007214846316275 3472271427010822269474413)
      ·
        refine ⟨1302101785129058351052905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3472271427010822269474413 1302101785129058351052905)
        ·
          refine ⟨976576338846793763289679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1302101785129058351052905 976576338846793763289679)
          ·
            refine ⟨1464864508270190644934519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976576338846793763289679 1464864508270190644934519)
            ·
              refine ⟨2197296762405285967401779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464864508270190644934519 2197296762405285967401779)
              ·
                refine ⟨3295945143607928951102669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197296762405285967401779 3295945143607928951102669)
                ·
                  refine ⟨1235979428852973356663501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3295945143607928951102669 1235979428852973356663501)
                  ·
                    refine ⟨463492285819865008748813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1235979428852973356663501 463492285819865008748813)
                    ·
                      refine ⟨173809607182449378280805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 463492285819865008748813 173809607182449378280805)
                      ·
                        rfl

theorem cell23_338493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_338493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338493 prefixEnd_338493 := by exact prefixLift 338493
  have htrace : WordTrace (prefixWord ++ tailWord_338493) baseStart_338493 baseEnd_338493 := by
    simpa [prefixWord, tailWord_338493, baseEnd_338493] using wordTrace_append hprefix tailTrace_338493
  have hstable : (prefixWord ++ tailWord_338493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338493).length < 2 ^ (prefixWord ++ tailWord_338493).sum := by decide
  have hdescent : baseEnd_338493 < baseStart_338493 := by decide
  rcases family_descends (prefixWord ++ tailWord_338493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338494 : List Nat := [4, 2, 1, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_338494 : Nat := 118140960795 + 338494 * 2 ^ 59
def prefixEnd_338494 : Nat := 4983230072969 + 3 ^ 40 * 338494 * 2
def baseEnd_338494 : Nat := 173810120663103874368301

theorem tailTrace_338494 : CollatzResearch.WordTrace tailWord_338494 prefixEnd_338494 173810120663103874368301 := by
  unfold tailWord_338494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543236304462690377225817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8230593623801015345204357 1543236304462690377225817)
  ·
    refine ⟨1157427228347017782919363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1543236304462690377225817 1157427228347017782919363)
    ·
      refine ⟨1736140842520526674379045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1157427228347017782919363 1736140842520526674379045)
      ·
        refine ⟨325526407972598751446071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1736140842520526674379045 325526407972598751446071)
        ·
          refine ⟨488289611958898127169107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325526407972598751446071 488289611958898127169107)
          ·
            refine ⟨732434417938347190753661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488289611958898127169107 732434417938347190753661)
            ·
              refine ⟨274662906726880196532623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 732434417938347190753661 274662906726880196532623)
              ·
                refine ⟨411994360090320294798935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274662906726880196532623 411994360090320294798935)
                ·
                  refine ⟨617991540135480442198403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411994360090320294798935 617991540135480442198403)
                  ·
                    refine ⟨926987310203220663297605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 617991540135480442198403 926987310203220663297605)
                    ·
                      refine ⟨173810120663103874368301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 926987310203220663297605 173810120663103874368301)
                      ·
                        rfl

theorem cell23_338494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_338494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338494 prefixEnd_338494 := by exact prefixLift 338494
  have htrace : WordTrace (prefixWord ++ tailWord_338494) baseStart_338494 baseEnd_338494 := by
    simpa [prefixWord, tailWord_338494, baseEnd_338494] using wordTrace_append hprefix tailTrace_338494
  have hstable : (prefixWord ++ tailWord_338494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338494).length < 2 ^ (prefixWord ++ tailWord_338494).sum := by decide
  have hdescent : baseEnd_338494 < baseStart_338494 := by decide
  rcases family_descends (prefixWord ++ tailWord_338494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338497 : List Nat := [1, 2, 5, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_338497 : Nat := 118140960795 + 338497 * 2 ^ 59
def prefixEnd_338497 : Nat := 4983230072969 + 3 ^ 40 * 338497 * 2
def baseEnd_338497 : Nat := 173811661105067362630787

theorem tailTrace_338497 : CollatzResearch.WordTrace tailWord_338497 prefixEnd_338497 173811661105067362630787 := by
  unfold tailWord_338497
  simp only [CollatzResearch.WordTrace]
  refine ⟨12345999854690654530165745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8230666569793769686777163 12345999854690654530165745)
  ·
    refine ⟨9259499891017990897624309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12345999854690654530165745 9259499891017990897624309)
    ·
      refine ⟨868078114782936646652279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9259499891017990897624309 868078114782936646652279)
      ·
        refine ⟨1302117172174404969978419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868078114782936646652279 1302117172174404969978419)
        ·
          refine ⟨1953175758261607454967629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1302117172174404969978419 1953175758261607454967629)
          ·
            refine ⟨732440909348102795612861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1953175758261607454967629 732440909348102795612861)
            ·
              refine ⟨274665341005538548354823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 732440909348102795612861 274665341005538548354823)
              ·
                refine ⟨411998011508307822532235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274665341005538548354823 411998011508307822532235)
                ·
                  refine ⟨617997017262461733798353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 411998011508307822532235 617997017262461733798353)
                  ·
                    refine ⟨463497762946846300348765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 617997017262461733798353 463497762946846300348765)
                    ·
                      refine ⟨173811661105067362630787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 463497762946846300348765 173811661105067362630787)
                      ·
                        rfl

theorem cell23_338497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_338497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338497 prefixEnd_338497 := by exact prefixLift 338497
  have htrace : WordTrace (prefixWord ++ tailWord_338497) baseStart_338497 baseEnd_338497 := by
    simpa [prefixWord, tailWord_338497, baseEnd_338497] using wordTrace_append hprefix tailTrace_338497
  have hstable : (prefixWord ++ tailWord_338497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338497).length < 2 ^ (prefixWord ++ tailWord_338497).sum := by decide
  have hdescent : baseEnd_338497 < baseStart_338497 := by decide
  rcases family_descends (prefixWord ++ tailWord_338497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338500 : List Nat := [2, 3, 5, 1, 1, 11]
def baseStart_338500 : Nat := 118140960795 + 338500 * 2 ^ 59
def prefixEnd_338500 : Nat := 4983230072969 + 3 ^ 40 * 338500 * 2
def baseEnd_338500 : Nat := 715280664802596094211

theorem tailTrace_338500 : CollatzResearch.WordTrace tailWord_338500 prefixEnd_338500 715280664802596094211 := by
  unfold tailWord_338500
  simp only [CollatzResearch.WordTrace]
  refine ⟨6173054636839893021262477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8230739515786524028349969 6173054636839893021262477)
  ·
    refine ⟨2314895488814959882973429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6173054636839893021262477 2314895488814959882973429)
    ·
      refine ⟨217021452076402489028759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2314895488814959882973429 217021452076402489028759)
      ·
        refine ⟨325532178114603733543139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217021452076402489028759 325532178114603733543139)
        ·
          refine ⟨488298267171905600314709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325532178114603733543139 488298267171905600314709)
          ·
            refine ⟨715280664802596094211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 488298267171905600314709 715280664802596094211)
            ·
              rfl

theorem cell23_338500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 11].length) (baseStart_338500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338500 prefixEnd_338500 := by exact prefixLift 338500
  have htrace : WordTrace (prefixWord ++ tailWord_338500) baseStart_338500 baseEnd_338500 := by
    simpa [prefixWord, tailWord_338500, baseEnd_338500] using wordTrace_append hprefix tailTrace_338500
  have hstable : (prefixWord ++ tailWord_338500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338500).length < 2 ^ (prefixWord ++ tailWord_338500).sum := by decide
  have hdescent : baseEnd_338500 < baseStart_338500 := by decide
  rcases family_descends (prefixWord ++ tailWord_338500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338510 : List Nat := [4, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3]
def baseStart_338510 : Nat := 118140960795 + 338510 * 2 ^ 59
def prefixEnd_338510 : Nat := 4983230072969 + 3 ^ 40 * 338510 * 2
def baseEnd_338510 : Nat := 173818336353575811768227

theorem tailTrace_338510 : CollatzResearch.WordTrace tailWord_338510 prefixEnd_338510 173818336353575811768227 := by
  unfold tailWord_338510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543309250455444718798623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8230982669095705166925989 1543309250455444718798623)
  ·
    refine ⟨2314963875683167078197935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1543309250455444718798623 2314963875683167078197935)
    ·
      refine ⟨3472445813524750617296903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2314963875683167078197935 3472445813524750617296903)
      ·
        refine ⟨5208668720287125925945355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472445813524750617296903 5208668720287125925945355)
        ·
          refine ⟨7813003080430688888918033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5208668720287125925945355 7813003080430688888918033)
          ·
            refine ⟨5859752310323016666688525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7813003080430688888918033 5859752310323016666688525)
            ·
              refine ⟨2197407116371131250008197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5859752310323016666688525 2197407116371131250008197)
              ·
                refine ⟨412013834319587109376537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2197407116371131250008197 412013834319587109376537)
                ·
                  refine ⟨309010375739690332032403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412013834319587109376537 309010375739690332032403)
                  ·
                    refine ⟨463515563609535498048605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 309010375739690332032403 463515563609535498048605)
                    ·
                      refine ⟨173818336353575811768227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 463515563609535498048605 173818336353575811768227)
                      ·
                        rfl

theorem cell23_338510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_338510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338510 prefixEnd_338510 := by exact prefixLift 338510
  have htrace : WordTrace (prefixWord ++ tailWord_338510) baseStart_338510 baseEnd_338510 := by
    simpa [prefixWord, tailWord_338510, baseEnd_338510] using wordTrace_append hprefix tailTrace_338510
  have hstable : (prefixWord ++ tailWord_338510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338510).length < 2 ^ (prefixWord ++ tailWord_338510).sum := by decide
  have hdescent : baseEnd_338510 < baseStart_338510 := by decide
  rcases family_descends (prefixWord ++ tailWord_338510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338580 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_338580 : Nat := 118140960795 + 338580 * 2 ^ 59
def prefixEnd_338580 : Nat := 4983230072969 + 3 ^ 40 * 338580 * 2
def baseEnd_338580 : Nat := 173854279999390537892905

theorem tailTrace_338580 : CollatzResearch.WordTrace tailWord_338580 prefixEnd_338580 173854279999390537892905 := by
  unfold tailWord_338580
  simp only [CollatzResearch.WordTrace]
  refine ⟨6174513556694979852718597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8232684742259973136958129 6174513556694979852718597)
  ·
    refine ⟨1157721291880308722384737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6174513556694979852718597 1157721291880308722384737)
    ·
      refine ⟨868290968910231541788553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1157721291880308722384737 868290968910231541788553)
      ·
        refine ⟨651218226682673656341415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 868290968910231541788553 651218226682673656341415)
        ·
          refine ⟨976827340024010484512123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651218226682673656341415 976827340024010484512123)
          ·
            refine ⟨1465241010036015726768185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976827340024010484512123 1465241010036015726768185)
            ·
              refine ⟨1098930757527011795076139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1465241010036015726768185 1098930757527011795076139)
              ·
                refine ⟨1648396136290517692614209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098930757527011795076139 1648396136290517692614209)
                ·
                  refine ⟨1236297102217888269460657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1648396136290517692614209 1236297102217888269460657)
                  ·
                    refine ⟨927222826663416202095493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1236297102217888269460657 927222826663416202095493)
                    ·
                      refine ⟨173854279999390537892905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 927222826663416202095493 173854279999390537892905)
                      ·
                        rfl

theorem cell23_338580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_338580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338580 prefixEnd_338580 := by exact prefixLift 338580
  have htrace : WordTrace (prefixWord ++ tailWord_338580) baseStart_338580 baseEnd_338580 := by
    simpa [prefixWord, tailWord_338580, baseEnd_338580] using wordTrace_append hprefix tailTrace_338580
  have hstable : (prefixWord ++ tailWord_338580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338580).length < 2 ^ (prefixWord ++ tailWord_338580).sum := by decide
  have hdescent : baseEnd_338580 < baseStart_338580 := by decide
  rcases family_descends (prefixWord ++ tailWord_338580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338583 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 3]
def baseStart_338583 : Nat := 118140960795 + 338583 * 2 ^ 59
def prefixEnd_338583 : Nat := 4983230072969 + 3 ^ 40 * 338583 * 2
def baseEnd_338583 : Nat := 173855820441354026155391

theorem tailTrace_338583 : CollatzResearch.WordTrace tailWord_338583 prefixEnd_338583 173855820441354026155391 := by
  unfold tailWord_338583
  simp only [CollatzResearch.WordTrace]
  refine ⟨12349136532379091217796403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8232757688252727478530935 12349136532379091217796403)
  ·
    refine ⟨18523704798568636826694605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12349136532379091217796403 18523704798568636826694605)
    ·
      refine ⟨6946389299463238810010477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18523704798568636826694605 6946389299463238810010477)
      ·
        refine ⟨2604895987298714553753929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6946389299463238810010477 2604895987298714553753929)
        ·
          refine ⟨1953671990474035915315447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2604895987298714553753929 1953671990474035915315447)
          ·
            refine ⟨2930507985711053872973171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1953671990474035915315447 2930507985711053872973171)
            ·
              refine ⟨4395761978566580809459757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2930507985711053872973171 4395761978566580809459757)
              ·
                refine ⟨1648410741962467803547409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4395761978566580809459757 1648410741962467803547409)
                ·
                  refine ⟨1236308056471850852660557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1648410741962467803547409 1236308056471850852660557)
                  ·
                    refine ⟨463615521176944069747709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1236308056471850852660557 463615521176944069747709)
                    ·
                      refine ⟨173855820441354026155391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 463615521176944069747709 173855820441354026155391)
                      ·
                        rfl

theorem cell23_338583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_338583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338583 prefixEnd_338583 := by exact prefixLift 338583
  have htrace : WordTrace (prefixWord ++ tailWord_338583) baseStart_338583 baseEnd_338583 := by
    simpa [prefixWord, tailWord_338583, baseEnd_338583] using wordTrace_append hprefix tailTrace_338583
  have hstable : (prefixWord ++ tailWord_338583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338583).length < 2 ^ (prefixWord ++ tailWord_338583).sum := by decide
  have hdescent : baseEnd_338583 < baseStart_338583 := by decide
  rcases family_descends (prefixWord ++ tailWord_338583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338584 : List Nat := [2, 1, 2, 4, 1, 1, 5, 1, 2, 2, 2]
def baseStart_338584 : Nat := 118140960795 + 338584 * 2 ^ 59
def prefixEnd_338584 : Nat := 4983230072969 + 3 ^ 40 * 338584 * 2
def baseEnd_338584 : Nat := 173856333922008522242887

theorem tailTrace_338584 : CollatzResearch.WordTrace tailWord_338584 prefixEnd_338584 173856333922008522242887 := by
  unfold tailWord_338584
  simp only [CollatzResearch.WordTrace]
  refine ⟨6174586502687734194291403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8232782003583645592388537 6174586502687734194291403)
  ·
    refine ⟨9261879754031601291437105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6174586502687734194291403 9261879754031601291437105)
    ·
      refine ⟨6946409815523700968577829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9261879754031601291437105 6946409815523700968577829)
      ·
        refine ⟨1302451840410693931608343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6946409815523700968577829 1302451840410693931608343)
        ·
          refine ⟨1953677760616040897412515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1302451840410693931608343 1953677760616040897412515)
          ·
            refine ⟨2930516640924061346118773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1953677760616040897412515 2930516640924061346118773)
            ·
              refine ⟨274735935086630751198635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2930516640924061346118773 274735935086630751198635)
              ·
                refine ⟨412103902629946126797953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274735935086630751198635 412103902629946126797953)
                ·
                  refine ⟨309077926972459595098465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412103902629946126797953 309077926972459595098465)
                  ·
                    refine ⟨231808445229344696323849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 309077926972459595098465 231808445229344696323849)
                    ·
                      refine ⟨173856333922008522242887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 231808445229344696323849 173856333922008522242887)
                      ·
                        rfl

theorem cell23_338584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_338584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338584 prefixEnd_338584 := by exact prefixLift 338584
  have htrace : WordTrace (prefixWord ++ tailWord_338584) baseStart_338584 baseEnd_338584 := by
    simpa [prefixWord, tailWord_338584, baseEnd_338584] using wordTrace_append hprefix tailTrace_338584
  have hstable : (prefixWord ++ tailWord_338584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338584).length < 2 ^ (prefixWord ++ tailWord_338584).sum := by decide
  have hdescent : baseEnd_338584 < baseStart_338584 := by decide
  rcases family_descends (prefixWord ++ tailWord_338584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338623 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 4]
def baseStart_338623 : Nat := 118140960795 + 338623 * 2 ^ 59
def prefixEnd_338623 : Nat := 4983230072969 + 3 ^ 40 * 338623 * 2
def baseEnd_338623 : Nat := 173876359667533869655207

theorem tailTrace_338623 : CollatzResearch.WordTrace tailWord_338623 prefixEnd_338623 173876359667533869655207 := by
  unfold tailWord_338623
  simp only [CollatzResearch.WordTrace]
  refine ⟨12350595452234178049252523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8233730301489452032835015 12350595452234178049252523)
  ·
    refine ⟨18525893178351267073878785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12350595452234178049252523 18525893178351267073878785)
    ·
      refine ⟨13894419883763450305409089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18525893178351267073878785 13894419883763450305409089)
      ·
        refine ⟨10420814912822587729056817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13894419883763450305409089 10420814912822587729056817)
        ·
          refine ⟨7815611184616940796792613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10420814912822587729056817 7815611184616940796792613)
          ·
            refine ⟨1465427097115676399398615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7815611184616940796792613 1465427097115676399398615)
            ·
              refine ⟨2198140645673514599097923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465427097115676399398615 2198140645673514599097923)
              ·
                refine ⟨3297210968510271898646885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198140645673514599097923 3297210968510271898646885)
                ·
                  refine ⟨618227056595675980996291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3297210968510271898646885 618227056595675980996291)
                  ·
                    refine ⟨927340584893513971494437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 618227056595675980996291 927340584893513971494437)
                    ·
                      refine ⟨173876359667533869655207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 927340584893513971494437 173876359667533869655207)
                      ·
                        rfl

theorem cell23_338623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_338623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338623 prefixEnd_338623 := by exact prefixLift 338623
  have htrace : WordTrace (prefixWord ++ tailWord_338623) baseStart_338623 baseEnd_338623 := by
    simpa [prefixWord, tailWord_338623, baseEnd_338623] using wordTrace_append hprefix tailTrace_338623
  have hstable : (prefixWord ++ tailWord_338623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338623).length < 2 ^ (prefixWord ++ tailWord_338623).sum := by decide
  have hdescent : baseEnd_338623 < baseStart_338623 := by decide
  rcases family_descends (prefixWord ++ tailWord_338623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338660 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_338660 : Nat := 118140960795 + 338660 * 2 ^ 59
def prefixEnd_338660 : Nat := 4983230072969 + 3 ^ 40 * 338660 * 2
def baseEnd_338660 : Nat := 173895358451750224892537

theorem tailTrace_338660 : CollatzResearch.WordTrace tailWord_338660 prefixEnd_338660 173895358451750224892537 := by
  unfold tailWord_338660
  simp only [CollatzResearch.WordTrace]
  refine ⟨6175972476550066684174717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8234629968733422245566289 6175972476550066684174717)
  ·
    refine ⟨2315989678706275006565519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6175972476550066684174717 2315989678706275006565519)
    ·
      refine ⟨3473984518059412509848279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2315989678706275006565519 3473984518059412509848279)
      ·
        refine ⟨5210976777089118764772419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3473984518059412509848279 5210976777089118764772419)
        ·
          refine ⟨7816465165633678147158629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5210976777089118764772419 7816465165633678147158629)
          ·
            refine ⟨1465587218556314652592243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7816465165633678147158629 1465587218556314652592243)
            ·
              refine ⟨2198380827834471978888365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465587218556314652592243 2198380827834471978888365)
              ·
                refine ⟨824392810437926992083137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2198380827834471978888365 824392810437926992083137)
                ·
                  refine ⟨618294607828445244062353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 824392810437926992083137 618294607828445244062353)
                  ·
                    refine ⟨463720955871333933046765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 618294607828445244062353 463720955871333933046765)
                    ·
                      refine ⟨173895358451750224892537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 463720955871333933046765 173895358451750224892537)
                      ·
                        rfl

theorem cell23_338660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_338660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338660 prefixEnd_338660 := by exact prefixLift 338660
  have htrace : WordTrace (prefixWord ++ tailWord_338660) baseStart_338660 baseEnd_338660 := by
    simpa [prefixWord, tailWord_338660, baseEnd_338660] using wordTrace_append hprefix tailTrace_338660
  have hstable : (prefixWord ++ tailWord_338660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338660).length < 2 ^ (prefixWord ++ tailWord_338660).sum := by decide
  have hdescent : baseEnd_338660 < baseStart_338660 := by decide
  rcases family_descends (prefixWord ++ tailWord_338660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338684 : List Nat := [2, 2, 2, 1, 3, 2, 4, 2, 1, 4]
def baseStart_338684 : Nat := 118140960795 + 338684 * 2 ^ 59
def prefixEnd_338684 : Nat := 4983230072969 + 3 ^ 40 * 338684 * 2
def baseEnd_338684 : Nat := 57969227329152710330809

theorem tailTrace_338684 : CollatzResearch.WordTrace tailWord_338684 prefixEnd_338684 57969227329152710330809 := by
  unfold tailWord_338684
  simp only [CollatzResearch.WordTrace]
  refine ⟨6176410152506592733611553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8235213536675456978148737 6176410152506592733611553)
  ·
    refine ⟨4632307614379944550208665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6176410152506592733611553 4632307614379944550208665)
    ·
      refine ⟨3474230710784958412656499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4632307614379944550208665 3474230710784958412656499)
      ·
        refine ⟨5211346066177437618984749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3474230710784958412656499 5211346066177437618984749)
        ·
          refine ⟨1954254774816539107119281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5211346066177437618984749 1954254774816539107119281)
          ·
            refine ⟨1465691081112404330339461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1954254774816539107119281 1465691081112404330339461)
            ·
              refine ⟨274817077708575811938649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1465691081112404330339461 274817077708575811938649)
              ·
                refine ⟨206112808281431858953987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274817077708575811938649 206112808281431858953987)
                ·
                  refine ⟨309169212422147788430981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206112808281431858953987 309169212422147788430981)
                  ·
                    refine ⟨57969227329152710330809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 309169212422147788430981 57969227329152710330809)
                    ·
                      rfl

theorem cell23_338684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_338684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338684 prefixEnd_338684 := by exact prefixLift 338684
  have htrace : WordTrace (prefixWord ++ tailWord_338684) baseStart_338684 baseEnd_338684 := by
    simpa [prefixWord, tailWord_338684, baseEnd_338684] using wordTrace_append hprefix tailTrace_338684
  have hstable : (prefixWord ++ tailWord_338684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338684).length < 2 ^ (prefixWord ++ tailWord_338684).sum := by decide
  have hdescent : baseEnd_338684 < baseStart_338684 := by decide
  rcases family_descends (prefixWord ++ tailWord_338684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338700 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 1, 5, 2]
def baseStart_338700 : Nat := 118140960795 + 338700 * 2 ^ 59
def prefixEnd_338700 : Nat := 4983230072969 + 3 ^ 40 * 338700 * 2
def baseEnd_338700 : Nat := 173915897677930068392353

theorem tailTrace_338700 : CollatzResearch.WordTrace tailWord_338700 prefixEnd_338700 173915897677930068392353 := by
  unfold tailWord_338700
  simp only [CollatzResearch.WordTrace]
  refine ⟨6176701936477610099902777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8235602581970146799870369 6176701936477610099902777)
  ·
    refine ⟨4632526452358207574927083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6176701936477610099902777 4632526452358207574927083)
    ·
      refine ⟨6948789678537311362390625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4632526452358207574927083 6948789678537311362390625)
      ·
        refine ⟨5211592258902983521792969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6948789678537311362390625 5211592258902983521792969)
        ·
          refine ⟨3908694194177237641344727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5211592258902983521792969 3908694194177237641344727)
          ·
            refine ⟨5863041291265856462017091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908694194177237641344727 5863041291265856462017091)
            ·
              refine ⟨8794561936898784693025637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5863041291265856462017091 8794561936898784693025637)
              ·
                refine ⟨1648980363168522129942307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8794561936898784693025637 1648980363168522129942307)
                ·
                  refine ⟨2473470544752783194913461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1648980363168522129942307 2473470544752783194913461)
                  ·
                    refine ⟨231887863570573424523137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2473470544752783194913461 231887863570573424523137)
                    ·
                      refine ⟨173915897677930068392353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 231887863570573424523137 173915897677930068392353)
                      ·
                        rfl

theorem cell23_338700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_338700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338700 prefixEnd_338700 := by exact prefixLift 338700
  have htrace : WordTrace (prefixWord ++ tailWord_338700) baseStart_338700 baseEnd_338700 := by
    simpa [prefixWord, tailWord_338700, baseEnd_338700] using wordTrace_append hprefix tailTrace_338700
  have hstable : (prefixWord ++ tailWord_338700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338700).length < 2 ^ (prefixWord ++ tailWord_338700).sum := by decide
  have hdescent : baseEnd_338700 < baseStart_338700 := by decide
  rcases family_descends (prefixWord ++ tailWord_338700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338743 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_338743 : Nat := 118140960795 + 338743 * 2 ^ 59
def prefixEnd_338743 : Nat := 4983230072969 + 3 ^ 40 * 338743 * 2
def baseEnd_338743 : Nat := 173937977346073400154655

theorem tailTrace_338743 : CollatzResearch.WordTrace tailWord_338743 prefixEnd_338743 173937977346073400154655 := by
  unfold tailWord_338743
  simp only [CollatzResearch.WordTrace]
  refine ⟨12354972211799438543620883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8236648141199625695747255 12354972211799438543620883)
  ·
    refine ⟨18532458317699157815431325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12354972211799438543620883 18532458317699157815431325)
    ·
      refine ⟨6949671869137184180786747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18532458317699157815431325 6949671869137184180786747)
      ·
        refine ⟨10424507803705776271180121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6949671869137184180786747 10424507803705776271180121)
        ·
          refine ⟨7818380852779332203385091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10424507803705776271180121 7818380852779332203385091)
          ·
            refine ⟨11727571279168998305077637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7818380852779332203385091 11727571279168998305077637)
            ·
              refine ⟨2198919614844187182202057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11727571279168998305077637 2198919614844187182202057)
              ·
                refine ⟨1649189711133140386651543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2198919614844187182202057 1649189711133140386651543)
                ·
                  refine ⟨2473784566699710579977315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649189711133140386651543 2473784566699710579977315)
                  ·
                    refine ⟨3710676850049565869965973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2473784566699710579977315 3710676850049565869965973)
                    ·
                      refine ⟨173937977346073400154655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3710676850049565869965973 173937977346073400154655)
                      ·
                        rfl

theorem cell23_338743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_338743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338743 prefixEnd_338743 := by exact prefixLift 338743
  have htrace : WordTrace (prefixWord ++ tailWord_338743) baseStart_338743 baseEnd_338743 := by
    simpa [prefixWord, tailWord_338743, baseEnd_338743] using wordTrace_append hprefix tailTrace_338743
  have hstable : (prefixWord ++ tailWord_338743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338743).length < 2 ^ (prefixWord ++ tailWord_338743).sum := by decide
  have hdescent : baseEnd_338743 < baseStart_338743 := by decide
  rcases family_descends (prefixWord ++ tailWord_338743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338764 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 3, 2, 2]
def baseStart_338764 : Nat := 118140960795 + 338764 * 2 ^ 59
def prefixEnd_338764 : Nat := 4983230072969 + 3 ^ 40 * 338764 * 2
def baseEnd_338764 : Nat := 173948760439817817992059

theorem tailTrace_338764 : CollatzResearch.WordTrace tailWord_338764 prefixEnd_338764 173948760439817817992059 := by
  unfold tailWord_338764
  simp only [CollatzResearch.WordTrace]
  refine ⟨6177869072361679565067673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8237158763148906086756897 6177869072361679565067673)
  ·
    refine ⟨4633401804271259673800755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6177869072361679565067673 4633401804271259673800755)
    ·
      refine ⟨6950102706406889510701133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4633401804271259673800755 6950102706406889510701133)
      ·
        refine ⟨2606288514902583566512925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6950102706406889510701133 2606288514902583566512925)
        ·
          refine ⟨977358193088468837442347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2606288514902583566512925 977358193088468837442347)
          ·
            refine ⟨1466037289632703256163521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977358193088468837442347 1466037289632703256163521)
            ·
              refine ⟨1099527967224527442122641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466037289632703256163521 1099527967224527442122641)
              ·
                refine ⟨824645975418395581591981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099527967224527442122641 824645975418395581591981)
                ·
                  refine ⟨309242240781898343096993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824645975418395581591981 309242240781898343096993)
                  ·
                    refine ⟨231931680586423757322745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 309242240781898343096993 231931680586423757322745)
                    ·
                      refine ⟨173948760439817817992059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 231931680586423757322745 173948760439817817992059)
                      ·
                        rfl

theorem cell23_338764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_338764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338764 prefixEnd_338764 := by exact prefixLift 338764
  have htrace : WordTrace (prefixWord ++ tailWord_338764) baseStart_338764 baseEnd_338764 := by
    simpa [prefixWord, tailWord_338764, baseEnd_338764] using wordTrace_append hprefix tailTrace_338764
  have hstable : (prefixWord ++ tailWord_338764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338764).length < 2 ^ (prefixWord ++ tailWord_338764).sum := by decide
  have hdescent : baseEnd_338764 < baseStart_338764 := by decide
  rcases family_descends (prefixWord ++ tailWord_338764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338798 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_338798 : Nat := 118140960795 + 338798 * 2 ^ 59
def prefixEnd_338798 : Nat := 4983230072969 + 3 ^ 40 * 338798 * 2
def baseEnd_338798 : Nat := 173966218782070684966903

theorem tailTrace_338798 : CollatzResearch.WordTrace tailWord_338798 prefixEnd_338798 173966218782070684966903 := by
  unfold tailWord_338798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1544622278325022867109131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8237985484400121957915365 1544622278325022867109131)
  ·
    refine ⟨2316933417487534300663697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1544622278325022867109131 2316933417487534300663697)
    ·
      refine ⟨1737700063115650725497773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2316933417487534300663697 1737700063115650725497773)
      ·
        refine ⟨651637523668369022061665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1737700063115650725497773 651637523668369022061665)
        ·
          refine ⟨488728142751276766546249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 651637523668369022061665 488728142751276766546249)
          ·
            refine ⟨366546107063457574909687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488728142751276766546249 366546107063457574909687)
            ·
              refine ⟨549819160595186362364531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366546107063457574909687 549819160595186362364531)
              ·
                refine ⟨824728740892779543546797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549819160595186362364531 824728740892779543546797)
                ·
                  refine ⟨309273277834792328830049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824728740892779543546797 309273277834792328830049)
                  ·
                    refine ⟨231954958376094246622537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 309273277834792328830049 231954958376094246622537)
                    ·
                      refine ⟨173966218782070684966903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 231954958376094246622537 173966218782070684966903)
                      ·
                        rfl

theorem cell23_338798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_338798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338798 prefixEnd_338798 := by exact prefixLift 338798
  have htrace : WordTrace (prefixWord ++ tailWord_338798) baseStart_338798 baseEnd_338798 := by
    simpa [prefixWord, tailWord_338798, baseEnd_338798] using wordTrace_append hprefix tailTrace_338798
  have hstable : (prefixWord ++ tailWord_338798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338798).length < 2 ^ (prefixWord ++ tailWord_338798).sum := by decide
  have hdescent : baseEnd_338798 < baseStart_338798 := by decide
  rcases family_descends (prefixWord ++ tailWord_338798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338824 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 3, 3, 2]
def baseStart_338824 : Nat := 118140960795 + 338824 * 2 ^ 59
def prefixEnd_338824 : Nat := 4983230072969 + 3 ^ 40 * 338824 * 2
def baseEnd_338824 : Nat := 173979569279087583241783

theorem tailTrace_338824 : CollatzResearch.WordTrace tailWord_338824 prefixEnd_338824 173979569279087583241783 := by
  unfold tailWord_338824
  simp only [CollatzResearch.WordTrace]
  refine ⟨6178963262252994688659763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8238617683003992918213017 6178963262252994688659763)
  ·
    refine ⟨9268444893379492032989645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6178963262252994688659763 9268444893379492032989645)
    ·
      refine ⟨3475666835017309512371117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9268444893379492032989645 3475666835017309512371117)
      ·
        refine ⟨1303375063131491067139169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3475666835017309512371117 1303375063131491067139169)
        ·
          refine ⟨977531297348618300354377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1303375063131491067139169 977531297348618300354377)
          ·
            refine ⟨733148473011463725265783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977531297348618300354377 733148473011463725265783)
            ·
              refine ⟨1099722709517195587898675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733148473011463725265783 1099722709517195587898675)
              ·
                refine ⟨1649584064275793381848013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099722709517195587898675 1649584064275793381848013)
                ·
                  refine ⟨618594024103422518193005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1649584064275793381848013 618594024103422518193005)
                  ·
                    refine ⟨231972759038783444322377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 618594024103422518193005 231972759038783444322377)
                    ·
                      refine ⟨173979569279087583241783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 231972759038783444322377 173979569279087583241783)
                      ·
                        rfl

theorem cell23_338824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_338824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338824 prefixEnd_338824 := by exact prefixLift 338824
  have htrace : WordTrace (prefixWord ++ tailWord_338824) baseStart_338824 baseEnd_338824 := by
    simpa [prefixWord, tailWord_338824, baseEnd_338824] using wordTrace_append hprefix tailTrace_338824
  have hstable : (prefixWord ++ tailWord_338824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338824).length < 2 ^ (prefixWord ++ tailWord_338824).sum := by decide
  have hdescent : baseEnd_338824 < baseStart_338824 := by decide
  rcases family_descends (prefixWord ++ tailWord_338824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338837 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 3, 4, 2]
def baseStart_338837 : Nat := 118140960795 + 338837 * 2 ^ 59
def prefixEnd_338837 : Nat := 4983230072969 + 3 ^ 40 * 338837 * 2
def baseEnd_338837 : Nat := 173986244527596032379223

theorem tailTrace_338837 : CollatzResearch.WordTrace tailWord_338837 prefixEnd_338837 173986244527596032379223 := by
  unfold tailWord_338837
  simp only [CollatzResearch.WordTrace]
  refine ⟨12358400673458892597542765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8238933782305928398361843 12358400673458892597542765)
  ·
    refine ⟨4634400252547084724078537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12358400673458892597542765 4634400252547084724078537)
    ·
      refine ⟨3475800189410313543058903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4634400252547084724078537 3475800189410313543058903)
      ·
        refine ⟨5213700284115470314588355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3475800189410313543058903 5213700284115470314588355)
        ·
          refine ⟨7820550426173205471882533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213700284115470314588355 7820550426173205471882533)
          ·
            refine ⟨1466353204907476025977975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7820550426173205471882533 1466353204907476025977975)
            ·
              refine ⟨2199529807361214038966963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466353204907476025977975 2199529807361214038966963)
              ·
                refine ⟨3299294711041821058450445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2199529807361214038966963 3299294711041821058450445)
                ·
                  refine ⟨1237235516640682896918917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3299294711041821058450445 1237235516640682896918917)
                  ·
                    refine ⟨231981659370128043172297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1237235516640682896918917 231981659370128043172297)
                    ·
                      refine ⟨173986244527596032379223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 231981659370128043172297 173986244527596032379223)
                      ·
                        rfl

theorem cell23_338837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_338837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338837 prefixEnd_338837 := by exact prefixLift 338837
  have htrace : WordTrace (prefixWord ++ tailWord_338837) baseStart_338837 baseEnd_338837 := by
    simpa [prefixWord, tailWord_338837, baseEnd_338837] using wordTrace_append hprefix tailTrace_338837
  have hstable : (prefixWord ++ tailWord_338837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338837).length < 2 ^ (prefixWord ++ tailWord_338837).sum := by decide
  have hdescent : baseEnd_338837 < baseStart_338837 := by decide
  rcases family_descends (prefixWord ++ tailWord_338837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338877 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 7]
def baseStart_338877 : Nat := 118140960795 + 338877 * 2 ^ 59
def prefixEnd_338877 : Nat := 4983230072969 + 3 ^ 40 * 338877 * 2
def baseEnd_338877 : Nat := 19334087083752875097671

theorem tailTrace_338877 : CollatzResearch.WordTrace tailWord_338877 prefixEnd_338877 19334087083752875097671 := by
  unfold tailWord_338877
  simp only [CollatzResearch.WordTrace]
  refine ⟨12359859593313979428998885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8239906395542652952665923 12359859593313979428998885)
  ·
    refine ⟨2317473673746371142937291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12359859593313979428998885 2317473673746371142937291)
    ·
      refine ⟨3476210510619556714405937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2317473673746371142937291 3476210510619556714405937)
      ·
        refine ⟨2607157882964667535804453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3476210510619556714405937 2607157882964667535804453)
        ·
          refine ⟨488842103055875162963335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2607157882964667535804453 488842103055875162963335)
          ·
            refine ⟨733263154583812744445003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488842103055875162963335 733263154583812744445003)
            ·
              refine ⟨1099894731875719116667505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733263154583812744445003 1099894731875719116667505)
              ·
                refine ⟨824921048906789337500629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099894731875719116667505 824921048906789337500629)
                ·
                  refine ⟨19334087083752875097671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 824921048906789337500629 19334087083752875097671)
                  ·
                    rfl

theorem cell23_338877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_338877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338877 prefixEnd_338877 := by exact prefixLift 338877
  have htrace : WordTrace (prefixWord ++ tailWord_338877) baseStart_338877 baseEnd_338877 := by
    simpa [prefixWord, tailWord_338877, baseEnd_338877] using wordTrace_append hprefix tailTrace_338877
  have hstable : (prefixWord ++ tailWord_338877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338877).length < 2 ^ (prefixWord ++ tailWord_338877).sum := by decide
  have hdescent : baseEnd_338877 < baseStart_338877 := by decide
  rcases family_descends (prefixWord ++ tailWord_338877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338894 : List Nat := [4, 1, 1, 1, 2, 4, 2, 3, 5]
def baseStart_338894 : Nat := 118140960795 + 338894 * 2 ^ 59
def prefixEnd_338894 : Nat := 4983230072969 + 3 ^ 40 * 338894 * 2
def baseEnd_338894 : Nat := 19335056991655812151829

theorem tailTrace_338894 : CollatzResearch.WordTrace tailWord_338894 prefixEnd_338894 19335056991655812151829 := by
  unfold tailWord_338894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1545059954281548916545967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8240319756168260888245157 1545059954281548916545967)
  ·
    refine ⟨2317589931422323374818951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1545059954281548916545967 2317589931422323374818951)
    ·
      refine ⟨3476384897133485062228427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2317589931422323374818951 3476384897133485062228427)
      ·
        refine ⟨5214577345700227593342641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3476384897133485062228427 5214577345700227593342641)
        ·
          refine ⟨3910933009275170695006981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5214577345700227593342641 3910933009275170695006981)
          ·
            refine ⟨733299939239094505313809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3910933009275170695006981 733299939239094505313809)
            ·
              refine ⟨549974954429320878985357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733299939239094505313809 549974954429320878985357)
              ·
                refine ⟨206240607910995329619509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 549974954429320878985357 206240607910995329619509)
                ·
                  refine ⟨19335056991655812151829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206240607910995329619509 19335056991655812151829)
                  ·
                    rfl

theorem cell23_338894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_338894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338894 prefixEnd_338894 := by exact prefixLift 338894
  have htrace : WordTrace (prefixWord ++ tailWord_338894) baseStart_338894 baseEnd_338894 := by
    simpa [prefixWord, tailWord_338894, baseEnd_338894] using wordTrace_append hprefix tailTrace_338894
  have hstable : (prefixWord ++ tailWord_338894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338894).length < 2 ^ (prefixWord ++ tailWord_338894).sum := by decide
  have hdescent : baseEnd_338894 < baseStart_338894 := by decide
  rcases family_descends (prefixWord ++ tailWord_338894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338937 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 3, 4]
def baseStart_338937 : Nat := 118140960795 + 338937 * 2 ^ 59
def prefixEnd_338937 : Nat := 4983230072969 + 3 ^ 40 * 338937 * 2
def baseEnd_338937 : Nat := 58012530864348547042921

theorem tailTrace_338937 : CollatzResearch.WordTrace tailWord_338937 prefixEnd_338937 58012530864348547042921 := by
  unfold tailWord_338937
  simp only [CollatzResearch.WordTrace]
  refine ⟨12362047973096609676183065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8241365315397739784122043 12362047973096609676183065)
  ·
    refine ⟨9271535979822457257137299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12362047973096609676183065 9271535979822457257137299)
    ·
      refine ⟨13907303969733685885705949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9271535979822457257137299 13907303969733685885705949)
      ·
        refine ⟨5215238988650132207139731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13907303969733685885705949 5215238988650132207139731)
        ·
          refine ⟨7822858482975198310709597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5215238988650132207139731 7822858482975198310709597)
          ·
            refine ⟨2933571931115699366516099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7822858482975198310709597 2933571931115699366516099)
            ·
              refine ⟨4400357896673549049774149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933571931115699366516099 4400357896673549049774149)
              ·
                refine ⟨825067105626290446832653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4400357896673549049774149 825067105626290446832653)
                ·
                  refine ⟨309400164609858917562245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 825067105626290446832653 309400164609858917562245)
                  ·
                    refine ⟨58012530864348547042921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 309400164609858917562245 58012530864348547042921)
                    ·
                      rfl

theorem cell23_338937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 4].length) (baseStart_338937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338937 prefixEnd_338937 := by exact prefixLift 338937
  have htrace : WordTrace (prefixWord ++ tailWord_338937) baseStart_338937 baseEnd_338937 := by
    simpa [prefixWord, tailWord_338937, baseEnd_338937] using wordTrace_append hprefix tailTrace_338937
  have hstable : (prefixWord ++ tailWord_338937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338937).length < 2 ^ (prefixWord ++ tailWord_338937).sum := by decide
  have hdescent : baseEnd_338937 < baseStart_338937 := by decide
  rcases family_descends (prefixWord ++ tailWord_338937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338967 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 8]
def baseStart_338967 : Nat := 118140960795 + 338967 * 2 ^ 59
def prefixEnd_338967 : Nat := 4983230072969 + 3 ^ 40 * 338967 * 2
def baseEnd_338967 : Nat := 19339221890297835972625

theorem tailTrace_338967 : CollatzResearch.WordTrace tailWord_338967 prefixEnd_338967 19339221890297835972625 := by
  unfold tailWord_338967
  simp only [CollatzResearch.WordTrace]
  refine ⟨12363142162987924799775155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8242094775325283199850103 12363142162987924799775155)
  ·
    refine ⟨18544713244481887199662733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12363142162987924799775155 18544713244481887199662733)
    ·
      refine ⟨6954267466680707699873525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18544713244481887199662733 6954267466680707699873525)
      ·
        refine ⟨651962575001316346863143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6954267466680707699873525 651962575001316346863143)
        ·
          refine ⟨977943862501974520294715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651962575001316346863143 977943862501974520294715)
          ·
            refine ⟨1466915793752961780442073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977943862501974520294715 1466915793752961780442073)
            ·
              refine ⟨1100186845314721335331555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466915793752961780442073 1100186845314721335331555)
              ·
                refine ⟨1650280267972082002997333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1100186845314721335331555 1650280267972082002997333)
                ·
                  refine ⟨19339221890297835972625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1650280267972082002997333 19339221890297835972625)
                  ·
                    rfl

theorem cell23_338967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 8].length) (baseStart_338967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338967 prefixEnd_338967 := by exact prefixLift 338967
  have htrace : WordTrace (prefixWord ++ tailWord_338967) baseStart_338967 baseEnd_338967 := by
    simpa [prefixWord, tailWord_338967, baseEnd_338967] using wordTrace_append hprefix tailTrace_338967
  have hstable : (prefixWord ++ tailWord_338967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338967).length < 2 ^ (prefixWord ++ tailWord_338967).sum := by decide
  have hdescent : baseEnd_338967 < baseStart_338967 := by decide
  rcases family_descends (prefixWord ++ tailWord_338967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338994 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3]
def baseStart_338994 : Nat := 118140960795 + 338994 * 2 ^ 59
def prefixEnd_338994 : Nat := 4983230072969 + 3 ^ 40 * 338994 * 2
def baseEnd_338994 : Nat := 174066860990351918116001

theorem tailTrace_338994 : CollatzResearch.WordTrace tailWord_338994 prefixEnd_338994 174066860990351918116001 := by
  unfold tailWord_338994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3091031733472527102752009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8242751289260072274005357 3091031733472527102752009)
  ·
    refine ⟨2318273800104395327064007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3091031733472527102752009 2318273800104395327064007)
    ·
      refine ⟨3477410700156592990596011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2318273800104395327064007 3477410700156592990596011)
      ·
        refine ⟨5216116050234889485894017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3477410700156592990596011 5216116050234889485894017)
        ·
          refine ⟨3912087037676167114420513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5216116050234889485894017 3912087037676167114420513)
          ·
            refine ⟨2934065278257125335815385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3912087037676167114420513 2934065278257125335815385)
            ·
              refine ⟨2200548958692844001861539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2934065278257125335815385 2200548958692844001861539)
              ·
                refine ⟨3300823438039266002792309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2200548958692844001861539 3300823438039266002792309)
                ·
                  refine ⟨309452197316181187761779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3300823438039266002792309 309452197316181187761779)
                  ·
                    refine ⟨464178295974271781642669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 309452197316181187761779 464178295974271781642669)
                    ·
                      refine ⟨174066860990351918116001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 464178295974271781642669 174066860990351918116001)
                      ·
                        rfl

theorem cell23_338994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_338994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_338994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_338994 prefixEnd_338994 := by exact prefixLift 338994
  have htrace : WordTrace (prefixWord ++ tailWord_338994) baseStart_338994 baseEnd_338994 := by
    simpa [prefixWord, tailWord_338994, baseEnd_338994] using wordTrace_append hprefix tailTrace_338994
  have hstable : (prefixWord ++ tailWord_338994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338994).length < 2 ^ (prefixWord ++ tailWord_338994).sum := by decide
  have hdescent : baseEnd_338994 < baseStart_338994 := by decide
  rcases family_descends (prefixWord ++ tailWord_338994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339011 : List Nat := [1, 1, 1, 3, 1, 2, 4, 5, 1, 1, 3]
def baseStart_339011 : Nat := 118140960795 + 339011 * 2 ^ 59
def prefixEnd_339011 : Nat := 4983230072969 + 3 ^ 40 * 339011 * 2
def baseEnd_339011 : Nat := 174075590161478351603423

theorem tailTrace_339011 : CollatzResearch.WordTrace tailWord_339011 prefixEnd_339011 174075590161478351603423 := by
  unfold tailWord_339011
  simp only [CollatzResearch.WordTrace]
  refine ⟨12364746974828520314376887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8243164649885680209584591 12364746974828520314376887)
  ·
    refine ⟨18547120462242780471565331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12364746974828520314376887 18547120462242780471565331)
    ·
      refine ⟨27820680693364170707347997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18547120462242780471565331 27820680693364170707347997)
      ·
        refine ⟨10432755260011564015255499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27820680693364170707347997 10432755260011564015255499)
        ·
          refine ⟨15649132890017346022883249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10432755260011564015255499 15649132890017346022883249)
          ·
            refine ⟨11736849667513009517162437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15649132890017346022883249 11736849667513009517162437)
            ·
              refine ⟨2200659312658689284467957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11736849667513009517162437 2200659312658689284467957)
              ·
                refine ⟨206311810561752120418871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2200659312658689284467957 206311810561752120418871)
                ·
                  refine ⟨309467715842628180628307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206311810561752120418871 309467715842628180628307)
                  ·
                    refine ⟨464201573763942270942461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 309467715842628180628307 464201573763942270942461)
                    ·
                      refine ⟨174075590161478351603423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 464201573763942270942461 174075590161478351603423)
                      ·
                        rfl

theorem cell23_339011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 1, 1, 3].length) (baseStart_339011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339011 prefixEnd_339011 := by exact prefixLift 339011
  have htrace : WordTrace (prefixWord ++ tailWord_339011) baseStart_339011 baseEnd_339011 := by
    simpa [prefixWord, tailWord_339011, baseEnd_339011] using wordTrace_append hprefix tailTrace_339011
  have hstable : (prefixWord ++ tailWord_339011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339011).length < 2 ^ (prefixWord ++ tailWord_339011).sum := by decide
  have hdescent : baseEnd_339011 < baseStart_339011 := by decide
  rcases family_descends (prefixWord ++ tailWord_339011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339107 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 4]
def baseStart_339107 : Nat := 118140960795 + 339107 * 2 ^ 59
def prefixEnd_339107 : Nat := 4983230072969 + 3 ^ 40 * 339107 * 2
def baseEnd_339107 : Nat := 174124884304309976002981

theorem tailTrace_339107 : CollatzResearch.WordTrace tailWord_339107 prefixEnd_339107 174124884304309976002981 := by
  unfold tailWord_339107
  simp only [CollatzResearch.WordTrace]
  refine ⟨12368248382480728709871575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8245498921653819139914383 12368248382480728709871575)
  ·
    refine ⟨18552372573721093064807363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12368248382480728709871575 18552372573721093064807363)
    ·
      refine ⟨27828558860581639597211045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18552372573721093064807363 27828558860581639597211045)
      ·
        refine ⟨5217854786359057424477071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27828558860581639597211045 5217854786359057424477071)
        ·
          refine ⟨7826782179538586136715607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5217854786359057424477071 7826782179538586136715607)
          ·
            refine ⟨11740173269307879205073411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7826782179538586136715607 11740173269307879205073411)
            ·
              refine ⟨17610259903961818807610117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11740173269307879205073411 17610259903961818807610117)
              ·
                refine ⟨3301923731992841026426897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17610259903961818807610117 3301923731992841026426897)
                ·
                  refine ⟨2476442798994630769820173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3301923731992841026426897 2476442798994630769820173)
                  ·
                    refine ⟨928666049622986538682565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2476442798994630769820173 928666049622986538682565)
                    ·
                      refine ⟨174124884304309976002981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 928666049622986538682565 174124884304309976002981)
                      ·
                        rfl

theorem cell23_339107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_339107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339107 prefixEnd_339107 := by exact prefixLift 339107
  have htrace : WordTrace (prefixWord ++ tailWord_339107) baseStart_339107 baseEnd_339107 := by
    simpa [prefixWord, tailWord_339107, baseEnd_339107] using wordTrace_append hprefix tailTrace_339107
  have hstable : (prefixWord ++ tailWord_339107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339107).length < 2 ^ (prefixWord ++ tailWord_339107).sum := by decide
  have hdescent : baseEnd_339107 < baseStart_339107 := by decide
  rcases family_descends (prefixWord ++ tailWord_339107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339147 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 7]
def baseStart_339147 : Nat := 118140960795 + 339147 * 2 ^ 59
def prefixEnd_339147 : Nat := 4983230072969 + 3 ^ 40 * 339147 * 2
def baseEnd_339147 : Nat := 19349491503387757722533

theorem tailTrace_339147 : CollatzResearch.WordTrace tailWord_339147 prefixEnd_339147 19349491503387757722533 := by
  unfold tailWord_339147
  simp only [CollatzResearch.WordTrace]
  refine ⟨12369707302335815541327695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8246471534890543694218463 12369707302335815541327695)
  ·
    refine ⟨18554560953503723311991543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12369707302335815541327695 18554560953503723311991543)
    ·
      refine ⟨27831841430255584967987315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18554560953503723311991543 27831841430255584967987315)
      ·
        refine ⟨41747762145383377451980973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27831841430255584967987315 41747762145383377451980973)
        ·
          refine ⟨15655410804518766544492865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41747762145383377451980973 15655410804518766544492865)
          ·
            refine ⟨11741558103389074908369649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15655410804518766544492865 11741558103389074908369649)
            ·
              refine ⟨8806168577541806181277237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11741558103389074908369649 8806168577541806181277237)
              ·
                refine ⟨825578304144544329494741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8806168577541806181277237 825578304144544329494741)
                ·
                  refine ⟨19349491503387757722533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 825578304144544329494741 19349491503387757722533)
                  ·
                    rfl

theorem cell23_339147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 7].length) (baseStart_339147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339147 prefixEnd_339147 := by exact prefixLift 339147
  have htrace : WordTrace (prefixWord ++ tailWord_339147) baseStart_339147 baseEnd_339147 := by
    simpa [prefixWord, tailWord_339147, baseEnd_339147] using wordTrace_append hprefix tailTrace_339147
  have hstable : (prefixWord ++ tailWord_339147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339147).length < 2 ^ (prefixWord ++ tailWord_339147).sum := by decide
  have hdescent : baseEnd_339147 < baseStart_339147 := by decide
  rcases family_descends (prefixWord ++ tailWord_339147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339154 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_339154 : Nat := 118140960795 + 339154 * 2 ^ 59
def prefixEnd_339154 : Nat := 4983230072969 + 3 ^ 40 * 339154 * 2
def baseEnd_339154 : Nat := 174149017895071292115265

theorem tailTrace_339154 : CollatzResearch.WordTrace tailWord_339154 prefixEnd_339154 174149017895071292115265 := by
  unfold tailWord_339154
  simp only [CollatzResearch.WordTrace]
  refine ⟨3092490653327613934208129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8246641742206970491221677 3092490653327613934208129)
  ·
    refine ⟨2319367989995710450656097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3092490653327613934208129 2319367989995710450656097)
    ·
      refine ⟨1739525992496782837992073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2319367989995710450656097 1739525992496782837992073)
      ·
        refine ⟨1304644494372587128494055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1739525992496782837992073 1304644494372587128494055)
        ·
          refine ⟨1956966741558880692741083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304644494372587128494055 1956966741558880692741083)
          ·
            refine ⟨2935450112338321039111625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956966741558880692741083 2935450112338321039111625)
            ·
              refine ⟨2201587584253740779333719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2935450112338321039111625 2201587584253740779333719)
              ·
                refine ⟨3302381376380611169000579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201587584253740779333719 3302381376380611169000579)
                ·
                  refine ⟨4953572064570916753500869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302381376380611169000579 4953572064570916753500869)
                  ·
                    refine ⟨928794762107046891281413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4953572064570916753500869 928794762107046891281413)
                    ·
                      refine ⟨174149017895071292115265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 928794762107046891281413 174149017895071292115265)
                      ·
                        rfl

theorem cell23_339154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_339154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339154 prefixEnd_339154 := by exact prefixLift 339154
  have htrace : WordTrace (prefixWord ++ tailWord_339154) baseStart_339154 baseEnd_339154 := by
    simpa [prefixWord, tailWord_339154, baseEnd_339154] using wordTrace_append hprefix tailTrace_339154
  have hstable : (prefixWord ++ tailWord_339154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339154).length < 2 ^ (prefixWord ++ tailWord_339154).sum := by decide
  have hdescent : baseEnd_339154 < baseStart_339154 := by decide
  rcases family_descends (prefixWord ++ tailWord_339154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339194 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 2, 5]
def baseStart_339194 : Nat := 118140960795 + 339194 * 2 ^ 59
def prefixEnd_339194 : Nat := 4983230072969 + 3 ^ 40 * 339194 * 2
def baseEnd_339194 : Nat := 58056519040417045205027

theorem tailTrace_339194 : CollatzResearch.WordTrace tailWord_339194 prefixEnd_339194 58056519040417045205027 := by
  unfold tailWord_339194
  simp only [CollatzResearch.WordTrace]
  refine ⟨3092855383291385642072159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8247614355443695045525757 3092855383291385642072159)
  ·
    refine ⟨4639283074937078463108239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3092855383291385642072159 4639283074937078463108239)
    ·
      refine ⟨6958924612405617694662359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4639283074937078463108239 6958924612405617694662359)
      ·
        refine ⟨10438386918608426541993539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6958924612405617694662359 10438386918608426541993539)
        ·
          refine ⟨15657580377912639812990309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10438386918608426541993539 15657580377912639812990309)
          ·
            refine ⟨2935796320858619964935683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15657580377912639812990309 2935796320858619964935683)
            ·
              refine ⟨4403694481287929947403525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2935796320858619964935683 4403694481287929947403525)
              ·
                refine ⟨825692715241486865138161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4403694481287929947403525 825692715241486865138161)
                ·
                  refine ⟨619269536431115148853621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 825692715241486865138161 619269536431115148853621)
                  ·
                    refine ⟨58056519040417045205027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 619269536431115148853621 58056519040417045205027)
                    ·
                      rfl

theorem cell23_339194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_339194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339194 prefixEnd_339194 := by exact prefixLift 339194
  have htrace : WordTrace (prefixWord ++ tailWord_339194) baseStart_339194 baseEnd_339194 := by
    simpa [prefixWord, tailWord_339194, baseEnd_339194] using wordTrace_append hprefix tailTrace_339194
  have hstable : (prefixWord ++ tailWord_339194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339194).length < 2 ^ (prefixWord ++ tailWord_339194).sum := by decide
  have hdescent : baseEnd_339194 < baseStart_339194 := by decide
  rcases family_descends (prefixWord ++ tailWord_339194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339198 : List Nat := [4, 2, 2, 1, 1, 3, 1, 4, 5]
def baseStart_339198 : Nat := 118140960795 + 339198 * 2 ^ 59
def prefixEnd_339198 : Nat := 4983230072969 + 3 ^ 40 * 339198 * 2
def baseEnd_339198 : Nat := 19352401227096568885007

theorem tailTrace_339198 : CollatzResearch.WordTrace tailWord_339198 prefixEnd_339198 19352401227096568885007 := by
  unfold tailWord_339198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1546445928143881406429281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8247711616767367500956165 1546445928143881406429281)
  ·
    refine ⟨1159834446107911054821961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1546445928143881406429281 1159834446107911054821961)
    ·
      refine ⟨869875834580933291116471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1159834446107911054821961 869875834580933291116471)
      ·
        refine ⟨1304813751871399936674707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 869875834580933291116471 1304813751871399936674707)
        ·
          refine ⟨1957220627807099905012061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304813751871399936674707 1957220627807099905012061)
          ·
            refine ⟨733957735427662464379523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1957220627807099905012061 733957735427662464379523)
            ·
              refine ⟨1100936603141493696569285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733957735427662464379523 1100936603141493696569285)
              ·
                refine ⟨206425613089030068106741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1100936603141493696569285 206425613089030068106741)
                ·
                  refine ⟨19352401227096568885007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206425613089030068106741 19352401227096568885007)
                  ·
                    rfl

theorem cell23_339198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_339198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339198 prefixEnd_339198 := by exact prefixLift 339198
  have htrace : WordTrace (prefixWord ++ tailWord_339198) baseStart_339198 baseEnd_339198 := by
    simpa [prefixWord, tailWord_339198, baseEnd_339198] using wordTrace_append hprefix tailTrace_339198
  have hstable : (prefixWord ++ tailWord_339198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339198).length < 2 ^ (prefixWord ++ tailWord_339198).sum := by decide
  have hdescent : baseEnd_339198 < baseStart_339198 := by decide
  rcases family_descends (prefixWord ++ tailWord_339198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339201 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_339201 : Nat := 118140960795 + 339201 * 2 ^ 59
def prefixEnd_339201 : Nat := 4983230072969 + 3 ^ 40 * 339201 * 2
def baseEnd_339201 : Nat := 174173151485832608227549

theorem tailTrace_339201 : CollatzResearch.WordTrace tailWord_339201 prefixEnd_339201 174173151485832608227549 := by
  unfold tailWord_339201
  simp only [CollatzResearch.WordTrace]
  refine ⟨12371676844140182763793457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8247784562760121842528971 12371676844140182763793457)
  ·
    refine ⟨9278757633105137072845093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12371676844140182763793457 9278757633105137072845093)
    ·
      refine ⟨1739767056207213201158455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9278757633105137072845093 1739767056207213201158455)
      ·
        refine ⟨2609650584310819801737683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1739767056207213201158455 2609650584310819801737683)
        ·
          refine ⟨3914475876466229702606525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609650584310819801737683 3914475876466229702606525)
          ·
            refine ⟨1467928453674836138477447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3914475876466229702606525 1467928453674836138477447)
            ·
              refine ⟨2201892680512254207716171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467928453674836138477447 2201892680512254207716171)
              ·
                refine ⟨3302839020768381311574257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201892680512254207716171 3302839020768381311574257)
                ·
                  refine ⟨2477129265576285983680693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3302839020768381311574257 2477129265576285983680693)
                  ·
                    refine ⟨232230868647776810970065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2477129265576285983680693 232230868647776810970065)
                    ·
                      refine ⟨174173151485832608227549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 232230868647776810970065 174173151485832608227549)
                      ·
                        rfl

theorem cell23_339201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_339201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339201 prefixEnd_339201 := by exact prefixLift 339201
  have htrace : WordTrace (prefixWord ++ tailWord_339201) baseStart_339201 baseEnd_339201 := by
    simpa [prefixWord, tailWord_339201, baseEnd_339201] using wordTrace_append hprefix tailTrace_339201
  have hstable : (prefixWord ++ tailWord_339201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339201).length < 2 ^ (prefixWord ++ tailWord_339201).sum := by decide
  have hdescent : baseEnd_339201 < baseStart_339201 := by decide
  rcases family_descends (prefixWord ++ tailWord_339201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339231 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 4]
def baseStart_339231 : Nat := 118140960795 + 339231 * 2 ^ 59
def prefixEnd_339231 : Nat := 4983230072969 + 3 ^ 40 * 339231 * 2
def baseEnd_339231 : Nat := 174188555905467490852411

theorem tailTrace_339231 : CollatzResearch.WordTrace tailWord_339231 prefixEnd_339231 174188555905467490852411 := by
  unfold tailWord_339231
  simp only [CollatzResearch.WordTrace]
  refine ⟨12372771034031497887385547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8248514022687665258257031 12372771034031497887385547)
  ·
    refine ⟨18559156551047246831078321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12372771034031497887385547 18559156551047246831078321)
    ·
      refine ⟨13919367413285435123308741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18559156551047246831078321 13919367413285435123308741)
      ·
        refine ⟨2609881389991019085620389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13919367413285435123308741 2609881389991019085620389)
        ·
          refine ⟨489352760623316078553823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2609881389991019085620389 489352760623316078553823)
          ·
            refine ⟨734029140934974117830735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489352760623316078553823 734029140934974117830735)
            ·
              refine ⟨1101043711402461176746103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734029140934974117830735 1101043711402461176746103)
              ·
                refine ⟨1651565567103691765119155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101043711402461176746103 1651565567103691765119155)
                ·
                  refine ⟨2477348350655537647678733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651565567103691765119155 2477348350655537647678733)
                  ·
                    refine ⟨929005631495826617879525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2477348350655537647678733 929005631495826617879525)
                    ·
                      refine ⟨174188555905467490852411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 929005631495826617879525 174188555905467490852411)
                      ·
                        rfl

theorem cell23_339231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_339231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339231 prefixEnd_339231 := by exact prefixLift 339231
  have htrace : WordTrace (prefixWord ++ tailWord_339231) baseStart_339231 baseEnd_339231 := by
    simpa [prefixWord, tailWord_339231, baseEnd_339231] using wordTrace_append hprefix tailTrace_339231
  have hstable : (prefixWord ++ tailWord_339231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339231).length < 2 ^ (prefixWord ++ tailWord_339231).sum := by decide
  have hdescent : baseEnd_339231 < baseStart_339231 := by decide
  rcases family_descends (prefixWord ++ tailWord_339231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339258 : List Nat := [3, 1, 1, 1, 4, 1, 1, 6, 1, 4]
def baseStart_339258 : Nat := 118140960795 + 339258 * 2 ^ 59
def prefixEnd_339258 : Nat := 4983230072969 + 3 ^ 40 * 339258 * 2
def baseEnd_339258 : Nat := 58067473294379628404929

theorem tailTrace_339258 : CollatzResearch.WordTrace tailWord_339258 prefixEnd_339258 58067473294379628404929 := by
  unfold tailWord_339258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093438951233420374654607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8249170536622454332412285 3093438951233420374654607)
  ·
    refine ⟨4640158426850130561981911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3093438951233420374654607 4640158426850130561981911)
    ·
      refine ⟨6960237640275195842972867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4640158426850130561981911 6960237640275195842972867)
      ·
        refine ⟨10440356460412793764459301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6960237640275195842972867 10440356460412793764459301)
        ·
          refine ⟨1957566836327398830836119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10440356460412793764459301 1957566836327398830836119)
          ·
            refine ⟨2936350254491098246254179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957566836327398830836119 2936350254491098246254179)
            ·
              refine ⟨4404525381736647369381269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936350254491098246254179 4404525381736647369381269)
              ·
                refine ⟨206462127268905345439747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4404525381736647369381269 206462127268905345439747)
                ·
                  refine ⟨309693190903358018159621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206462127268905345439747 309693190903358018159621)
                  ·
                    refine ⟨58067473294379628404929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 309693190903358018159621 58067473294379628404929)
                    ·
                      rfl

theorem cell23_339258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_339258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339258 prefixEnd_339258 := by exact prefixLift 339258
  have htrace : WordTrace (prefixWord ++ tailWord_339258) baseStart_339258 baseEnd_339258 := by
    simpa [prefixWord, tailWord_339258, baseEnd_339258] using wordTrace_append hprefix tailTrace_339258
  have hstable : (prefixWord ++ tailWord_339258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339258).length < 2 ^ (prefixWord ++ tailWord_339258).sum := by decide
  have hdescent : baseEnd_339258 < baseStart_339258 := by decide
  rcases family_descends (prefixWord ++ tailWord_339258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339268 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_339268 : Nat := 118140960795 + 339268 * 2 ^ 59
def prefixEnd_339268 : Nat := 4983230072969 + 3 ^ 40 * 339268 * 2
def baseEnd_339268 : Nat := 174207554689683846089741

theorem tailTrace_339268 : CollatzResearch.WordTrace tailWord_339268 prefixEnd_339268 174207554689683846089741 := by
  unfold tailWord_339268
  simp only [CollatzResearch.WordTrace]
  refine ⟨6187060267448726603241229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8249413689931635470988305 6187060267448726603241229)
  ·
    refine ⟨2320147600293272476215461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6187060267448726603241229 2320147600293272476215461)
    ·
      refine ⟨435027675054988589290399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2320147600293272476215461 435027675054988589290399)
      ·
        refine ⟨652541512582482883935599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435027675054988589290399 652541512582482883935599)
        ·
          refine ⟨978812268873724325903399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652541512582482883935599 978812268873724325903399)
          ·
            refine ⟨1468218403310586488855099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978812268873724325903399 1468218403310586488855099)
            ·
              refine ⟨2202327604965879733282649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468218403310586488855099 2202327604965879733282649)
              ·
                refine ⟨1651745703724409799961987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202327604965879733282649 1651745703724409799961987)
                ·
                  refine ⟨2477618555586614699942981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651745703724409799961987 2477618555586614699942981)
                  ·
                    refine ⟨464553479172490256239309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2477618555586614699942981 464553479172490256239309)
                    ·
                      refine ⟨174207554689683846089741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 464553479172490256239309 174207554689683846089741)
                      ·
                        rfl

theorem cell23_339268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_339268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339268 prefixEnd_339268 := by exact prefixLift 339268
  have htrace : WordTrace (prefixWord ++ tailWord_339268) baseStart_339268 baseEnd_339268 := by
    simpa [prefixWord, tailWord_339268, baseEnd_339268] using wordTrace_append hprefix tailTrace_339268
  have hstable : (prefixWord ++ tailWord_339268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339268).length < 2 ^ (prefixWord ++ tailWord_339268).sum := by decide
  have hdescent : baseEnd_339268 < baseStart_339268 := by decide
  rcases family_descends (prefixWord ++ tailWord_339268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339301 : List Nat := [1, 3, 1, 3, 1, 2, 1, 5, 1, 5]
def baseStart_339301 : Nat := 118140960795 + 339301 * 2 ^ 59
def prefixEnd_339301 : Nat := 4983230072969 + 3 ^ 40 * 339301 * 2
def baseEnd_339301 : Nat := 58074833183760738992363

theorem tailTrace_339301 : CollatzResearch.WordTrace tailWord_339301 prefixEnd_339301 58074833183760738992363 := by
  unfold tailWord_339301
  simp only [CollatzResearch.WordTrace]
  refine ⟨12375324143777899842433757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8250216095851933228289171 12375324143777899842433757)
  ·
    refine ⟨4640746553916712440912659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12375324143777899842433757 4640746553916712440912659)
    ·
      refine ⟨6961119830875068661368989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4640746553916712440912659 6961119830875068661368989)
      ·
        refine ⟨2610419936578150748013371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6961119830875068661368989 2610419936578150748013371)
        ·
          refine ⟨3915629904867226122020057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2610419936578150748013371 3915629904867226122020057)
          ·
            refine ⟨2936722428650419591515043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3915629904867226122020057 2936722428650419591515043)
            ·
              refine ⟨4405083642975629387272565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936722428650419591515043 4405083642975629387272565)
              ·
                refine ⟨412976591528965255056803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4405083642975629387272565 412976591528965255056803)
                ·
                  refine ⟨619464887293447882585205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412976591528965255056803 619464887293447882585205)
                  ·
                    refine ⟨58074833183760738992363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 619464887293447882585205 58074833183760738992363)
                    ·
                      rfl

theorem cell23_339301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_339301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339301 prefixEnd_339301 := by exact prefixLift 339301
  have htrace : WordTrace (prefixWord ++ tailWord_339301) baseStart_339301 baseEnd_339301 := by
    simpa [prefixWord, tailWord_339301, baseEnd_339301] using wordTrace_append hprefix tailTrace_339301
  have hstable : (prefixWord ++ tailWord_339301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339301).length < 2 ^ (prefixWord ++ tailWord_339301).sum := by decide
  have hdescent : baseEnd_339301 < baseStart_339301 := by decide
  rcases family_descends (prefixWord ++ tailWord_339301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339308 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 4, 3, 2]
def baseStart_339308 : Nat := 118140960795 + 339308 * 2 ^ 59
def prefixEnd_339308 : Nat := 4983230072969 + 3 ^ 40 * 339308 * 2
def baseEnd_339308 : Nat := 174228093915863689589557

theorem tailTrace_339308 : CollatzResearch.WordTrace tailWord_339308 prefixEnd_339308 174228093915863689589557 := by
  unfold tailWord_339308
  simp only [CollatzResearch.WordTrace]
  refine ⟨6187789727376270018969289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8250386303168360025292385 6187789727376270018969289)
  ·
    refine ⟨4640842295532202514226967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6187789727376270018969289 4640842295532202514226967)
    ·
      refine ⟨6961263443298303771340451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4640842295532202514226967 6961263443298303771340451)
      ·
        refine ⟨10441895164947455657010677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6961263443298303771340451 10441895164947455657010677)
        ·
          refine ⟨978927671713823967844751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10441895164947455657010677 978927671713823967844751)
          ·
            refine ⟨1468391507570735951767127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978927671713823967844751 1468391507570735951767127)
            ·
              refine ⟨2202587261356103927650691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468391507570735951767127 2202587261356103927650691)
              ·
                refine ⟨3303880892034155891476037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2202587261356103927650691 3303880892034155891476037)
                ·
                  refine ⟨619477667256404229651757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3303880892034155891476037 619477667256404229651757)
                  ·
                    refine ⟨232304125221151586119409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 619477667256404229651757 232304125221151586119409)
                    ·
                      refine ⟨174228093915863689589557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 232304125221151586119409 174228093915863689589557)
                      ·
                        rfl

theorem cell23_339308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 3, 2].length) (baseStart_339308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339308 prefixEnd_339308 := by exact prefixLift 339308
  have htrace : WordTrace (prefixWord ++ tailWord_339308) baseStart_339308 baseEnd_339308 := by
    simpa [prefixWord, tailWord_339308, baseEnd_339308] using wordTrace_append hprefix tailTrace_339308
  have hstable : (prefixWord ++ tailWord_339308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339308).length < 2 ^ (prefixWord ++ tailWord_339308).sum := by decide
  have hdescent : baseEnd_339308 < baseStart_339308 := by decide
  rcases family_descends (prefixWord ++ tailWord_339308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339342 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2]
def baseStart_339342 : Nat := 118140960795 + 339342 * 2 ^ 59
def prefixEnd_339342 : Nat := 4983230072969 + 3 ^ 40 * 339342 * 2
def baseEnd_339342 : Nat := 174245552258116556564401

theorem tailTrace_339342 : CollatzResearch.WordTrace tailWord_339342 prefixEnd_339342 174245552258116556564401 := by
  unfold tailWord_339342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1547102442078670480584535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8251213024419575896450853 1547102442078670480584535)
  ·
    refine ⟨2320653663118005720876803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1547102442078670480584535 2320653663118005720876803)
    ·
      refine ⟨3480980494677008581315205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2320653663118005720876803 3480980494677008581315205)
      ·
        refine ⟨652683842751939108996601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3480980494677008581315205 652683842751939108996601)
        ·
          refine ⟨489512882063954331747451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652683842751939108996601 489512882063954331747451)
          ·
            refine ⟨734269323095931497621177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489512882063954331747451 734269323095931497621177)
            ·
              refine ⟨550701992321948623215883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734269323095931497621177 550701992321948623215883)
              ·
                refine ⟨826052988482922934823825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550701992321948623215883 826052988482922934823825)
                ·
                  refine ⟨619539741362192201117869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 826052988482922934823825 619539741362192201117869)
                  ·
                    refine ⟨232327403010822075419201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 619539741362192201117869 232327403010822075419201)
                    ·
                      refine ⟨174245552258116556564401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 232327403010822075419201 174245552258116556564401)
                      ·
                        rfl

theorem cell23_339342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_339342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339342 prefixEnd_339342 := by exact prefixLift 339342
  have htrace : WordTrace (prefixWord ++ tailWord_339342) baseStart_339342 baseEnd_339342 := by
    simpa [prefixWord, tailWord_339342, baseEnd_339342] using wordTrace_append hprefix tailTrace_339342
  have hstable : (prefixWord ++ tailWord_339342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339342).length < 2 ^ (prefixWord ++ tailWord_339342).sum := by decide
  have hdescent : baseEnd_339342 < baseStart_339342 := by decide
  rcases family_descends (prefixWord ++ tailWord_339342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339348 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_339348 : Nat := 118140960795 + 339348 * 2 ^ 59
def prefixEnd_339348 : Nat := 4983230072969 + 3 ^ 40 * 339348 * 2
def baseEnd_339348 : Nat := 58082877714014511029791

theorem tailTrace_339348 : CollatzResearch.WordTrace tailWord_339348 prefixEnd_339348 58082877714014511029791 := by
  unfold tailWord_339348
  simp only [CollatzResearch.WordTrace]
  refine ⟨6188519187303813434697349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8251358916405084579596465 6188519187303813434697349)
  ·
    refine ⟨1160347347619465019005753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6188519187303813434697349 1160347347619465019005753)
    ·
      refine ⟨870260510714598764254315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1160347347619465019005753 870260510714598764254315)
      ·
        refine ⟨1305390766071898146381473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 870260510714598764254315 1305390766071898146381473)
        ·
          refine ⟨979043074553923609786105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1305390766071898146381473 979043074553923609786105)
          ·
            refine ⟨734282305915442707339579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 979043074553923609786105 734282305915442707339579)
            ·
              refine ⟨1101423458873164061009369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734282305915442707339579 1101423458873164061009369)
              ·
                refine ⟨826067594154873045757027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1101423458873164061009369 826067594154873045757027)
                ·
                  refine ⟨1239101391232309568635541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826067594154873045757027 1239101391232309568635541)
                  ·
                    refine ⟨58082877714014511029791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1239101391232309568635541 58082877714014511029791)
                    ·
                      rfl

theorem cell23_339348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_339348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339348 prefixEnd_339348 := by exact prefixLift 339348
  have htrace : WordTrace (prefixWord ++ tailWord_339348) baseStart_339348 baseEnd_339348 := by
    simpa [prefixWord, tailWord_339348, baseEnd_339348] using wordTrace_append hprefix tailTrace_339348
  have hstable : (prefixWord ++ tailWord_339348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339348).length < 2 ^ (prefixWord ++ tailWord_339348).sum := by decide
  have hdescent : baseEnd_339348 < baseStart_339348 := by decide
  rcases family_descends (prefixWord ++ tailWord_339348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339428 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 3, 4, 2]
def baseStart_339428 : Nat := 118140960795 + 339428 * 2 ^ 59
def prefixEnd_339428 : Nat := 4983230072969 + 3 ^ 40 * 339428 * 2
def baseEnd_339428 : Nat := 174289711594403220089005

theorem tailTrace_339428 : CollatzResearch.WordTrace tailWord_339428 prefixEnd_339428 174289711594403220089005 := by
  unfold tailWord_339428
  simp only [CollatzResearch.WordTrace]
  refine ⟨6189978107158900266153469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8253304142878533688204625 6189978107158900266153469)
  ·
    refine ⟨2321241790184587599807551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6189978107158900266153469 2321241790184587599807551)
    ·
      refine ⟨3481862685276881399711327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2321241790184587599807551 3481862685276881399711327)
      ·
        refine ⟨5222794027915322099566991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3481862685276881399711327 5222794027915322099566991)
        ·
          refine ⟨7834191041872983149350487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5222794027915322099566991 7834191041872983149350487)
          ·
            refine ⟨11751286562809474724025731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7834191041872983149350487 11751286562809474724025731)
            ·
              refine ⟨17626929844214212086038597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11751286562809474724025731 17626929844214212086038597)
              ·
                refine ⟨3305049345790164766132237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17626929844214212086038597 3305049345790164766132237)
                ·
                  refine ⟨1239393504671311787299589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3305049345790164766132237 1239393504671311787299589)
                  ·
                    refine ⟨232386282125870960118673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1239393504671311787299589 232386282125870960118673)
                    ·
                      refine ⟨174289711594403220089005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 232386282125870960118673 174289711594403220089005)
                      ·
                        rfl

theorem cell23_339428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_339428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339428 prefixEnd_339428 := by exact prefixLift 339428
  have htrace : WordTrace (prefixWord ++ tailWord_339428) baseStart_339428 baseEnd_339428 := by
    simpa [prefixWord, tailWord_339428, baseEnd_339428] using wordTrace_append hprefix tailTrace_339428
  have hstable : (prefixWord ++ tailWord_339428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339428).length < 2 ^ (prefixWord ++ tailWord_339428).sum := by decide
  have hdescent : baseEnd_339428 < baseStart_339428 := by decide
  rcases family_descends (prefixWord ++ tailWord_339428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339498 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 4, 5]
def baseStart_339498 : Nat := 118140960795 + 339498 * 2 ^ 59
def prefixEnd_339498 : Nat := 4983230072969 + 3 ^ 40 * 339498 * 2
def baseEnd_339498 : Nat := 58108551746739315404561

theorem tailTrace_339498 : CollatzResearch.WordTrace tailWord_339498 prefixEnd_339498 58108551746739315404561 := by
  unfold tailWord_339498
  simp only [CollatzResearch.WordTrace]
  refine ⟨3095627331016050621838787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8255006216042801658236765 3095627331016050621838787)
  ·
    refine ⟨4643440996524075932758181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3095627331016050621838787 4643440996524075932758181)
    ·
      refine ⟨870645186848264237392159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4643440996524075932758181 870645186848264237392159)
      ·
        refine ⟨1305967780272396356088239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 870645186848264237392159 1305967780272396356088239)
        ·
          refine ⟨1958951670408594534132359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1305967780272396356088239 1958951670408594534132359)
          ·
            refine ⟨2938427505612891801198539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1958951670408594534132359 2938427505612891801198539)
            ·
              refine ⟨4407641258419337701797809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2938427505612891801198539 4407641258419337701797809)
              ·
                refine ⟨3305730943814503276348357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4407641258419337701797809 3305730943814503276348357)
                ·
                  refine ⟨619824551965219364315317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3305730943814503276348357 619824551965219364315317)
                  ·
                    refine ⟨58108551746739315404561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 619824551965219364315317 58108551746739315404561)
                    ·
                      rfl

theorem cell23_339498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_339498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339498 prefixEnd_339498 := by exact prefixLift 339498
  have htrace : WordTrace (prefixWord ++ tailWord_339498) baseStart_339498 baseEnd_339498 := by
    simpa [prefixWord, tailWord_339498, baseEnd_339498] using wordTrace_append hprefix tailTrace_339498
  have hstable : (prefixWord ++ tailWord_339498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339498).length < 2 ^ (prefixWord ++ tailWord_339498).sum := by decide
  have hdescent : baseEnd_339498 < baseStart_339498 := by decide
  rcases family_descends (prefixWord ++ tailWord_339498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339531 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 6]
def baseStart_339531 : Nat := 118140960795 + 339531 * 2 ^ 59
def prefixEnd_339531 : Nat := 4983230072969 + 3 ^ 40 * 339531 * 2
def baseEnd_339531 : Nat := 174342600101816317101031

theorem tailTrace_339531 : CollatzResearch.WordTrace tailWord_339531 prefixEnd_339531 174342600101816317101031 := by
  unfold tailWord_339531
  simp only [CollatzResearch.WordTrace]
  refine ⟨12383712932944649123306447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8255808621963099415537631 12383712932944649123306447)
  ·
    refine ⟨18575569399416973684959671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12383712932944649123306447 18575569399416973684959671)
    ·
      refine ⟨27863354099125460527439507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18575569399416973684959671 27863354099125460527439507)
      ·
        refine ⟨41795031148688190791159261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27863354099125460527439507 41795031148688190791159261)
        ·
          refine ⟨15673136680758071546684723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41795031148688190791159261 15673136680758071546684723)
          ·
            refine ⟨23509705021137107320027085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15673136680758071546684723 23509705021137107320027085)
            ·
              refine ⟨8816139382926415245010157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23509705021137107320027085 8816139382926415245010157)
              ·
                refine ⟨3306052268597405716878809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8816139382926415245010157 3306052268597405716878809)
                ·
                  refine ⟨2479539201448054287659107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3306052268597405716878809 2479539201448054287659107)
                  ·
                    refine ⟨3719308802172081431488661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2479539201448054287659107 3719308802172081431488661)
                    ·
                      refine ⟨174342600101816317101031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3719308802172081431488661 174342600101816317101031)
                      ·
                        rfl

theorem cell23_339531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 6].length) (baseStart_339531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339531 prefixEnd_339531 := by exact prefixLift 339531
  have htrace : WordTrace (prefixWord ++ tailWord_339531) baseStart_339531 baseEnd_339531 := by
    simpa [prefixWord, tailWord_339531, baseEnd_339531] using wordTrace_append hprefix tailTrace_339531
  have hstable : (prefixWord ++ tailWord_339531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339531).length < 2 ^ (prefixWord ++ tailWord_339531).sum := by decide
  have hdescent : baseEnd_339531 < baseStart_339531 := by decide
  rcases family_descends (prefixWord ++ tailWord_339531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339595 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 4, 3, 2]
def baseStart_339595 : Nat := 118140960795 + 339595 * 2 ^ 59
def prefixEnd_339595 : Nat := 4983230072969 + 3 ^ 40 * 339595 * 2
def baseEnd_339595 : Nat := 174375462863704066700737

theorem tailTrace_339595 : CollatzResearch.WordTrace tailWord_339595 prefixEnd_339595 174375462863704066700737 := by
  unfold tailWord_339595
  simp only [CollatzResearch.WordTrace]
  refine ⟨12386047204712788053636239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8257364803141858702424159 12386047204712788053636239)
  ·
    refine ⟨18579070807069182080454359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12386047204712788053636239 18579070807069182080454359)
    ·
      refine ⟨27868606210603773120681539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18579070807069182080454359 27868606210603773120681539)
      ·
        refine ⟨41802909315905659681022309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27868606210603773120681539 41802909315905659681022309)
        ·
          refine ⟨7838045496732311190191683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41802909315905659681022309 7838045496732311190191683)
          ·
            refine ⟨11757068245098466785287525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7838045496732311190191683 11757068245098466785287525)
            ·
              refine ⟨2204450295955962522241411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11757068245098466785287525 2204450295955962522241411)
              ·
                refine ⟨3306675443933943783362117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2204450295955962522241411 3306675443933943783362117)
                ·
                  refine ⟨620001645737614459380397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3306675443933943783362117 620001645737614459380397)
                  ·
                    refine ⟨232500617151605422267649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 620001645737614459380397 232500617151605422267649)
                    ·
                      refine ⟨174375462863704066700737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 232500617151605422267649 174375462863704066700737)
                      ·
                        rfl

theorem cell23_339595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 3, 2].length) (baseStart_339595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339595 prefixEnd_339595 := by exact prefixLift 339595
  have htrace : WordTrace (prefixWord ++ tailWord_339595) baseStart_339595 baseEnd_339595 := by
    simpa [prefixWord, tailWord_339595, baseEnd_339595] using wordTrace_append hprefix tailTrace_339595
  have hstable : (prefixWord ++ tailWord_339595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339595).length < 2 ^ (prefixWord ++ tailWord_339595).sum := by decide
  have hdescent : baseEnd_339595 < baseStart_339595 := by decide
  rcases family_descends (prefixWord ++ tailWord_339595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339628 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 3]
def baseStart_339628 : Nat := 118140960795 + 339628 * 2 ^ 59
def prefixEnd_339628 : Nat := 4983230072969 + 3 ^ 40 * 339628 * 2
def baseEnd_339628 : Nat := 174392407725302437588085

theorem tailTrace_339628 : CollatzResearch.WordTrace tailWord_339628 prefixEnd_339628 174392407725302437588085 := by
  unfold tailWord_339628
  simp only [CollatzResearch.WordTrace]
  refine ⟨6193625406796617344793769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8258167209062156459725025 6193625406796617344793769)
  ·
    refine ⟨4645219055097463008595327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6193625406796617344793769 4645219055097463008595327)
    ·
      refine ⟨6967828582646194512892991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4645219055097463008595327 6967828582646194512892991)
      ·
        refine ⟨10451742873969291769339487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6967828582646194512892991 10451742873969291769339487)
        ·
          refine ⟨15677614310953937654009231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10451742873969291769339487 15677614310953937654009231)
          ·
            refine ⟨23516421466430906481013847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15677614310953937654009231 23516421466430906481013847)
            ·
              refine ⟨35274632199646359721520771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23516421466430906481013847 35274632199646359721520771)
              ·
                refine ⟨52911948299469539582281157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35274632199646359721520771 52911948299469539582281157)
                ·
                  refine ⟨9920990306150538671677717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52911948299469539582281157 9920990306150538671677717)
                  ·
                    refine ⟨465046420600806500234893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9920990306150538671677717 465046420600806500234893)
                    ·
                      refine ⟨174392407725302437588085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 465046420600806500234893 174392407725302437588085)
                      ·
                        rfl

theorem cell23_339628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_339628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339628 prefixEnd_339628 := by exact prefixLift 339628
  have htrace : WordTrace (prefixWord ++ tailWord_339628) baseStart_339628 baseEnd_339628 := by
    simpa [prefixWord, tailWord_339628, baseEnd_339628] using wordTrace_append hprefix tailTrace_339628
  have hstable : (prefixWord ++ tailWord_339628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339628).length < 2 ^ (prefixWord ++ tailWord_339628).sum := by decide
  have hdescent : baseEnd_339628 < baseStart_339628 := by decide
  rcases family_descends (prefixWord ++ tailWord_339628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339645 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_339645 : Nat := 118140960795 + 339645 * 2 ^ 59
def prefixEnd_339645 : Nat := 4983230072969 + 3 ^ 40 * 339645 * 2
def baseEnd_339645 : Nat := 174401136896428871075507

theorem tailTrace_339645 : CollatzResearch.WordTrace tailWord_339645 prefixEnd_339645 174401136896428871075507 := by
  unfold tailWord_339645
  simp only [CollatzResearch.WordTrace]
  refine ⟨12387870854531646592956389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8258580569687764395304259 12387870854531646592956389)
  ·
    refine ⟨2322725785224683736179323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12387870854531646592956389 2322725785224683736179323)
    ·
      refine ⟨3484088677837025604268985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2322725785224683736179323 3484088677837025604268985)
      ·
        refine ⟨2613066508377769203201739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3484088677837025604268985 2613066508377769203201739)
        ·
          refine ⟨3919599762566653804802609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613066508377769203201739 3919599762566653804802609)
          ·
            refine ⟨2939699821924990353601957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3919599762566653804802609 2939699821924990353601957)
            ·
              refine ⟨551193716610935691300367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2939699821924990353601957 551193716610935691300367)
              ·
                refine ⟨826790574916403536950551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551193716610935691300367 826790574916403536950551)
                ·
                  refine ⟨1240185862374605305425827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826790574916403536950551 1240185862374605305425827)
                  ·
                    refine ⟨1860278793561907958138741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1240185862374605305425827 1860278793561907958138741)
                    ·
                      refine ⟨174401136896428871075507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1860278793561907958138741 174401136896428871075507)
                      ·
                        rfl

theorem cell23_339645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_339645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339645 prefixEnd_339645 := by exact prefixLift 339645
  have htrace : WordTrace (prefixWord ++ tailWord_339645) baseStart_339645 baseEnd_339645 := by
    simpa [prefixWord, tailWord_339645, baseEnd_339645] using wordTrace_append hprefix tailTrace_339645
  have hstable : (prefixWord ++ tailWord_339645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339645).length < 2 ^ (prefixWord ++ tailWord_339645).sum := by decide
  have hdescent : baseEnd_339645 < baseStart_339645 := by decide
  rcases family_descends (prefixWord ++ tailWord_339645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339652 : List Nat := [2, 3, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_339652 : Nat := 118140960795 + 339652 * 2 ^ 59
def prefixEnd_339652 : Nat := 4983230072969 + 3 ^ 40 * 339652 * 2
def baseEnd_339652 : Nat := 58134910420336781229325

theorem tailTrace_339652 : CollatzResearch.WordTrace tailWord_339652 prefixEnd_339652 58134910420336781229325 := by
  unfold tailWord_339652
  simp only [CollatzResearch.WordTrace]
  refine ⟨6194063082753143394230605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8258750777004191192307473 6194063082753143394230605)
  ·
    refine ⟨2322773656032428772836477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6194063082753143394230605 2322773656032428772836477)
    ·
      refine ⟨871040121012160789813679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2322773656032428772836477 871040121012160789813679)
      ·
        refine ⟨1306560181518241184720519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871040121012160789813679 1306560181518241184720519)
        ·
          refine ⟨1959840272277361777080779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306560181518241184720519 1959840272277361777080779)
          ·
            refine ⟨2939760408416042665621169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959840272277361777080779 2939760408416042665621169)
            ·
              refine ⟨2204820306312031999215877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2939760408416042665621169 2204820306312031999215877)
              ·
                refine ⟨413403807433505999852977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2204820306312031999215877 413403807433505999852977)
                ·
                  refine ⟨310052855575129499889733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413403807433505999852977 310052855575129499889733)
                  ·
                    refine ⟨58134910420336781229325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 310052855575129499889733 58134910420336781229325)
                    ·
                      rfl

theorem cell23_339652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_339652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339652 prefixEnd_339652 := by exact prefixLift 339652
  have htrace : WordTrace (prefixWord ++ tailWord_339652) baseStart_339652 baseEnd_339652 := by
    simpa [prefixWord, tailWord_339652, baseEnd_339652] using wordTrace_append hprefix tailTrace_339652
  have hstable : (prefixWord ++ tailWord_339652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339652).length < 2 ^ (prefixWord ++ tailWord_339652).sum := by decide
  have hdescent : baseEnd_339652 < baseStart_339652 := by decide
  rcases family_descends (prefixWord ++ tailWord_339652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339659 : List Nat := [1, 1, 1, 1, 3, 2, 1, 8, 1, 2, 2]
def baseStart_339659 : Nat := 118140960795 + 339659 * 2 ^ 59
def prefixEnd_339659 : Nat := 4983230072969 + 3 ^ 40 * 339659 * 2
def baseEnd_339659 : Nat := 174408325625591816300443

theorem tailTrace_339659 : CollatzResearch.WordTrace tailWord_339659 prefixEnd_339659 174408325625591816300443 := by
  unfold tailWord_339659
  simp only [CollatzResearch.WordTrace]
  refine ⟨12388381476480926983966031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8258920984320617989310687 12388381476480926983966031)
  ·
    refine ⟨18582572214721390475949047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12388381476480926983966031 18582572214721390475949047)
    ·
      refine ⟨27873858322082085713923571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18582572214721390475949047 27873858322082085713923571)
      ·
        refine ⟨41810787483123128570885357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27873858322082085713923571 41810787483123128570885357)
        ·
          refine ⟨15679045306171173214082009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41810787483123128570885357 15679045306171173214082009)
          ·
            refine ⟨11759283979628379910561507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15679045306171173214082009 11759283979628379910561507)
            ·
              refine ⟨17638925969442569865842261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11759283979628379910561507 17638925969442569865842261)
              ·
                refine ⟨206706163704405115615339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 17638925969442569865842261 206706163704405115615339)
                ·
                  refine ⟨310059245556607673423009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206706163704405115615339 310059245556607673423009)
                  ·
                    refine ⟨232544434167455755067257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 310059245556607673423009 232544434167455755067257)
                    ·
                      refine ⟨174408325625591816300443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 232544434167455755067257 174408325625591816300443)
                      ·
                        rfl

theorem cell23_339659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 1, 2, 2].length) (baseStart_339659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339659 prefixEnd_339659 := by exact prefixLift 339659
  have htrace : WordTrace (prefixWord ++ tailWord_339659) baseStart_339659 baseEnd_339659 := by
    simpa [prefixWord, tailWord_339659, baseEnd_339659] using wordTrace_append hprefix tailTrace_339659
  have hstable : (prefixWord ++ tailWord_339659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339659).length < 2 ^ (prefixWord ++ tailWord_339659).sum := by decide
  have hdescent : baseEnd_339659 < baseStart_339659 := by decide
  rcases family_descends (prefixWord ++ tailWord_339659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339676 : List Nat := [2, 2, 5, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_339676 : Nat := 118140960795 + 339676 * 2 ^ 59
def prefixEnd_339676 : Nat := 4983230072969 + 3 ^ 40 * 339676 * 2
def baseEnd_339676 : Nat := 174417054796718249787865

theorem tailTrace_339676 : CollatzResearch.WordTrace tailWord_339676 prefixEnd_339676 174417054796718249787865 := by
  unfold tailWord_339676
  simp only [CollatzResearch.WordTrace]
  refine ⟨6194500758709669443667441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8259334344946225924889921 6194500758709669443667441)
  ·
    refine ⟨4645875569032252082750581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6194500758709669443667441 4645875569032252082750581)
    ·
      refine ⟨435550834596773632757867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4645875569032252082750581 435550834596773632757867)
      ·
        refine ⟨653326251895160449136801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435550834596773632757867 653326251895160449136801)
        ·
          refine ⟨489994688921370336852601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 653326251895160449136801 489994688921370336852601)
          ·
            refine ⟨367496016691027752639451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489994688921370336852601 367496016691027752639451)
            ·
              refine ⟨551244025036541628959177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367496016691027752639451 551244025036541628959177)
              ·
                refine ⟨413433018777406221719383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551244025036541628959177 413433018777406221719383)
                ·
                  refine ⟨620149528166109332579075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 413433018777406221719383 620149528166109332579075)
                  ·
                    refine ⟨930224292249163998868613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 620149528166109332579075 930224292249163998868613)
                    ·
                      refine ⟨174417054796718249787865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 930224292249163998868613 174417054796718249787865)
                      ·
                        rfl

theorem cell23_339676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_339676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339676 prefixEnd_339676 := by exact prefixLift 339676
  have htrace : WordTrace (prefixWord ++ tailWord_339676) baseStart_339676 baseEnd_339676 := by
    simpa [prefixWord, tailWord_339676, baseEnd_339676] using wordTrace_append hprefix tailTrace_339676
  have hstable : (prefixWord ++ tailWord_339676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339676).length < 2 ^ (prefixWord ++ tailWord_339676).sum := by decide
  have hdescent : baseEnd_339676 < baseStart_339676 := by decide
  rcases family_descends (prefixWord ++ tailWord_339676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339772 : List Nat := [2, 2, 2, 2, 1, 1, 4, 4, 5]
def baseStart_339772 : Nat := 118140960795 + 339772 * 2 ^ 59
def prefixEnd_339772 : Nat := 4983230072969 + 3 ^ 40 * 339772 * 2
def baseEnd_339772 : Nat := 19385149882172208243047

theorem tailTrace_339772 : CollatzResearch.WordTrace tailWord_339772 prefixEnd_339772 19385149882172208243047 := by
  unfold tailWord_339772
  simp only [CollatzResearch.WordTrace]
  refine ⟨6196251462535773641414785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8261668616714364855219713 6196251462535773641414785)
  ·
    refine ⟨4647188596901830231061089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6196251462535773641414785 4647188596901830231061089)
    ·
      refine ⟨3485391447676372673295817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4647188596901830231061089 3485391447676372673295817)
      ·
        refine ⟨2614043585757279504971863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3485391447676372673295817 2614043585757279504971863)
        ·
          refine ⟨3921065378635919257457795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2614043585757279504971863 3921065378635919257457795)
          ·
            refine ⟨5881598067953878886186693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3921065378635919257457795 5881598067953878886186693)
            ·
              refine ⟨1102799637741352291160005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5881598067953878886186693 1102799637741352291160005)
              ·
                refine ⟨206774932076503554592501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1102799637741352291160005 206774932076503554592501)
                ·
                  refine ⟨19385149882172208243047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206774932076503554592501 19385149882172208243047)
                  ·
                    rfl

theorem cell23_339772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 5].length) (baseStart_339772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339772 prefixEnd_339772 := by exact prefixLift 339772
  have htrace : WordTrace (prefixWord ++ tailWord_339772) baseStart_339772 baseEnd_339772 := by
    simpa [prefixWord, tailWord_339772, baseEnd_339772] using wordTrace_append hprefix tailTrace_339772
  have hstable : (prefixWord ++ tailWord_339772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339772).length < 2 ^ (prefixWord ++ tailWord_339772).sum := by decide
  have hdescent : baseEnd_339772 < baseStart_339772 := by decide
  rcases family_descends (prefixWord ++ tailWord_339772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339879 : List Nat := [1, 1, 6, 1, 2, 2, 2, 2, 6]
def baseStart_339879 : Nat := 118140960795 + 339879 * 2 ^ 59
def prefixEnd_339879 : Nat := 4983230072969 + 3 ^ 40 * 339879 * 2
def baseEnd_339879 : Nat := 19391254596620106172159

theorem tailTrace_339879 : CollatzResearch.WordTrace tailWord_339879 prefixEnd_339879 19391254596620106172159 := by
  unfold tailWord_339879
  simp only [CollatzResearch.WordTrace]
  refine ⟨12396405535683904556974691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8264270357122603037983127 12396405535683904556974691)
  ·
    refine ⟨18594608303525856835462037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12396405535683904556974691 18594608303525856835462037)
    ·
      refine ⟨871622264227774539162283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18594608303525856835462037 871622264227774539162283)
      ·
        refine ⟨1307433396341661808743425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871622264227774539162283 1307433396341661808743425)
        ·
          refine ⟨980575047256246356557569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1307433396341661808743425 980575047256246356557569)
          ·
            refine ⟨735431285442184767418177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 980575047256246356557569 735431285442184767418177)
            ·
              refine ⟨551573464081638575563633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735431285442184767418177 551573464081638575563633)
              ·
                refine ⟨413680098061228931672725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551573464081638575563633 413680098061228931672725)
                ·
                  refine ⟨19391254596620106172159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 413680098061228931672725 19391254596620106172159)
                  ·
                    rfl

theorem cell23_339879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 6].length) (baseStart_339879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339879 prefixEnd_339879 := by exact prefixLift 339879
  have htrace : WordTrace (prefixWord ++ tailWord_339879) baseStart_339879 baseEnd_339879 := by
    simpa [prefixWord, tailWord_339879, baseEnd_339879] using wordTrace_append hprefix tailTrace_339879
  have hstable : (prefixWord ++ tailWord_339879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339879).length < 2 ^ (prefixWord ++ tailWord_339879).sum := by decide
  have hdescent : baseEnd_339879 < baseStart_339879 := by decide
  rcases family_descends (prefixWord ++ tailWord_339879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339916 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 2, 3, 2]
def baseStart_339916 : Nat := 118140960795 + 339916 * 2 ^ 59
def prefixEnd_339916 : Nat := 4983230072969 + 3 ^ 40 * 339916 * 2
def baseEnd_339916 : Nat := 174540290153797310786761

theorem tailTrace_339916 : CollatzResearch.WordTrace tailWord_339916 prefixEnd_339916 174540290153797310786761 := by
  unfold tailWord_339916
  simp only [CollatzResearch.WordTrace]
  refine ⟨6198877518274929938035801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8265170024366573250714401 6198877518274929938035801)
  ·
    refine ⟨4649158138706197453526851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6198877518274929938035801 4649158138706197453526851)
    ·
      refine ⟨6973737208059296180290277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4649158138706197453526851 6973737208059296180290277)
      ·
        refine ⟨1307575726511118033804427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6973737208059296180290277 1307575726511118033804427)
        ·
          refine ⟨1961363589766677050706641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1307575726511118033804427 1961363589766677050706641)
          ·
            refine ⟨1471022692325007788029981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1961363589766677050706641 1471022692325007788029981)
            ·
              refine ⟨551633509621877920511243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1471022692325007788029981 551633509621877920511243)
              ·
                refine ⟨827450264432816880766865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551633509621877920511243 827450264432816880766865)
                ·
                  refine ⟨620587698324612660575149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 827450264432816880766865 620587698324612660575149)
                  ·
                    refine ⟨232720386871729747715681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 620587698324612660575149 232720386871729747715681)
                    ·
                      refine ⟨174540290153797310786761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 232720386871729747715681 174540290153797310786761)
                      ·
                        rfl

theorem cell23_339916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_339916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339916 prefixEnd_339916 := by exact prefixLift 339916
  have htrace : WordTrace (prefixWord ++ tailWord_339916) baseStart_339916 baseEnd_339916 := by
    simpa [prefixWord, tailWord_339916, baseEnd_339916] using wordTrace_append hprefix tailTrace_339916
  have hstable : (prefixWord ++ tailWord_339916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339916).length < 2 ^ (prefixWord ++ tailWord_339916).sum := by decide
  have hdescent : baseEnd_339916 < baseStart_339916 := by decide
  rcases family_descends (prefixWord ++ tailWord_339916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339939 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 4, 4]
def baseStart_339939 : Nat := 118140960795 + 339939 * 2 ^ 59
def prefixEnd_339939 : Nat := 4983230072969 + 3 ^ 40 * 339939 * 2
def baseEnd_339939 : Nat := 58184033402950240266385

theorem tailTrace_339939 : CollatzResearch.WordTrace tailWord_339939 prefixEnd_339939 58184033402950240266385 := by
  unfold tailWord_339939
  simp only [CollatzResearch.WordTrace]
  refine ⟨12398593915466534804158871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8265729276977689869439247 12398593915466534804158871)
  ·
    refine ⟨18597890873199802206238307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12398593915466534804158871 18597890873199802206238307)
    ·
      refine ⟨27896836309799703309357461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18597890873199802206238307 27896836309799703309357461)
      ·
        refine ⟨1307664202021861092626131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27896836309799703309357461 1307664202021861092626131)
        ·
          refine ⟨1961496303032791638939197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1307664202021861092626131 1961496303032791638939197)
          ·
            refine ⟨735561113637296864602199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1961496303032791638939197 735561113637296864602199)
            ·
              refine ⟨1103341670455945296903299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735561113637296864602199 1103341670455945296903299)
              ·
                refine ⟨1655012505683917945354949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103341670455945296903299 1655012505683917945354949)
                ·
                  refine ⟨310314844815734614754053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1655012505683917945354949 310314844815734614754053)
                  ·
                    refine ⟨58184033402950240266385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 310314844815734614754053 58184033402950240266385)
                    ·
                      rfl

theorem cell23_339939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 4].length) (baseStart_339939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339939 prefixEnd_339939 := by exact prefixLift 339939
  have htrace : WordTrace (prefixWord ++ tailWord_339939) baseStart_339939 baseEnd_339939 := by
    simpa [prefixWord, tailWord_339939, baseEnd_339939] using wordTrace_append hprefix tailTrace_339939
  have hstable : (prefixWord ++ tailWord_339939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339939).length < 2 ^ (prefixWord ++ tailWord_339939).sum := by decide
  have hdescent : baseEnd_339939 < baseStart_339939 := by decide
  rcases family_descends (prefixWord ++ tailWord_339939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339979 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 6, 1, 3]
def baseStart_339979 : Nat := 118140960795 + 339979 * 2 ^ 59
def prefixEnd_339979 : Nat := 4983230072969 + 3 ^ 40 * 339979 * 2
def baseEnd_339979 : Nat := 174572639435030564298971

theorem tailTrace_339979 : CollatzResearch.WordTrace tailWord_339979 prefixEnd_339979 174572639435030564298971 := by
  unfold tailWord_339979
  simp only [CollatzResearch.WordTrace]
  refine ⟨12400052835321621635614991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8266701890214414423743327 12400052835321621635614991)
  ·
    refine ⟨18600079252982432453422487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12400052835321621635614991 18600079252982432453422487)
    ·
      refine ⟨27900118879473648680133731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18600079252982432453422487 27900118879473648680133731)
      ·
        refine ⟨41850178319210473020200597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27900118879473648680133731 41850178319210473020200597)
        ·
          refine ⟨1961727108712990922821903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41850178319210473020200597 1961727108712990922821903)
          ·
            refine ⟨2942590663069486384232855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1961727108712990922821903 2942590663069486384232855)
            ·
              refine ⟨4413885994604229576349283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2942590663069486384232855 4413885994604229576349283)
              ·
                refine ⟨6620828991906344364523925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4413885994604229576349283 6620828991906344364523925)
                ·
                  refine ⟨310351358995609892087059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6620828991906344364523925 310351358995609892087059)
                  ·
                    refine ⟨465527038493414838130589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 310351358995609892087059 465527038493414838130589)
                    ·
                      refine ⟨174572639435030564298971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 465527038493414838130589 174572639435030564298971)
                      ·
                        rfl

theorem cell23_339979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 1, 3].length) (baseStart_339979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339979 prefixEnd_339979 := by exact prefixLift 339979
  have htrace : WordTrace (prefixWord ++ tailWord_339979) baseStart_339979 baseEnd_339979 := by
    simpa [prefixWord, tailWord_339979, baseEnd_339979] using wordTrace_append hprefix tailTrace_339979
  have hstable : (prefixWord ++ tailWord_339979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339979).length < 2 ^ (prefixWord ++ tailWord_339979).sum := by decide
  have hdescent : baseEnd_339979 < baseStart_339979 := by decide
  rcases family_descends (prefixWord ++ tailWord_339979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339992 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_339992 : Nat := 118140960795 + 339992 * 2 ^ 59
def prefixEnd_339992 : Nat := 4983230072969 + 3 ^ 40 * 339992 * 2
def baseEnd_339992 : Nat := 174579314683539013436411

theorem tailTrace_339992 : CollatzResearch.WordTrace tailWord_339992 prefixEnd_339992 174579314683539013436411 := by
  unfold tailWord_339992
  simp only [CollatzResearch.WordTrace]
  refine ⟨6200263492137262427919115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8267017989516349903892153 6200263492137262427919115)
  ·
    refine ⟨9300395238205893641878673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6200263492137262427919115 9300395238205893641878673)
    ·
      refine ⟨6975296428654420231409005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9300395238205893641878673 6975296428654420231409005)
      ·
        refine ⟨2615736160745407586778377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6975296428654420231409005 2615736160745407586778377)
        ·
          refine ⟨1961802120559055690083783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2615736160745407586778377 1961802120559055690083783)
          ·
            refine ⟨2942703180838583535125675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1961802120559055690083783 2942703180838583535125675)
            ·
              refine ⟨4414054771257875302688513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2942703180838583535125675 4414054771257875302688513)
              ·
                refine ⟨3310541078443406477016385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4414054771257875302688513 3310541078443406477016385)
                ·
                  refine ⟨2482905808832554857762289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3310541078443406477016385 2482905808832554857762289)
                  ·
                    refine ⟨1862179356624416143321717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2482905808832554857762289 1862179356624416143321717)
                    ·
                      refine ⟨174579314683539013436411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1862179356624416143321717 174579314683539013436411)
                      ·
                        rfl

theorem cell23_339992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_339992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339992 prefixEnd_339992 := by exact prefixLift 339992
  have htrace : WordTrace (prefixWord ++ tailWord_339992) baseStart_339992 baseEnd_339992 := by
    simpa [prefixWord, tailWord_339992, baseEnd_339992] using wordTrace_append hprefix tailTrace_339992
  have hstable : (prefixWord ++ tailWord_339992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339992).length < 2 ^ (prefixWord ++ tailWord_339992).sum := by decide
  have hdescent : baseEnd_339992 < baseStart_339992 := by decide
  rcases family_descends (prefixWord ++ tailWord_339992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339996 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_339996 : Nat := 118140960795 + 339996 * 2 ^ 59
def prefixEnd_339996 : Nat := 4983230072969 + 3 ^ 40 * 339996 * 2
def baseEnd_339996 : Nat := 174581368606156997786393

theorem tailTrace_339996 : CollatzResearch.WordTrace tailWord_339996 prefixEnd_339996 174581368606156997786393 := by
  unfold tailWord_339996
  simp only [CollatzResearch.WordTrace]
  refine ⟨6200336438130016769491921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8267115250840022359322561 6200336438130016769491921)
  ·
    refine ⟨4650252328597512577118941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6200336438130016769491921 4650252328597512577118941)
    ·
      refine ⟨1743844623224067216419603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4650252328597512577118941 1743844623224067216419603)
      ·
        refine ⟨2615766934836100824629405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1743844623224067216419603 2615766934836100824629405)
        ·
          refine ⟨980912600563537809236027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2615766934836100824629405 980912600563537809236027)
          ·
            refine ⟨1471368900845306713854041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980912600563537809236027 1471368900845306713854041)
            ·
              refine ⟨1103526675633980035390531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1471368900845306713854041 1103526675633980035390531)
              ·
                refine ⟨1655290013450970053085797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103526675633980035390531 1655290013450970053085797)
                ·
                  refine ⟨310366877522056884953587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1655290013450970053085797 310366877522056884953587)
                  ·
                    refine ⟨465550316283085327430381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 310366877522056884953587 465550316283085327430381)
                    ·
                      refine ⟨174581368606156997786393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 465550316283085327430381 174581368606156997786393)
                      ·
                        rfl

theorem cell23_339996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_339996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339996 prefixEnd_339996 := by exact prefixLift 339996
  have htrace : WordTrace (prefixWord ++ tailWord_339996) baseStart_339996 baseEnd_339996 := by
    simpa [prefixWord, tailWord_339996, baseEnd_339996] using wordTrace_append hprefix tailTrace_339996
  have hstable : (prefixWord ++ tailWord_339996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339996).length < 2 ^ (prefixWord ++ tailWord_339996).sum := by decide
  have hdescent : baseEnd_339996 < baseStart_339996 := by decide
  rcases family_descends (prefixWord ++ tailWord_339996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339997 : List Nat := [1, 4, 2, 2, 2, 2, 3, 2, 1, 2, 2]
def baseStart_339997 : Nat := 118140960795 + 339997 * 2 ^ 59
def prefixEnd_339997 : Nat := 4983230072969 + 3 ^ 40 * 339997 * 2
def baseEnd_339997 : Nat := 174581882086811493873889

theorem tailTrace_339997 : CollatzResearch.WordTrace tailWord_339997 prefixEnd_339997 174581882086811493873889 := by
  unfold tailWord_339997
  simp only [CollatzResearch.WordTrace]
  refine ⟨12400709349256410709770245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8267139566170940473180163 12400709349256410709770245)
  ·
    refine ⟨2325133002985577008081921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12400709349256410709770245 2325133002985577008081921)
    ·
      refine ⟨1743849752239182756061441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2325133002985577008081921 1743849752239182756061441)
      ·
        refine ⟨1307887314179387067046081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1743849752239182756061441 1307887314179387067046081)
        ·
          refine ⟨980915485634540300284561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1307887314179387067046081 980915485634540300284561)
          ·
            refine ⟨735686614225905225213421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 980915485634540300284561 735686614225905225213421)
            ·
              refine ⟨275882480334714459455033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 735686614225905225213421 275882480334714459455033)
              ·
                refine ⟨206911860251035844591275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275882480334714459455033 206911860251035844591275)
                ·
                  refine ⟨310367790376553766886913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206911860251035844591275 310367790376553766886913)
                  ·
                    refine ⟨232775842782415325165185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 310367790376553766886913 232775842782415325165185)
                    ·
                      refine ⟨174581882086811493873889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 232775842782415325165185 174581882086811493873889)
                      ·
                        rfl

theorem cell23_339997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_339997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_339997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_339997 prefixEnd_339997 := by exact prefixLift 339997
  have htrace : WordTrace (prefixWord ++ tailWord_339997) baseStart_339997 baseEnd_339997 := by
    simpa [prefixWord, tailWord_339997, baseEnd_339997] using wordTrace_append hprefix tailTrace_339997
  have hstable : (prefixWord ++ tailWord_339997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339997).length < 2 ^ (prefixWord ++ tailWord_339997).sum := by decide
  have hdescent : baseEnd_339997 < baseStart_339997 := by decide
  rcases family_descends (prefixWord ++ tailWord_339997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340007 : List Nat := [1, 1, 7, 1, 3, 1, 2, 1, 2, 4]
def baseStart_340007 : Nat := 118140960795 + 340007 * 2 ^ 59
def prefixEnd_340007 : Nat := 4983230072969 + 3 ^ 40 * 340007 * 2
def baseEnd_340007 : Nat := 58195672297785484916281

theorem tailTrace_340007 : CollatzResearch.WordTrace tailWord_340007 prefixEnd_340007 58195672297785484916281 := by
  unfold tailWord_340007
  simp only [CollatzResearch.WordTrace]
  refine ⟨12401074079220182417634275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8267382719480121611756183 12401074079220182417634275)
  ·
    refine ⟨18601611118830273626451413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12401074079220182417634275 18601611118830273626451413)
    ·
      refine ⟨435975260597584538119955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 18601611118830273626451413 435975260597584538119955)
      ·
        refine ⟨653962890896376807179933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435975260597584538119955 653962890896376807179933)
        ·
          refine ⟨245236084086141302692475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 653962890896376807179933 245236084086141302692475)
          ·
            refine ⟨367854126129211954038713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245236084086141302692475 367854126129211954038713)
            ·
              refine ⟨275890594596908965529035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367854126129211954038713 275890594596908965529035)
              ·
                refine ⟨413835891895363448293553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275890594596908965529035 413835891895363448293553)
                ·
                  refine ⟨310376918921522586220165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413835891895363448293553 310376918921522586220165)
                  ·
                    refine ⟨58195672297785484916281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 310376918921522586220165 58195672297785484916281)
                    ·
                      rfl

theorem cell23_340007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_340007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340007 prefixEnd_340007 := by exact prefixLift 340007
  have htrace : WordTrace (prefixWord ++ tailWord_340007) baseStart_340007 baseEnd_340007 := by
    simpa [prefixWord, tailWord_340007, baseEnd_340007] using wordTrace_append hprefix tailTrace_340007
  have hstable : (prefixWord ++ tailWord_340007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340007).length < 2 ^ (prefixWord ++ tailWord_340007).sum := by decide
  have hdescent : baseEnd_340007 < baseStart_340007 := by decide
  rcases family_descends (prefixWord ++ tailWord_340007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340053 : List Nat := [1, 3, 2, 2, 1, 3, 1, 4, 2, 2, 2]
def baseStart_340053 : Nat := 118140960795 + 340053 * 2 ^ 59
def prefixEnd_340053 : Nat := 4983230072969 + 3 ^ 40 * 340053 * 2
def baseEnd_340053 : Nat := 174610637003463274773631

theorem tailTrace_340053 : CollatzResearch.WordTrace tailWord_340053 prefixEnd_340053 174610637003463274773631 := by
  unfold tailWord_340053
  simp only [CollatzResearch.WordTrace]
  refine ⟨12402751837053532273808813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8268501224702354849205875 12402751837053532273808813)
  ·
    refine ⟨4651031938895074602678305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12402751837053532273808813 4651031938895074602678305)
    ·
      refine ⟨3488273954171305952008729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4651031938895074602678305 3488273954171305952008729)
      ·
        refine ⟨2616205465628479464006547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3488273954171305952008729 2616205465628479464006547)
        ·
          refine ⟨3924308198442719196009821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2616205465628479464006547 3924308198442719196009821)
          ·
            refine ⟨1471615574416019698503683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3924308198442719196009821 1471615574416019698503683)
            ·
              refine ⟨2207423361624029547755525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471615574416019698503683 2207423361624029547755525)
              ·
                refine ⟨413891880304505540204161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2207423361624029547755525 413891880304505540204161)
                ·
                  refine ⟨310418910228379155153121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413891880304505540204161 310418910228379155153121)
                  ·
                    refine ⟨232814182671284366364841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 310418910228379155153121 232814182671284366364841)
                    ·
                      refine ⟨174610637003463274773631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 232814182671284366364841 174610637003463274773631)
                      ·
                        rfl

theorem cell23_340053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_340053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340053 prefixEnd_340053 := by exact prefixLift 340053
  have htrace : WordTrace (prefixWord ++ tailWord_340053) baseStart_340053 baseEnd_340053 := by
    simpa [prefixWord, tailWord_340053, baseEnd_340053] using wordTrace_append hprefix tailTrace_340053
  have hstable : (prefixWord ++ tailWord_340053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340053).length < 2 ^ (prefixWord ++ tailWord_340053).sum := by decide
  have hdescent : baseEnd_340053 < baseStart_340053 := by decide
  rcases family_descends (prefixWord ++ tailWord_340053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340069 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 1, 5, 3]
def baseStart_340069 : Nat := 118140960795 + 340069 * 2 ^ 59
def prefixEnd_340069 : Nat := 4983230072969 + 3 ^ 40 * 340069 * 2
def baseEnd_340069 : Nat := 174618852693935212173557

theorem tailTrace_340069 : CollatzResearch.WordTrace tailWord_340069 prefixEnd_340069 174618852693935212173557 := by
  unfold tailWord_340069
  simp only [CollatzResearch.WordTrace]
  refine ⟨12403335404995567006391261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8268890269997044670927507 12403335404995567006391261)
  ·
    refine ⟨4651250776873337627396723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12403335404995567006391261 4651250776873337627396723)
    ·
      refine ⟨6976876165310006441095085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4651250776873337627396723 6976876165310006441095085)
      ·
        refine ⟨2616328561991252415410657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6976876165310006441095085 2616328561991252415410657)
        ·
          refine ⟨1962246421493439311557993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2616328561991252415410657 1962246421493439311557993)
          ·
            refine ⟨1471684816120079483668495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1962246421493439311557993 1471684816120079483668495)
            ·
              refine ⟨2207527224180119225502743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471684816120079483668495 2207527224180119225502743)
              ·
                refine ⟨3311290836270178838254115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207527224180119225502743 3311290836270178838254115)
                ·
                  refine ⟨4966936254405268257381173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3311290836270178838254115 4966936254405268257381173)
                  ·
                    refine ⟨465650273850493899129485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4966936254405268257381173 465650273850493899129485)
                    ·
                      refine ⟨174618852693935212173557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 465650273850493899129485 174618852693935212173557)
                      ·
                        rfl

theorem cell23_340069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_340069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340069 prefixEnd_340069 := by exact prefixLift 340069
  have htrace : WordTrace (prefixWord ++ tailWord_340069) baseStart_340069 baseEnd_340069 := by
    simpa [prefixWord, tailWord_340069, baseEnd_340069] using wordTrace_append hprefix tailTrace_340069
  have hstable : (prefixWord ++ tailWord_340069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340069).length < 2 ^ (prefixWord ++ tailWord_340069).sum := by decide
  have hdescent : baseEnd_340069 < baseStart_340069 := by decide
  rcases family_descends (prefixWord ++ tailWord_340069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340089 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 1, 7]
def baseStart_340089 : Nat := 118140960795 + 340089 * 2 ^ 59
def prefixEnd_340089 : Nat := 4983230072969 + 3 ^ 40 * 340089 * 2
def baseEnd_340089 : Nat := 58209707435675044641155

theorem tailTrace_340089 : CollatzResearch.WordTrace tailWord_340089 prefixEnd_340089 58209707435675044641155 := by
  unfold tailWord_340089
  simp only [CollatzResearch.WordTrace]
  refine ⟨12404064864923110422119321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8269376576615406948079547 12404064864923110422119321)
  ·
    refine ⟨9303048648692332816589491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12404064864923110422119321 9303048648692332816589491)
    ·
      refine ⟨13954572973038499224884237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9303048648692332816589491 13954572973038499224884237)
      ·
        refine ⟨5232964864889437209331589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13954572973038499224884237 5232964864889437209331589)
        ·
          refine ⟨981180912166769476749673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5232964864889437209331589 981180912166769476749673)
          ·
            refine ⟨735885684125077107562255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 981180912166769476749673 735885684125077107562255)
            ·
              refine ⟨1103828526187615661343383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735885684125077107562255 1103828526187615661343383)
              ·
                refine ⟨1655742789281423492015075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1103828526187615661343383 1655742789281423492015075)
                ·
                  refine ⟨2483614183922135238022613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655742789281423492015075 2483614183922135238022613)
                  ·
                    refine ⟨58209707435675044641155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2483614183922135238022613 58209707435675044641155)
                    ·
                      rfl

theorem cell23_340089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 7].length) (baseStart_340089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340089 prefixEnd_340089 := by exact prefixLift 340089
  have htrace : WordTrace (prefixWord ++ tailWord_340089) baseStart_340089 baseEnd_340089 := by
    simpa [prefixWord, tailWord_340089, baseEnd_340089] using wordTrace_append hprefix tailTrace_340089
  have hstable : (prefixWord ++ tailWord_340089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340089).length < 2 ^ (prefixWord ++ tailWord_340089).sum := by decide
  have hdescent : baseEnd_340089 < baseStart_340089 := by decide
  rcases family_descends (prefixWord ++ tailWord_340089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340146 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_340146 : Nat := 118140960795 + 340146 * 2 ^ 59
def prefixEnd_340146 : Nat := 4983230072969 + 3 ^ 40 * 340146 * 2
def baseEnd_340146 : Nat := 174658390704331410910703

theorem tailTrace_340146 : CollatzResearch.WordTrace tailWord_340146 prefixEnd_340146 174658390704331410910703 := by
  unfold tailWord_340146
  simp only [CollatzResearch.WordTrace]
  refine ⟨3101535956429152289236073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8270762550477739437962861 3101535956429152289236073)
  ·
    refine ⟨2326151967321864216927055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3101535956429152289236073 2326151967321864216927055)
    ·
      refine ⟨3489227950982796325390583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2326151967321864216927055 3489227950982796325390583)
      ·
        refine ⟨5233841926474194488085875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3489227950982796325390583 5233841926474194488085875)
        ·
          refine ⟨7850762889711291732128813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5233841926474194488085875 7850762889711291732128813)
          ·
            refine ⟨2944036083641734399548305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7850762889711291732128813 2944036083641734399548305)
            ·
              refine ⟨2208027062731300799661229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2944036083641734399548305 2208027062731300799661229)
              ·
                refine ⟨828010148524237799872961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2208027062731300799661229 828010148524237799872961)
                ·
                  refine ⟨621007611393178349904721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 828010148524237799872961 621007611393178349904721)
                  ·
                    refine ⟨465755708544883762428541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 621007611393178349904721 465755708544883762428541)
                    ·
                      refine ⟨174658390704331410910703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 465755708544883762428541 174658390704331410910703)
                      ·
                        rfl

theorem cell23_340146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_340146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340146 prefixEnd_340146 := by exact prefixLift 340146
  have htrace : WordTrace (prefixWord ++ tailWord_340146) baseStart_340146 baseEnd_340146 := by
    simpa [prefixWord, tailWord_340146, baseEnd_340146] using wordTrace_append hprefix tailTrace_340146
  have hstable : (prefixWord ++ tailWord_340146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340146).length < 2 ^ (prefixWord ++ tailWord_340146).sum := by decide
  have hdescent : baseEnd_340146 < baseStart_340146 := by decide
  rcases family_descends (prefixWord ++ tailWord_340146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340170 : List Nat := [3, 1, 2, 1, 3, 1, 5, 2, 1, 4]
def baseStart_340170 : Nat := 118140960795 + 340170 * 2 ^ 59
def prefixEnd_340170 : Nat := 4983230072969 + 3 ^ 40 * 340170 * 2
def baseEnd_340170 : Nat := 58223571413346439003531

theorem tailTrace_340170 : CollatzResearch.WordTrace tailWord_340170 prefixEnd_340170 58223571413346439003531 := by
  unfold tailWord_340170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3101754794407415313954491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8271346118419774170545309 3101754794407415313954491)
  ·
    refine ⟨4652632191611122970931737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3101754794407415313954491 4652632191611122970931737)
    ·
      refine ⟨3489474143708342228198803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4652632191611122970931737 3489474143708342228198803)
      ·
        refine ⟨5234211215562513342298205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3489474143708342228198803 5234211215562513342298205)
        ·
          refine ⟨1962829205835942503361827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5234211215562513342298205 1962829205835942503361827)
          ·
            refine ⟨2944243808753913755042741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962829205835942503361827 2944243808753913755042741)
            ·
              refine ⟨276022857070679414535257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2944243808753913755042741 276022857070679414535257)
              ·
                refine ⟨207017142803009560901443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276022857070679414535257 207017142803009560901443)
                ·
                  refine ⟨310525714204514341352165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207017142803009560901443 310525714204514341352165)
                  ·
                    refine ⟨58223571413346439003531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 310525714204514341352165 58223571413346439003531)
                    ·
                      rfl

theorem cell23_340170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_340170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340170 prefixEnd_340170 := by exact prefixLift 340170
  have htrace : WordTrace (prefixWord ++ tailWord_340170) baseStart_340170 baseEnd_340170 := by
    simpa [prefixWord, tailWord_340170, baseEnd_340170] using wordTrace_append hprefix tailTrace_340170
  have hstable : (prefixWord ++ tailWord_340170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340170).length < 2 ^ (prefixWord ++ tailWord_340170).sum := by decide
  have hdescent : baseEnd_340170 < baseStart_340170 := by decide
  rcases family_descends (prefixWord ++ tailWord_340170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340186 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2]
def baseStart_340186 : Nat := 118140960795 + 340186 * 2 ^ 59
def prefixEnd_340186 : Nat := 4983230072969 + 3 ^ 40 * 340186 * 2
def baseEnd_340186 : Nat := 174678929930511254410519

theorem tailTrace_340186 : CollatzResearch.WordTrace tailWord_340186 prefixEnd_340186 174678929930511254410519 := by
  unfold tailWord_340186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3101900686392923997100103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8271735163714463992266941 3101900686392923997100103)
  ·
    refine ⟨4652851029589385995650155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3101900686392923997100103 4652851029589385995650155)
    ·
      refine ⟨6979276544384078993475233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4652851029589385995650155 6979276544384078993475233)
      ·
        refine ⟨5234457408288059245106425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6979276544384078993475233 5234457408288059245106425)
        ·
          refine ⟨3925843056216044433829819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5234457408288059245106425 3925843056216044433829819)
          ·
            refine ⟨5888764584324066650744729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925843056216044433829819 5888764584324066650744729)
            ·
              refine ⟨4416573438243049988058547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5888764584324066650744729 4416573438243049988058547)
              ·
                refine ⟨6624860157364574982087821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4416573438243049988058547 6624860157364574982087821)
                ·
                  refine ⟨2484322559011715618282933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6624860157364574982087821 2484322559011715618282933)
                  ·
                    refine ⟨232905239907348339214025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2484322559011715618282933 232905239907348339214025)
                    ·
                      refine ⟨174678929930511254410519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 232905239907348339214025 174678929930511254410519)
                      ·
                        rfl

theorem cell23_340186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_340186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340186 prefixEnd_340186 := by exact prefixLift 340186
  have htrace : WordTrace (prefixWord ++ tailWord_340186) baseStart_340186 baseEnd_340186 := by
    simpa [prefixWord, tailWord_340186, baseEnd_340186] using wordTrace_append hprefix tailTrace_340186
  have hstable : (prefixWord ++ tailWord_340186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340186).length < 2 ^ (prefixWord ++ tailWord_340186).sum := by decide
  have hdescent : baseEnd_340186 < baseStart_340186 := by decide
  rcases family_descends (prefixWord ++ tailWord_340186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340203 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 2, 3, 2]
def baseStart_340203 : Nat := 118140960795 + 340203 * 2 ^ 59
def prefixEnd_340203 : Nat := 4983230072969 + 3 ^ 40 * 340203 * 2
def baseEnd_340203 : Nat := 174687659101637687897941

theorem tailTrace_340203 : CollatzResearch.WordTrace tailWord_340203 prefixEnd_340203 174687659101637687897941 := by
  unfold tailWord_340203
  simp only [CollatzResearch.WordTrace]
  refine ⟨12408222786510107891769263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8272148524340071927846175 12408222786510107891769263)
  ·
    refine ⟨18612334179765161837653895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12408222786510107891769263 18612334179765161837653895)
    ·
      refine ⟨27918501269647742756480843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18612334179765161837653895 27918501269647742756480843)
      ·
        refine ⟨41877751904471614134721265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27918501269647742756480843 41877751904471614134721265)
        ·
          refine ⟨31408313928353710601040949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41877751904471614134721265 31408313928353710601040949)
          ·
            refine ⟨2944529430783160368847589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31408313928353710601040949 2944529430783160368847589)
            ·
              refine ⟨552099268271842569158923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2944529430783160368847589 552099268271842569158923)
              ·
                refine ⟨828148902407763853738385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552099268271842569158923 828148902407763853738385)
                ·
                  refine ⟨621111676805822890303789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 828148902407763853738385 621111676805822890303789)
                  ·
                    refine ⟨232916878802183583863921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621111676805822890303789 232916878802183583863921)
                    ·
                      refine ⟨174687659101637687897941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 232916878802183583863921 174687659101637687897941)
                      ·
                        rfl

theorem cell23_340203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 3, 2].length) (baseStart_340203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340203 prefixEnd_340203 := by exact prefixLift 340203
  have htrace : WordTrace (prefixWord ++ tailWord_340203) baseStart_340203 baseEnd_340203 := by
    simpa [prefixWord, tailWord_340203, baseEnd_340203] using wordTrace_append hprefix tailTrace_340203
  have hstable : (prefixWord ++ tailWord_340203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340203).length < 2 ^ (prefixWord ++ tailWord_340203).sum := by decide
  have hdescent : baseEnd_340203 < baseStart_340203 := by decide
  rcases family_descends (prefixWord ++ tailWord_340203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340209 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 3, 6]
def baseStart_340209 : Nat := 118140960795 + 340209 * 2 ^ 59
def prefixEnd_340209 : Nat := 4983230072969 + 3 ^ 40 * 340209 * 2
def baseEnd_340209 : Nat := 58230246661854888140971

theorem tailTrace_340209 : CollatzResearch.WordTrace tailWord_340209 prefixEnd_340209 58230246661854888140971 := by
  unfold tailWord_340209
  simp only [CollatzResearch.WordTrace]
  refine ⟨12408441624488370916487681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8272294416325580610991787 12408441624488370916487681)
  ·
    refine ⟨9306331218366278187365761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12408441624488370916487681 9306331218366278187365761)
    ·
      refine ⟨6979748413774708640524321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9306331218366278187365761 6979748413774708640524321)
      ·
        refine ⟨5234811310331031480393241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6979748413774708640524321 5234811310331031480393241)
        ·
          refine ⟨3926108482748273610294931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5234811310331031480393241 3926108482748273610294931)
          ·
            refine ⟨5889162724122410415442397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926108482748273610294931 5889162724122410415442397)
            ·
              refine ⟨2208436021545903905790899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5889162724122410415442397 2208436021545903905790899)
              ·
                refine ⟨3312654032318855858686349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2208436021545903905790899 3312654032318855858686349)
                ·
                  refine ⟨1242245262119570947007381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3312654032318855858686349 1242245262119570947007381)
                  ·
                    refine ⟨58230246661854888140971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1242245262119570947007381 58230246661854888140971)
                    ·
                      rfl

theorem cell23_340209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_340209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340209 prefixEnd_340209 := by exact prefixLift 340209
  have htrace : WordTrace (prefixWord ++ tailWord_340209) baseStart_340209 baseEnd_340209 := by
    simpa [prefixWord, tailWord_340209, baseEnd_340209] using wordTrace_append hprefix tailTrace_340209
  have hstable : (prefixWord ++ tailWord_340209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340209).length < 2 ^ (prefixWord ++ tailWord_340209).sum := by decide
  have hdescent : baseEnd_340209 < baseStart_340209 := by decide
  rcases family_descends (prefixWord ++ tailWord_340209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340216 : List Nat := [2, 1, 2, 1, 1, 2, 1, 7, 1, 1, 4]
def baseStart_340216 : Nat := 118140960795 + 340216 * 2 ^ 59
def prefixEnd_340216 : Nat := 4983230072969 + 3 ^ 40 * 340216 * 2
def baseEnd_340216 : Nat := 174694334350146137035381

theorem tailTrace_340216 : CollatzResearch.WordTrace tailWord_340216 prefixEnd_340216 174694334350146137035381 := by
  unfold tailWord_340216
  simp only [CollatzResearch.WordTrace]
  refine ⟨6204348467731505555996251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8272464623642007407995001 6204348467731505555996251)
  ·
    refine ⟨9306522701597258333994377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6204348467731505555996251 9306522701597258333994377)
    ·
      refine ⟨6979892026197943750495783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9306522701597258333994377 6979892026197943750495783)
      ·
        refine ⟨10469838039296915625743675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6979892026197943750495783 10469838039296915625743675)
        ·
          refine ⟨15704757058945373438615513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10469838039296915625743675 15704757058945373438615513)
          ·
            refine ⟨11778567794209030078961635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15704757058945373438615513 11778567794209030078961635)
            ·
              refine ⟨17667851691313545118442453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11778567794209030078961635 17667851691313545118442453)
              ·
                refine ⟨414090274015161213713495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17667851691313545118442453 414090274015161213713495)
                ·
                  refine ⟨621135411022741820570243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414090274015161213713495 621135411022741820570243)
                  ·
                    refine ⟨931703116534112730855365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 621135411022741820570243 931703116534112730855365)
                    ·
                      refine ⟨174694334350146137035381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 931703116534112730855365 174694334350146137035381)
                      ·
                        rfl

theorem cell23_340216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_340216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340216 prefixEnd_340216 := by exact prefixLift 340216
  have htrace : WordTrace (prefixWord ++ tailWord_340216) baseStart_340216 baseEnd_340216 := by
    simpa [prefixWord, tailWord_340216, baseEnd_340216] using wordTrace_append hprefix tailTrace_340216
  have hstable : (prefixWord ++ tailWord_340216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340216).length < 2 ^ (prefixWord ++ tailWord_340216).sum := by decide
  have hdescent : baseEnd_340216 < baseStart_340216 := by decide
  rcases family_descends (prefixWord ++ tailWord_340216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340229 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_340229 : Nat := 118140960795 + 340229 * 2 ^ 59
def prefixEnd_340229 : Nat := 4983230072969 + 3 ^ 40 * 340229 * 2
def baseEnd_340229 : Nat := 174701009598654586172821

theorem tailTrace_340229 : CollatzResearch.WordTrace tailWord_340229 prefixEnd_340229 174701009598654586172821 := by
  unfold tailWord_340229
  simp only [CollatzResearch.WordTrace]
  refine ⟨12409171084415914332215741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8272780722943942888143827 12409171084415914332215741)
  ·
    refine ⟨4653439156655967874580903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12409171084415914332215741 4653439156655967874580903)
    ·
      refine ⟨6980158734983951811871355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4653439156655967874580903 6980158734983951811871355)
      ·
        refine ⟨10470238102475927717807033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6980158734983951811871355 10470238102475927717807033)
        ·
          refine ⟨7852678576856945788355275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10470238102475927717807033 7852678576856945788355275)
          ·
            refine ⟨11779017865285418682532913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7852678576856945788355275 11779017865285418682532913)
            ·
              refine ⟨8834263398964064011899685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11779017865285418682532913 8834263398964064011899685)
              ·
                refine ⟨1656424387305762002231191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8834263398964064011899685 1656424387305762002231191)
                ·
                  refine ⟨2484636580958643003346787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656424387305762002231191 2484636580958643003346787)
                  ·
                    refine ⟨3726954871437964505020181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2484636580958643003346787 3726954871437964505020181)
                    ·
                      refine ⟨174701009598654586172821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3726954871437964505020181 174701009598654586172821)
                      ·
                        rfl

theorem cell23_340229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_340229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340229 prefixEnd_340229 := by exact prefixLift 340229
  have htrace : WordTrace (prefixWord ++ tailWord_340229) baseStart_340229 baseEnd_340229 := by
    simpa [prefixWord, tailWord_340229, baseEnd_340229] using wordTrace_append hprefix tailTrace_340229
  have hstable : (prefixWord ++ tailWord_340229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340229).length < 2 ^ (prefixWord ++ tailWord_340229).sum := by decide
  have hdescent : baseEnd_340229 < baseStart_340229 := by decide
  rcases family_descends (prefixWord ++ tailWord_340229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340236 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 5, 2, 3]
def baseStart_340236 : Nat := 118140960795 + 340236 * 2 ^ 59
def prefixEnd_340236 : Nat := 4983230072969 + 3 ^ 40 * 340236 * 2
def baseEnd_340236 : Nat := 174704603963236058785289

theorem tailTrace_340236 : CollatzResearch.WordTrace tailWord_340236 prefixEnd_340236 174704603963236058785289 := by
  unfold tailWord_340236
  simp only [CollatzResearch.WordTrace]
  refine ⟨6204713197695277263860281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8272950930260369685147041 6204713197695277263860281)
  ·
    refine ⟨4653534898271457947895211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6204713197695277263860281 4653534898271457947895211)
    ·
      refine ⟨6980302347407186921842817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4653534898271457947895211 6980302347407186921842817)
      ·
        refine ⟨5235226760555390191382113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6980302347407186921842817 5235226760555390191382113)
        ·
          refine ⟨3926420070416542643536585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5235226760555390191382113 3926420070416542643536585)
          ·
            refine ⟨2944815052812406982652439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3926420070416542643536585 2944815052812406982652439)
            ·
              refine ⟨4417222579218610473978659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2944815052812406982652439 4417222579218610473978659)
              ·
                refine ⟨6625833868827915710967989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4417222579218610473978659 6625833868827915710967989)
                ·
                  refine ⟨621171925202617097903249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6625833868827915710967989 621171925202617097903249)
                  ·
                    refine ⟨465878943901962823427437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 621171925202617097903249 465878943901962823427437)
                    ·
                      refine ⟨174704603963236058785289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 465878943901962823427437 174704603963236058785289)
                      ·
                        rfl

theorem cell23_340236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_340236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340236 prefixEnd_340236 := by exact prefixLift 340236
  have htrace : WordTrace (prefixWord ++ tailWord_340236) baseStart_340236 baseEnd_340236 := by
    simpa [prefixWord, tailWord_340236, baseEnd_340236] using wordTrace_append hprefix tailTrace_340236
  have hstable : (prefixWord ++ tailWord_340236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340236).length < 2 ^ (prefixWord ++ tailWord_340236).sum := by decide
  have hdescent : baseEnd_340236 < baseStart_340236 := by decide
  rcases family_descends (prefixWord ++ tailWord_340236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340254 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_340254 : Nat := 118140960795 + 340254 * 2 ^ 59
def prefixEnd_340254 : Nat := 4983230072969 + 3 ^ 40 * 340254 * 2
def baseEnd_340254 : Nat := 174713846615016988360207

theorem tailTrace_340254 : CollatzResearch.WordTrace tailWord_340254 prefixEnd_340254 174713846615016988360207 := by
  unfold tailWord_340254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1551260363665667950234477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8273388606216895734583877 1551260363665667950234477)
  ·
    refine ⟨581722636374625481337929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1551260363665667950234477 581722636374625481337929)
    ·
      refine ⟨436291977280969111003447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 581722636374625481337929 436291977280969111003447)
      ·
        refine ⟨654437965921453666505171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436291977280969111003447 654437965921453666505171)
        ·
          refine ⟨981656948882180499757757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654437965921453666505171 981656948882180499757757)
          ·
            refine ⟨368121355830817687409159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 981656948882180499757757 368121355830817687409159)
            ·
              refine ⟨552182033746226531113739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368121355830817687409159 552182033746226531113739)
              ·
                refine ⟨828273050619339796670609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552182033746226531113739 828273050619339796670609)
                ·
                  refine ⟨621204787964504847502957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 828273050619339796670609 621204787964504847502957)
                  ·
                    refine ⟨232951795486689317813609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 621204787964504847502957 232951795486689317813609)
                    ·
                      refine ⟨174713846615016988360207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 232951795486689317813609 174713846615016988360207)
                      ·
                        rfl

theorem cell23_340254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_340254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340254 prefixEnd_340254 := by exact prefixLift 340254
  have htrace : WordTrace (prefixWord ++ tailWord_340254) baseStart_340254 baseEnd_340254 := by
    simpa [prefixWord, tailWord_340254, baseEnd_340254] using wordTrace_append hprefix tailTrace_340254
  have hstable : (prefixWord ++ tailWord_340254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340254).length < 2 ^ (prefixWord ++ tailWord_340254).sum := by decide
  have hdescent : baseEnd_340254 < baseStart_340254 := by decide
  rcases family_descends (prefixWord ++ tailWord_340254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340299 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 1, 8]
def baseStart_340299 : Nat := 118140960795 + 340299 * 2 ^ 59
def prefixEnd_340299 : Nat := 4983230072969 + 3 ^ 40 * 340299 * 2
def baseEnd_340299 : Nat := 58245651081489770765833

theorem tailTrace_340299 : CollatzResearch.WordTrace tailWord_340299 prefixEnd_340299 58245651081489770765833 := by
  unfold tailWord_340299
  simp only [CollatzResearch.WordTrace]
  refine ⟨12411724194162316287263951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8274482796108210858175967 12411724194162316287263951)
  ·
    refine ⟨18617586291243474430895927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12411724194162316287263951 18617586291243474430895927)
    ·
      refine ⟨27926379436865211646343891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18617586291243474430895927 27926379436865211646343891)
      ·
        refine ⟨41889569155297817469515837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27926379436865211646343891 41889569155297817469515837)
        ·
          refine ⟨15708588433236681551068439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41889569155297817469515837 15708588433236681551068439)
          ·
            refine ⟨23562882649855022326602659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15708588433236681551068439 23562882649855022326602659)
            ·
              refine ⟨35344323974782533489903989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23562882649855022326602659 35344323974782533489903989)
              ·
                refine ⟨3313530372635862514678499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35344323974782533489903989 3313530372635862514678499)
                ·
                  refine ⟨4970295558953793772017749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3313530372635862514678499 4970295558953793772017749)
                  ·
                    refine ⟨58245651081489770765833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4970295558953793772017749 58245651081489770765833)
                    ·
                      rfl

theorem cell23_340299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 8].length) (baseStart_340299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340299 prefixEnd_340299 := by exact prefixLift 340299
  have htrace : WordTrace (prefixWord ++ tailWord_340299) baseStart_340299 baseEnd_340299 := by
    simpa [prefixWord, tailWord_340299, baseEnd_340299] using wordTrace_append hprefix tailTrace_340299
  have hstable : (prefixWord ++ tailWord_340299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340299).length < 2 ^ (prefixWord ++ tailWord_340299).sum := by decide
  have hdescent : baseEnd_340299 < baseStart_340299 := by decide
  rcases family_descends (prefixWord ++ tailWord_340299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340306 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_340306 : Nat := 118140960795 + 340306 * 2 ^ 59
def prefixEnd_340306 : Nat := 4983230072969 + 3 ^ 40 * 340306 * 2
def baseEnd_340306 : Nat := 174740547609050784909967

theorem tailTrace_340306 : CollatzResearch.WordTrace tailWord_340306 prefixEnd_340306 174740547609050784909967 := by
  unfold tailWord_340306
  simp only [CollatzResearch.WordTrace]
  refine ⟨3102994876284239120692193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8274653003424637655179181 3102994876284239120692193)
  ·
    refine ⟨2327246157213179340519145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3102994876284239120692193 2327246157213179340519145)
    ·
      refine ⟨1745434617909884505389359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2327246157213179340519145 1745434617909884505389359)
      ·
        refine ⟨2618151926864826758084039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1745434617909884505389359 2618151926864826758084039)
        ·
          refine ⟨3927227890297240137126059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2618151926864826758084039 3927227890297240137126059)
          ·
            refine ⟨5890841835445860205689089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927227890297240137126059 5890841835445860205689089)
            ·
              refine ⟨4418131376584395154266817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5890841835445860205689089 4418131376584395154266817)
              ·
                refine ⟨3313598532438296365700113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4418131376584395154266817 3313598532438296365700113)
                ·
                  refine ⟨2485198899328722274275085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3313598532438296365700113 2485198899328722274275085)
                  ·
                    refine ⟨931949587248270852853157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2485198899328722274275085 931949587248270852853157)
                    ·
                      refine ⟨174740547609050784909967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 931949587248270852853157 174740547609050784909967)
                      ·
                        rfl

theorem cell23_340306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_340306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340306 prefixEnd_340306 := by exact prefixLift 340306
  have htrace : WordTrace (prefixWord ++ tailWord_340306) baseStart_340306 baseEnd_340306 := by
    simpa [prefixWord, tailWord_340306, baseEnd_340306] using wordTrace_append hprefix tailTrace_340306
  have hstable : (prefixWord ++ tailWord_340306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340306).length < 2 ^ (prefixWord ++ tailWord_340306).sum := by decide
  have hdescent : baseEnd_340306 < baseStart_340306 := by decide
  rcases family_descends (prefixWord ++ tailWord_340306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340323 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 3, 4, 2]
def baseStart_340323 : Nat := 118140960795 + 340323 * 2 ^ 59
def prefixEnd_340323 : Nat := 4983230072969 + 3 ^ 40 * 340323 * 2
def baseEnd_340323 : Nat := 174749276780177218397389

theorem tailTrace_340323 : CollatzResearch.WordTrace tailWord_340323 prefixEnd_340323 174749276780177218397389 := by
  unfold tailWord_340323
  simp only [CollatzResearch.WordTrace]
  refine ⟨12412599546075368386137623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8275066364050245590758415 12412599546075368386137623)
  ·
    refine ⟨18618899319113052579206435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12412599546075368386137623 18618899319113052579206435)
    ·
      refine ⟨27928348978669578868809653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18618899319113052579206435 27928348978669578868809653)
      ·
        refine ⟨2618282716750273018950905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27928348978669578868809653 2618282716750273018950905)
        ·
          refine ⟨1963712037562704764213179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2618282716750273018950905 1963712037562704764213179)
          ·
            refine ⟨2945568056344057146319769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963712037562704764213179 2945568056344057146319769)
            ·
              refine ⟨2209176042258042859739827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2945568056344057146319769 2209176042258042859739827)
              ·
                refine ⟨3313764063387064289609741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2209176042258042859739827 3313764063387064289609741)
                ·
                  refine ⟨1242661523770149108603653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3313764063387064289609741 1242661523770149108603653)
                  ·
                    refine ⟨232999035706902957863185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1242661523770149108603653 232999035706902957863185)
                    ·
                      refine ⟨174749276780177218397389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 232999035706902957863185 174749276780177218397389)
                      ·
                        rfl

theorem cell23_340323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_340323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340323 prefixEnd_340323 := by exact prefixLift 340323
  have htrace : WordTrace (prefixWord ++ tailWord_340323) baseStart_340323 baseEnd_340323 := by
    simpa [prefixWord, tailWord_340323, baseEnd_340323] using wordTrace_append hprefix tailTrace_340323
  have hstable : (prefixWord ++ tailWord_340323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340323).length < 2 ^ (prefixWord ++ tailWord_340323).sum := by decide
  have hdescent : baseEnd_340323 < baseStart_340323 := by decide
  rcases family_descends (prefixWord ++ tailWord_340323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340396 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_340396 : Nat := 118140960795 + 340396 * 2 ^ 59
def prefixEnd_340396 : Nat := 4983230072969 + 3 ^ 40 * 340396 * 2
def baseEnd_340396 : Nat := 174786760867955432784553

theorem tailTrace_340396 : CollatzResearch.WordTrace tailWord_340396 prefixEnd_340396 174786760867955432784553 := by
  unfold tailWord_340396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6207631037405450926772521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8276841383207267902363361 6207631037405450926772521)
  ·
    refine ⟨4655723278054088195079391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6207631037405450926772521 4655723278054088195079391)
    ·
      refine ⟨6983584917081132292619087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4655723278054088195079391 6983584917081132292619087)
      ·
        refine ⟨10475377375621698438928631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6983584917081132292619087 10475377375621698438928631)
        ·
          refine ⟨15713066063432547658392947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10475377375621698438928631 15713066063432547658392947)
          ·
            refine ⟨23569599095148821487589421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15713066063432547658392947 23569599095148821487589421)
            ·
              refine ⟨8838599660680808057846033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23569599095148821487589421 8838599660680808057846033)
              ·
                refine ⟨6628949745510606043384525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8838599660680808057846033 6628949745510606043384525)
                ·
                  refine ⟨2485856154566477266269197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6628949745510606043384525 2485856154566477266269197)
                  ·
                    refine ⟨932196057962428974850949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2485856154566477266269197 932196057962428974850949)
                    ·
                      refine ⟨174786760867955432784553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 932196057962428974850949 174786760867955432784553)
                      ·
                        rfl

theorem cell23_340396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_340396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340396 prefixEnd_340396 := by exact prefixLift 340396
  have htrace : WordTrace (prefixWord ++ tailWord_340396) baseStart_340396 baseEnd_340396 := by
    simpa [prefixWord, tailWord_340396, baseEnd_340396] using wordTrace_append hprefix tailTrace_340396
  have hstable : (prefixWord ++ tailWord_340396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340396).length < 2 ^ (prefixWord ++ tailWord_340396).sum := by decide
  have hdescent : baseEnd_340396 < baseStart_340396 := by decide
  rcases family_descends (prefixWord ++ tailWord_340396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340397 : List Nat := [1, 5, 2, 2, 2, 1, 1, 4, 5]
def baseStart_340397 : Nat := 118140960795 + 340397 * 2 ^ 59
def prefixEnd_340397 : Nat := 4983230072969 + 3 ^ 40 * 340397 * 2
def baseEnd_340397 : Nat := 19420808260956658763561

theorem tailTrace_340397 : CollatzResearch.WordTrace tailWord_340397 prefixEnd_340397 19420808260956658763561 := by
  unfold tailWord_340397
  simp only [CollatzResearch.WordTrace]
  refine ⟨12415298547807279024331445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8276865698538186016220963 12415298547807279024331445)
  ·
    refine ⟨1163934238856932408531073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12415298547807279024331445 1163934238856932408531073)
    ·
      refine ⟨872950679142699306398305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1163934238856932408531073 872950679142699306398305)
      ·
        refine ⟨654713009357024479798729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 872950679142699306398305 654713009357024479798729)
        ·
          refine ⟨491034757017768359849047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 654713009357024479798729 491034757017768359849047)
          ·
            refine ⟨736552135526652539773571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491034757017768359849047 736552135526652539773571)
            ·
              refine ⟨1104828203289978809660357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 736552135526652539773571 1104828203289978809660357)
              ·
                refine ⟨207155288116871026811317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1104828203289978809660357 207155288116871026811317)
                ·
                  refine ⟨19420808260956658763561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 207155288116871026811317 19420808260956658763561)
                  ·
                    rfl

theorem cell23_340397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_340397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340397 prefixEnd_340397 := by exact prefixLift 340397
  have htrace : WordTrace (prefixWord ++ tailWord_340397) baseStart_340397 baseEnd_340397 := by
    simpa [prefixWord, tailWord_340397, baseEnd_340397] using wordTrace_append hprefix tailTrace_340397
  have hstable : (prefixWord ++ tailWord_340397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340397).length < 2 ^ (prefixWord ++ tailWord_340397).sum := by decide
  have hdescent : baseEnd_340397 < baseStart_340397 := by decide
  rcases family_descends (prefixWord ++ tailWord_340397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340423 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 5, 4]
def baseStart_340423 : Nat := 118140960795 + 340423 * 2 ^ 59
def prefixEnd_340423 : Nat := 4983230072969 + 3 ^ 40 * 340423 * 2
def baseEnd_340423 : Nat := 58266874948542275715643

theorem tailTrace_340423 : CollatzResearch.WordTrace tailWord_340423 prefixEnd_340423 58266874948542275715643 := by
  unfold tailWord_340423
  simp only [CollatzResearch.WordTrace]
  refine ⟨12416246845713085464777923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8277497897142056976518615 12416246845713085464777923)
  ·
    refine ⟨18624370268569628197166885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12416246845713085464777923 18624370268569628197166885)
    ·
      refine ⟨3492069425356805286968791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18624370268569628197166885 3492069425356805286968791)
      ·
        refine ⟨5238104138035207930453187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3492069425356805286968791 5238104138035207930453187)
        ·
          refine ⟨7857156207052811895679781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5238104138035207930453187 7857156207052811895679781)
          ·
            refine ⟨1473216788822402230439959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7857156207052811895679781 1473216788822402230439959)
            ·
              refine ⟨2209825183233603345659939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473216788822402230439959 2209825183233603345659939)
              ·
                refine ⟨3314737774850405018489909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2209825183233603345659939 3314737774850405018489909)
                ·
                  refine ⟨310756666392225470483429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3314737774850405018489909 310756666392225470483429)
                  ·
                    refine ⟨58266874948542275715643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 310756666392225470483429 58266874948542275715643)
                    ·
                      rfl

theorem cell23_340423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_340423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340423 prefixEnd_340423 := by exact prefixLift 340423
  have htrace : WordTrace (prefixWord ++ tailWord_340423) baseStart_340423 baseEnd_340423 := by
    simpa [prefixWord, tailWord_340423, baseEnd_340423] using wordTrace_append hprefix tailTrace_340423
  have hstable : (prefixWord ++ tailWord_340423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340423).length < 2 ^ (prefixWord ++ tailWord_340423).sum := by decide
  have hdescent : baseEnd_340423 < baseStart_340423 := by decide
  rcases family_descends (prefixWord ++ tailWord_340423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340490 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 1, 5, 2]
def baseStart_340490 : Nat := 118140960795 + 340490 * 2 ^ 59
def prefixEnd_340490 : Nat := 4983230072969 + 3 ^ 40 * 340490 * 2
def baseEnd_340490 : Nat := 174835028049478065009121

theorem tailTrace_340490 : CollatzResearch.WordTrace tailWord_340490 prefixEnd_340490 174835028049478065009121 := by
  unfold tailWord_340490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3104672634117588976866731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8279127024313570604977949 3104672634117588976866731)
  ·
    refine ⟨4657008951176383465300097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3104672634117588976866731 4657008951176383465300097)
    ·
      refine ⟨3492756713382287598975073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4657008951176383465300097 3492756713382287598975073)
      ·
        refine ⟨2619567535036715699231305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3492756713382287598975073 2619567535036715699231305)
        ·
          refine ⟨1964675651277536774423479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2619567535036715699231305 1964675651277536774423479)
          ·
            refine ⟨2947013476916305161635219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964675651277536774423479 2947013476916305161635219)
            ·
              refine ⟨4420520215374457742452829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947013476916305161635219 4420520215374457742452829)
              ·
                refine ⟨1657695080765421653419811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4420520215374457742452829 1657695080765421653419811)
                ·
                  refine ⟨2486542621148132480129717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657695080765421653419811 2486542621148132480129717)
                  ·
                    refine ⟨233113370732637420012161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2486542621148132480129717 233113370732637420012161)
                    ·
                      refine ⟨174835028049478065009121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233113370732637420012161 174835028049478065009121)
                      ·
                        rfl

theorem cell23_340490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_340490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340490 prefixEnd_340490 := by exact prefixLift 340490
  have htrace : WordTrace (prefixWord ++ tailWord_340490) baseStart_340490 baseEnd_340490 := by
    simpa [prefixWord, tailWord_340490, baseEnd_340490] using wordTrace_append hprefix tailTrace_340490
  have hstable : (prefixWord ++ tailWord_340490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340490).length < 2 ^ (prefixWord ++ tailWord_340490).sum := by decide
  have hdescent : baseEnd_340490 < baseStart_340490 := by decide
  rcases family_descends (prefixWord ++ tailWord_340490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340497 : List Nat := [1, 2, 2, 1, 1, 2, 2, 7, 1, 1, 3]
def baseStart_340497 : Nat := 118140960795 + 340497 * 2 ^ 59
def prefixEnd_340497 : Nat := 4983230072969 + 3 ^ 40 * 340497 * 2
def baseEnd_340497 : Nat := 174838622414059537621589

theorem tailTrace_340497 : CollatzResearch.WordTrace tailWord_340497 prefixEnd_340497 174838622414059537621589 := by
  unfold tailWord_340497
  simp only [CollatzResearch.WordTrace]
  refine ⟨12418945847444996102971745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8279297231629997401981163 12418945847444996102971745)
  ·
    refine ⟨9314209385583747077228809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12418945847444996102971745 9314209385583747077228809)
    ·
      refine ⟨6985657039187810307921607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9314209385583747077228809 6985657039187810307921607)
      ·
        refine ⟨10478485558781715461882411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6985657039187810307921607 10478485558781715461882411)
        ·
          refine ⟨15717728338172573192823617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10478485558781715461882411 15717728338172573192823617)
          ·
            refine ⟨11788296253629429894617713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15717728338172573192823617 11788296253629429894617713)
            ·
              refine ⟨8841222190222072420963285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11788296253629429894617713 8841222190222072420963285)
              ·
                refine ⟨207216145083329822366327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8841222190222072420963285 207216145083329822366327)
                ·
                  refine ⟨310824217624994733549491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207216145083329822366327 310824217624994733549491)
                  ·
                    refine ⟨466236326437492100324237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 310824217624994733549491 466236326437492100324237)
                    ·
                      refine ⟨174838622414059537621589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 466236326437492100324237 174838622414059537621589)
                      ·
                        rfl

theorem cell23_340497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 1, 1, 3].length) (baseStart_340497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340497 prefixEnd_340497 := by exact prefixLift 340497
  have htrace : WordTrace (prefixWord ++ tailWord_340497) baseStart_340497 baseEnd_340497 := by
    simpa [prefixWord, tailWord_340497, baseEnd_340497] using wordTrace_append hprefix tailTrace_340497
  have hstable : (prefixWord ++ tailWord_340497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340497).length < 2 ^ (prefixWord ++ tailWord_340497).sum := by decide
  have hdescent : baseEnd_340497 < baseStart_340497 := by decide
  rcases family_descends (prefixWord ++ tailWord_340497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340533 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_340533 : Nat := 118140960795 + 340533 * 2 ^ 59
def prefixEnd_340533 : Nat := 4983230072969 + 3 ^ 40 * 340533 * 2
def baseEnd_340533 : Nat := 174857107717621396771423

theorem tailTrace_340533 : CollatzResearch.WordTrace tailWord_340533 prefixEnd_340533 174857107717621396771423 := by
  unfold tailWord_340533
  simp only [CollatzResearch.WordTrace]
  refine ⟨12420258875314574251282253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8280172583543049500854835 12420258875314574251282253)
  ·
    refine ⟨4657597078242965344230845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12420258875314574251282253 4657597078242965344230845)
    ·
      refine ⟨1746598904341112004086567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4657597078242965344230845 1746598904341112004086567)
      ·
        refine ⟨2619898356511668006129851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746598904341112004086567 2619898356511668006129851)
        ·
          refine ⟨3929847534767502009194777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2619898356511668006129851 3929847534767502009194777)
          ·
            refine ⟨2947385651075626506896083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3929847534767502009194777 2947385651075626506896083)
            ·
              refine ⟨4421078476613439760344125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947385651075626506896083 4421078476613439760344125)
              ·
                refine ⟨1657904428730039910129047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4421078476613439760344125 1657904428730039910129047)
                ·
                  refine ⟨2486856643095059865193571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657904428730039910129047 2486856643095059865193571)
                  ·
                    refine ⟨3730284964642589797790357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2486856643095059865193571 3730284964642589797790357)
                    ·
                      refine ⟨174857107717621396771423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3730284964642589797790357 174857107717621396771423)
                      ·
                        rfl

theorem cell23_340533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_340533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340533 prefixEnd_340533 := by exact prefixLift 340533
  have htrace : WordTrace (prefixWord ++ tailWord_340533) baseStart_340533 baseEnd_340533 := by
    simpa [prefixWord, tailWord_340533, baseEnd_340533] using wordTrace_append hprefix tailTrace_340533
  have hstable : (prefixWord ++ tailWord_340533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340533).length < 2 ^ (prefixWord ++ tailWord_340533).sum := by decide
  have hdescent : baseEnd_340533 < baseStart_340533 := by decide
  rcases family_descends (prefixWord ++ tailWord_340533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340534 : List Nat := [5, 1, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_340534 : Nat := 118140960795 + 340534 * 2 ^ 59
def prefixEnd_340534 : Nat := 4983230072969 + 3 ^ 40 * 340534 * 2
def baseEnd_340534 : Nat := 58285873732758630952973

theorem tailTrace_340534 : CollatzResearch.WordTrace tailWord_340534 prefixEnd_340534 58285873732758630952973 := by
  unfold tailWord_340534
  simp only [CollatzResearch.WordTrace]
  refine ⟨776268459269434463879291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8280196898873967614712437 776268459269434463879291)
  ·
    refine ⟨1164402688904151695818937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 776268459269434463879291 1164402688904151695818937)
    ·
      refine ⟨873302016678113771864203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1164402688904151695818937 873302016678113771864203)
      ·
        refine ⟨1309953025017170657796305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873302016678113771864203 1309953025017170657796305)
        ·
          refine ⟨982464768762877993347229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1309953025017170657796305 982464768762877993347229)
          ·
            refine ⟨368424288286079247505211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 982464768762877993347229 368424288286079247505211)
            ·
              refine ⟨552636432429118871257817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368424288286079247505211 552636432429118871257817)
              ·
                refine ⟨414477324321839153443363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552636432429118871257817 414477324321839153443363)
                ·
                  refine ⟨621715986482758730165045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414477324321839153443363 621715986482758730165045)
                  ·
                    refine ⟨58285873732758630952973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 621715986482758730165045 58285873732758630952973)
                    ·
                      rfl

theorem cell23_340534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_340534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340534 prefixEnd_340534 := by exact prefixLift 340534
  have htrace : WordTrace (prefixWord ++ tailWord_340534) baseStart_340534 baseEnd_340534 := by
    simpa [prefixWord, tailWord_340534, baseEnd_340534] using wordTrace_append hprefix tailTrace_340534
  have hstable : (prefixWord ++ tailWord_340534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340534).length < 2 ^ (prefixWord ++ tailWord_340534).sum := by decide
  have hdescent : baseEnd_340534 < baseStart_340534 := by decide
  rcases family_descends (prefixWord ++ tailWord_340534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340537 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 5, 2, 2]
def baseStart_340537 : Nat := 118140960795 + 340537 * 2 ^ 59
def prefixEnd_340537 : Nat := 4983230072969 + 3 ^ 40 * 340537 * 2
def baseEnd_340537 : Nat := 174859161640239381121405

theorem tailTrace_340537 : CollatzResearch.WordTrace tailWord_340537 prefixEnd_340537 174859161640239381121405 := by
  unfold tailWord_340537
  simp only [CollatzResearch.WordTrace]
  refine ⟨12420404767300082934427865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8280269844866721956285243 12420404767300082934427865)
  ·
    refine ⟨9315303575475062200820899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12420404767300082934427865 9315303575475062200820899)
    ·
      refine ⟨13972955363212593301231349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9315303575475062200820899 13972955363212593301231349)
      ·
        refine ⟨1309964565301180621990439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13972955363212593301231349 1309964565301180621990439)
        ·
          refine ⟨1964946847951770932985659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309964565301180621990439 1964946847951770932985659)
          ·
            refine ⟨2947420271927656399478489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964946847951770932985659 2947420271927656399478489)
            ·
              refine ⟨2210565203945742299608867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2947420271927656399478489 2210565203945742299608867)
              ·
                refine ⟨3315847805918613449413301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2210565203945742299608867 3315847805918613449413301)
                ·
                  refine ⟨310860731804870010882497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3315847805918613449413301 310860731804870010882497)
                  ·
                    refine ⟨233145548853652508161873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 310860731804870010882497 233145548853652508161873)
                    ·
                      refine ⟨174859161640239381121405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233145548853652508161873 174859161640239381121405)
                      ·
                        rfl

theorem cell23_340537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_340537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340537 prefixEnd_340537 := by exact prefixLift 340537
  have htrace : WordTrace (prefixWord ++ tailWord_340537) baseStart_340537 baseEnd_340537 := by
    simpa [prefixWord, tailWord_340537, baseEnd_340537] using wordTrace_append hprefix tailTrace_340537
  have hstable : (prefixWord ++ tailWord_340537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340537).length < 2 ^ (prefixWord ++ tailWord_340537).sum := by decide
  have hdescent : baseEnd_340537 < baseStart_340537 := by decide
  rcases family_descends (prefixWord ++ tailWord_340537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340557 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_340557 : Nat := 118140960795 + 340557 * 2 ^ 59
def prefixEnd_340557 : Nat := 4983230072969 + 3 ^ 40 * 340557 * 2
def baseEnd_340557 : Nat := 174869431253329302871313

theorem tailTrace_340557 : CollatzResearch.WordTrace tailWord_340557 prefixEnd_340557 174869431253329302871313 := by
  unfold tailWord_340557
  simp only [CollatzResearch.WordTrace]
  refine ⟨12421134227227626350155925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8280756151485084233437283 12421134227227626350155925)
  ·
    refine ⟨582240666901294985163559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12421134227227626350155925 582240666901294985163559)
    ·
      refine ⟨873361000351942477745339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 582240666901294985163559 873361000351942477745339)
      ·
        refine ⟨1310041500527913716618009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873361000351942477745339 1310041500527913716618009)
        ·
          refine ⟨982531125395935287463507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1310041500527913716618009 982531125395935287463507)
          ·
            refine ⟨1473796688093902931195261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982531125395935287463507 1473796688093902931195261)
            ·
              refine ⟨552673758035213599198223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1473796688093902931195261 552673758035213599198223)
              ·
                refine ⟨829010637052820398797335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552673758035213599198223 829010637052820398797335)
                ·
                  refine ⟨1243515955579230598196003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829010637052820398797335 1243515955579230598196003)
                  ·
                    refine ⟨1865273933368845897294005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1243515955579230598196003 1865273933368845897294005)
                    ·
                      refine ⟨174869431253329302871313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1865273933368845897294005 174869431253329302871313)
                      ·
                        rfl

theorem cell23_340557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_340557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340557 prefixEnd_340557 := by exact prefixLift 340557
  have htrace : WordTrace (prefixWord ++ tailWord_340557) baseStart_340557 baseEnd_340557 := by
    simpa [prefixWord, tailWord_340557, baseEnd_340557] using wordTrace_append hprefix tailTrace_340557
  have hstable : (prefixWord ++ tailWord_340557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340557).length < 2 ^ (prefixWord ++ tailWord_340557).sum := by decide
  have hdescent : baseEnd_340557 < baseStart_340557 := by decide
  rcases family_descends (prefixWord ++ tailWord_340557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340583 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_340583 : Nat := 118140960795 + 340583 * 2 ^ 59
def prefixEnd_340583 : Nat := 4983230072969 + 3 ^ 40 * 340583 * 2
def baseEnd_340583 : Nat := 174882781750346201146193

theorem tailTrace_340583 : CollatzResearch.WordTrace tailWord_340583 prefixEnd_340583 174882781750346201146193 := by
  unfold tailWord_340583
  simp only [CollatzResearch.WordTrace]
  refine ⟨12422082525133432790602403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8281388350088955193734935 12422082525133432790602403)
  ·
    refine ⟨18633123787700149185903605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12422082525133432790602403 18633123787700149185903605)
    ·
      refine ⟨1746855355096888986178463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18633123787700149185903605 1746855355096888986178463)
      ·
        refine ⟨2620283032645333479267695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746855355096888986178463 2620283032645333479267695)
        ·
          refine ⟨3930424548968000218901543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2620283032645333479267695 3930424548968000218901543)
          ·
            refine ⟨5895636823452000328352315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3930424548968000218901543 5895636823452000328352315)
            ·
              refine ⟨8843455235178000492528473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5895636823452000328352315 8843455235178000492528473)
              ·
                refine ⟨6632591426383500369396355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8843455235178000492528473 6632591426383500369396355)
                ·
                  refine ⟨9948887139575250554094533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6632591426383500369396355 9948887139575250554094533)
                  ·
                    refine ⟨1865416338670359478892725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9948887139575250554094533 1865416338670359478892725)
                    ·
                      refine ⟨174882781750346201146193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1865416338670359478892725 174882781750346201146193)
                      ·
                        rfl

theorem cell23_340583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_340583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340583 prefixEnd_340583 := by exact prefixLift 340583
  have htrace : WordTrace (prefixWord ++ tailWord_340583) baseStart_340583 baseEnd_340583 := by
    simpa [prefixWord, tailWord_340583, baseEnd_340583] using wordTrace_append hprefix tailTrace_340583
  have hstable : (prefixWord ++ tailWord_340583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340583).length < 2 ^ (prefixWord ++ tailWord_340583).sum := by decide
  have hdescent : baseEnd_340583 < baseStart_340583 := by decide
  rcases family_descends (prefixWord ++ tailWord_340583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340623 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 4]
def baseStart_340623 : Nat := 118140960795 + 340623 * 2 ^ 59
def prefixEnd_340623 : Nat := 4983230072969 + 3 ^ 40 * 340623 * 2
def baseEnd_340623 : Nat := 174903320976526044646009

theorem tailTrace_340623 : CollatzResearch.WordTrace tailWord_340623 prefixEnd_340623 174903320976526044646009 := by
  unfold tailWord_340623
  simp only [CollatzResearch.WordTrace]
  refine ⟨12423541444988519622058523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8282360963325679748039015 12423541444988519622058523)
  ·
    refine ⟨18635312167482779433087785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12423541444988519622058523 18635312167482779433087785)
    ·
      refine ⟨13976484125612084574815839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18635312167482779433087785 13976484125612084574815839)
      ·
        refine ⟨20964726188418126862223759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13976484125612084574815839 20964726188418126862223759)
        ·
          refine ⟨31447089282627190293335639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20964726188418126862223759 31447089282627190293335639)
          ·
            refine ⟨47170633923940785440003459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31447089282627190293335639 47170633923940785440003459)
            ·
              refine ⟨70755950885911178160005189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47170633923940785440003459 70755950885911178160005189)
              ·
                refine ⟨13266740791108345905000973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70755950885911178160005189 13266740791108345905000973)
                ·
                  refine ⟨4975027796665629714375365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13266740791108345905000973 4975027796665629714375365)
                  ·
                    refine ⟨932817711874805571445381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4975027796665629714375365 932817711874805571445381)
                    ·
                      refine ⟨174903320976526044646009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 932817711874805571445381 174903320976526044646009)
                      ·
                        rfl

theorem cell23_340623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_340623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340623 prefixEnd_340623 := by exact prefixLift 340623
  have htrace : WordTrace (prefixWord ++ tailWord_340623) baseStart_340623 baseEnd_340623 := by
    simpa [prefixWord, tailWord_340623, baseEnd_340623] using wordTrace_append hprefix tailTrace_340623
  have hstable : (prefixWord ++ tailWord_340623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340623).length < 2 ^ (prefixWord ++ tailWord_340623).sum := by decide
  have hdescent : baseEnd_340623 < baseStart_340623 := by decide
  rcases family_descends (prefixWord ++ tailWord_340623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340627 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 4, 2, 2]
def baseStart_340627 : Nat := 118140960795 + 340627 * 2 ^ 59
def prefixEnd_340627 : Nat := 4983230072969 + 3 ^ 40 * 340627 * 2
def baseEnd_340627 : Nat := 174905374899144028995991

theorem tailTrace_340627 : CollatzResearch.WordTrace tailWord_340627 prefixEnd_340627 174905374899144028995991 := by
  unfold tailWord_340627
  simp only [CollatzResearch.WordTrace]
  refine ⟨12423687336974028305204135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8282458224649352203469423 12423687336974028305204135)
  ·
    refine ⟨18635531005461042457806203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12423687336974028305204135 18635531005461042457806203)
    ·
      refine ⟨27953296508191563686709305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18635531005461042457806203 27953296508191563686709305)
      ·
        refine ⟨20964972381143672765031979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27953296508191563686709305 20964972381143672765031979)
        ·
          refine ⟨31447458571715509147547969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20964972381143672765031979 31447458571715509147547969)
          ·
            refine ⟨23585593928786631860660977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31447458571715509147547969 23585593928786631860660977)
            ·
              refine ⟨17689195446589973895495733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23585593928786631860660977 17689195446589973895495733)
              ·
                refine ⟨1658362073117810052702725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17689195446589973895495733 1658362073117810052702725)
                ·
                  refine ⟨310942888709589384881761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1658362073117810052702725 310942888709589384881761)
                  ·
                    refine ⟨233207166532192038661321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 310942888709589384881761 233207166532192038661321)
                    ·
                      refine ⟨174905374899144028995991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233207166532192038661321 174905374899144028995991)
                      ·
                        rfl

theorem cell23_340627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 2, 2].length) (baseStart_340627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340627 prefixEnd_340627 := by exact prefixLift 340627
  have htrace : WordTrace (prefixWord ++ tailWord_340627) baseStart_340627 baseEnd_340627 := by
    simpa [prefixWord, tailWord_340627, baseEnd_340627] using wordTrace_append hprefix tailTrace_340627
  have hstable : (prefixWord ++ tailWord_340627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340627).length < 2 ^ (prefixWord ++ tailWord_340627).sum := by decide
  have hdescent : baseEnd_340627 < baseStart_340627 := by decide
  rcases family_descends (prefixWord ++ tailWord_340627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340680 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 4, 5]
def baseStart_340680 : Nat := 118140960795 + 340680 * 2 ^ 59
def prefixEnd_340680 : Nat := 4983230072969 + 3 ^ 40 * 340680 * 2
def baseEnd_340680 : Nat := 58310863124610773877749

theorem tailTrace_340680 : CollatzResearch.WordTrace tailWord_340680 prefixEnd_340680 58310863124610773877749 := by
  unfold tailWord_340680
  simp only [CollatzResearch.WordTrace]
  refine ⟨6212810202891009178441747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8283746937188012237922329 6212810202891009178441747)
  ·
    refine ⟨9319215304336513767662621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6212810202891009178441747 9319215304336513767662621)
    ·
      refine ⟨3494705739126192662873483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9319215304336513767662621 3494705739126192662873483)
      ·
        refine ⟨5242058608689288994310225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3494705739126192662873483 5242058608689288994310225)
        ·
          refine ⟨3931543956516966745732669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5242058608689288994310225 3931543956516966745732669)
          ·
            refine ⟨1474328983693862529649751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3931543956516966745732669 1474328983693862529649751)
            ·
              refine ⟨2211493475540793794474627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1474328983693862529649751 2211493475540793794474627)
              ·
                refine ⟨3317240213311190691711941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211493475540793794474627 3317240213311190691711941)
                ·
                  refine ⟨621982539995848254695989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3317240213311190691711941 621982539995848254695989)
                  ·
                    refine ⟨58310863124610773877749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 621982539995848254695989 58310863124610773877749)
                    ·
                      rfl

theorem cell23_340680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_340680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340680 prefixEnd_340680 := by exact prefixLift 340680
  have htrace : WordTrace (prefixWord ++ tailWord_340680) baseStart_340680 baseEnd_340680 := by
    simpa [prefixWord, tailWord_340680, baseEnd_340680] using wordTrace_append hprefix tailTrace_340680
  have hstable : (prefixWord ++ tailWord_340680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340680).length < 2 ^ (prefixWord ++ tailWord_340680).sum := by decide
  have hdescent : baseEnd_340680 < baseStart_340680 := by decide
  rcases family_descends (prefixWord ++ tailWord_340680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340683 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 8]
def baseStart_340683 : Nat := 118140960795 + 340683 * 2 ^ 59
def prefixEnd_340683 : Nat := 4983230072969 + 3 ^ 40 * 340683 * 2
def baseEnd_340683 : Nat := 174934129815795809895733

theorem tailTrace_340683 : CollatzResearch.WordTrace tailWord_340683 prefixEnd_340683 174934129815795809895733 := by
  unfold tailWord_340683
  simp only [CollatzResearch.WordTrace]
  refine ⟨12425729824771149869242703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8283819883180766579495135 12425729824771149869242703)
  ·
    refine ⟨18638594737156724803864055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12425729824771149869242703 18638594737156724803864055)
    ·
      refine ⟨27957892105735087205796083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18638594737156724803864055 27957892105735087205796083)
      ·
        refine ⟨41936838158602630808694125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27957892105735087205796083 41936838158602630808694125)
        ·
          refine ⟨15726314309475986553260297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41936838158602630808694125 15726314309475986553260297)
          ·
            refine ⟨11794735732106989914945223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15726314309475986553260297 11794735732106989914945223)
            ·
              refine ⟨17692103598160484872417835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11794735732106989914945223 17692103598160484872417835)
              ·
                refine ⟨26538155397240727308626753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17692103598160484872417835 26538155397240727308626753)
                ·
                  refine ⟨19903616547930545481470065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26538155397240727308626753 19903616547930545481470065)
                  ·
                    refine ⟨14927712410947909111102549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19903616547930545481470065 14927712410947909111102549)
                    ·
                      refine ⟨174934129815795809895733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 14927712410947909111102549 174934129815795809895733)
                      ·
                        rfl

theorem cell23_340683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_340683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340683 prefixEnd_340683 := by exact prefixLift 340683
  have htrace : WordTrace (prefixWord ++ tailWord_340683) baseStart_340683 baseEnd_340683 := by
    simpa [prefixWord, tailWord_340683, baseEnd_340683] using wordTrace_append hprefix tailTrace_340683
  have hstable : (prefixWord ++ tailWord_340683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340683).length < 2 ^ (prefixWord ++ tailWord_340683).sum := by decide
  have hdescent : baseEnd_340683 < baseStart_340683 := by decide
  rcases family_descends (prefixWord ++ tailWord_340683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340734 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_340734 : Nat := 118140960795 + 340734 * 2 ^ 59
def prefixEnd_340734 : Nat := 4983230072969 + 3 ^ 40 * 340734 * 2
def baseEnd_340734 : Nat := 174960317329175110357999

theorem tailTrace_340734 : CollatzResearch.WordTrace tailWord_340734 prefixEnd_340734 174960317329175110357999 := by
  unfold tailWord_340734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1553448743448298197418657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8285059965057590386232837 1553448743448298197418657)
  ·
    refine ⟨1165086557586223648063993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1553448743448298197418657 1165086557586223648063993)
    ·
      refine ⟨873814918189667736047995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1165086557586223648063993 873814918189667736047995)
      ·
        refine ⟨1310722377284501604071993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873814918189667736047995 1310722377284501604071993)
        ·
          refine ⟨983041782963376203053995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1310722377284501604071993 983041782963376203053995)
          ·
            refine ⟨1474562674445064304580993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983041782963376203053995 1474562674445064304580993)
            ·
              refine ⟨1105922005833798228435745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1474562674445064304580993 1105922005833798228435745)
              ·
                refine ⟨829441504375348671326809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1105922005833798228435745 829441504375348671326809)
                ·
                  refine ⟨622081128281511503495107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 829441504375348671326809 622081128281511503495107)
                  ·
                    refine ⟨933121692422267255242661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 622081128281511503495107 933121692422267255242661)
                    ·
                      refine ⟨174960317329175110357999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 933121692422267255242661 174960317329175110357999)
                      ·
                        rfl

theorem cell23_340734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_340734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340734 prefixEnd_340734 := by exact prefixLift 340734
  have htrace : WordTrace (prefixWord ++ tailWord_340734) baseStart_340734 baseEnd_340734 := by
    simpa [prefixWord, tailWord_340734, baseEnd_340734] using wordTrace_append hprefix tailTrace_340734
  have hstable : (prefixWord ++ tailWord_340734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340734).length < 2 ^ (prefixWord ++ tailWord_340734).sum := by decide
  have hdescent : baseEnd_340734 < baseStart_340734 := by decide
  rcases family_descends (prefixWord ++ tailWord_340734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340777 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 1, 5, 2]
def baseStart_340777 : Nat := 118140960795 + 340777 * 2 ^ 59
def prefixEnd_340777 : Nat := 4983230072969 + 3 ^ 40 * 340777 * 2
def baseEnd_340777 : Nat := 174982396997318442120301

theorem tailTrace_340777 : CollatzResearch.WordTrace tailWord_340777 prefixEnd_340777 174982396997318442120301 := by
  unfold tailWord_340777
  simp only [CollatzResearch.WordTrace]
  refine ⟨12429158286430603923164585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8286105524287069282109723 12429158286430603923164585)
  ·
    refine ⟨9321868714822952942373439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12429158286430603923164585 9321868714822952942373439)
    ·
      refine ⟨13982803072234429413560159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9321868714822952942373439 13982803072234429413560159)
      ·
        refine ⟨20974204608351644120340239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13982803072234429413560159 20974204608351644120340239)
        ·
          refine ⟨31461306912527466180510359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20974204608351644120340239 31461306912527466180510359)
          ·
            refine ⟨47191960368791199270765539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31461306912527466180510359 47191960368791199270765539)
            ·
              refine ⟨70787940553186798906148309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47191960368791199270765539 70787940553186798906148309)
              ·
                refine ⟨1659092356715315599362851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70787940553186798906148309 1659092356715315599362851)
                ·
                  refine ⟨2488638535072973399044277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659092356715315599362851 2488638535072973399044277)
                  ·
                    refine ⟨233309862663091256160401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2488638535072973399044277 233309862663091256160401)
                    ·
                      refine ⟨174982396997318442120301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233309862663091256160401 174982396997318442120301)
                      ·
                        rfl

theorem cell23_340777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 5, 2].length) (baseStart_340777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340777 prefixEnd_340777 := by exact prefixLift 340777
  have htrace : WordTrace (prefixWord ++ tailWord_340777) baseStart_340777 baseEnd_340777 := by
    simpa [prefixWord, tailWord_340777, baseEnd_340777] using wordTrace_append hprefix tailTrace_340777
  have hstable : (prefixWord ++ tailWord_340777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340777).length < 2 ^ (prefixWord ++ tailWord_340777).sum := by decide
  have hdescent : baseEnd_340777 < baseStart_340777 := by decide
  rcases family_descends (prefixWord ++ tailWord_340777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340800 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 3, 6]
def baseStart_340800 : Nat := 118140960795 + 340800 * 2 ^ 59
def prefixEnd_340800 : Nat := 4983230072969 + 3 ^ 40 * 340800 * 2
def baseEnd_340800 : Nat := 58331402350790617377565

theorem tailTrace_340800 : CollatzResearch.WordTrace tailWord_340800 prefixEnd_340800 58331402350790617377565 := by
  unfold tailWord_340800
  simp only [CollatzResearch.WordTrace]
  refine ⟨6214998582673639425625927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8286664776898185900834569 6214998582673639425625927)
  ·
    refine ⟨9322497874010459138438891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6214998582673639425625927 9322497874010459138438891)
    ·
      refine ⟨13983746811015688707658337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9322497874010459138438891 13983746811015688707658337)
      ·
        refine ⟨10487810108261766530743753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13983746811015688707658337 10487810108261766530743753)
        ·
          refine ⟨7865857581196324898057815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10487810108261766530743753 7865857581196324898057815)
          ·
            refine ⟨11798786371794487347086723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7865857581196324898057815 11798786371794487347086723)
            ·
              refine ⟨17698179557691731020630085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11798786371794487347086723 17698179557691731020630085)
              ·
                refine ⟨3318408667067199566368141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17698179557691731020630085 3318408667067199566368141)
                ·
                  refine ⟨1244403250150199837388053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3318408667067199566368141 1244403250150199837388053)
                  ·
                    refine ⟨58331402350790617377565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1244403250150199837388053 58331402350790617377565)
                    ·
                      rfl

theorem cell23_340800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_340800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340800 prefixEnd_340800 := by exact prefixLift 340800
  have htrace : WordTrace (prefixWord ++ tailWord_340800) baseStart_340800 baseEnd_340800 := by
    simpa [prefixWord, tailWord_340800, baseEnd_340800] using wordTrace_append hprefix tailTrace_340800
  have hstable : (prefixWord ++ tailWord_340800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340800).length < 2 ^ (prefixWord ++ tailWord_340800).sum := by decide
  have hdescent : baseEnd_340800 < baseStart_340800 := by decide
  rcases family_descends (prefixWord ++ tailWord_340800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340837 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 1, 2, 4]
def baseStart_340837 : Nat := 118140960795 + 340837 * 2 ^ 59
def prefixEnd_340837 : Nat := 4983230072969 + 3 ^ 40 * 340837 * 2
def baseEnd_340837 : Nat := 175013205836588207370025

theorem tailTrace_340837 : CollatzResearch.WordTrace tailWord_340837 prefixEnd_340837 175013205836588207370025 := by
  unfold tailWord_340837
  simp only [CollatzResearch.WordTrace]
  refine ⟨12431346666213234170348765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8287564444142156113565843 12431346666213234170348765)
  ·
    refine ⟨4661754999829962813880787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12431346666213234170348765 4661754999829962813880787)
    ·
      refine ⟨6992632499744944220821181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4661754999829962813880787 6992632499744944220821181)
      ·
        refine ⟨2622237187404354082807943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6992632499744944220821181 2622237187404354082807943)
        ·
          refine ⟨3933355781106531124211915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2622237187404354082807943 3933355781106531124211915)
          ·
            refine ⟨5900033671659796686317873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3933355781106531124211915 5900033671659796686317873)
            ·
              refine ⟨4425025253744847514738405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5900033671659796686317873 4425025253744847514738405)
              ·
                refine ⟨829692235077158909013451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4425025253744847514738405 829692235077158909013451)
                ·
                  refine ⟨1244538352615738363520177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 829692235077158909013451 1244538352615738363520177)
                  ·
                    refine ⟨933403764461803772640133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1244538352615738363520177 933403764461803772640133)
                    ·
                      refine ⟨175013205836588207370025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 933403764461803772640133 175013205836588207370025)
                      ·
                        rfl

theorem cell23_340837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_340837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340837 prefixEnd_340837 := by exact prefixLift 340837
  have htrace : WordTrace (prefixWord ++ tailWord_340837) baseStart_340837 baseEnd_340837 := by
    simpa [prefixWord, tailWord_340837, baseEnd_340837] using wordTrace_append hprefix tailTrace_340837
  have hstable : (prefixWord ++ tailWord_340837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340837).length < 2 ^ (prefixWord ++ tailWord_340837).sum := by decide
  have hdescent : baseEnd_340837 < baseStart_340837 := by decide
  rcases family_descends (prefixWord ++ tailWord_340837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340844 : List Nat := [2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 3]
def baseStart_340844 : Nat := 118140960795 + 340844 * 2 ^ 59
def prefixEnd_340844 : Nat := 4983230072969 + 3 ^ 40 * 340844 * 2
def baseEnd_340844 : Nat := 175016800201169679982493

theorem tailTrace_340844 : CollatzResearch.WordTrace tailWord_340844 prefixEnd_340844 175016800201169679982493 := by
  unfold tailWord_340844
  simp only [CollatzResearch.WordTrace]
  refine ⟨6215800988593937182926793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8287734651458582910569057 6215800988593937182926793)
  ·
    refine ⟨4661850741445452887195095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6215800988593937182926793 4661850741445452887195095)
    ·
      refine ⟨6992776112168179330792643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4661850741445452887195095 6992776112168179330792643)
      ·
        refine ⟨10489164168252268996188965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6992776112168179330792643 10489164168252268996188965)
        ·
          refine ⟨1966718281547300436785431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10489164168252268996188965 1966718281547300436785431)
          ·
            refine ⟨2950077422320950655178147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1966718281547300436785431 2950077422320950655178147)
            ·
              refine ⟨4425116133481425982767221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2950077422320950655178147 4425116133481425982767221)
              ·
                refine ⟨414854637513883685884427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4425116133481425982767221 414854637513883685884427)
                ·
                  refine ⟨622281956270825528826641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 414854637513883685884427 622281956270825528826641)
                  ·
                    refine ⟨466711467203119146619981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 622281956270825528826641 466711467203119146619981)
                    ·
                      refine ⟨175016800201169679982493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 466711467203119146619981 175016800201169679982493)
                      ·
                        rfl

theorem cell23_340844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_340844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340844 prefixEnd_340844 := by exact prefixLift 340844
  have htrace : WordTrace (prefixWord ++ tailWord_340844) baseStart_340844 baseEnd_340844 := by
    simpa [prefixWord, tailWord_340844, baseEnd_340844] using wordTrace_append hprefix tailTrace_340844
  have hstable : (prefixWord ++ tailWord_340844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340844).length < 2 ^ (prefixWord ++ tailWord_340844).sum := by decide
  have hdescent : baseEnd_340844 < baseStart_340844 := by decide
  rcases family_descends (prefixWord ++ tailWord_340844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340854 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_340854 : Nat := 118140960795 + 340854 * 2 ^ 59
def prefixEnd_340854 : Nat := 4983230072969 + 3 ^ 40 * 340854 * 2
def baseEnd_340854 : Nat := 175021935007714640857447

theorem tailTrace_340854 : CollatzResearch.WordTrace tailWord_340854 prefixEnd_340854 175021935007714640857447 := by
  unfold tailWord_340854
  simp only [CollatzResearch.WordTrace]
  refine ⟨776997919196977879607351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8287977804767764049145077 776997919196977879607351)
  ·
    refine ⟨1165496878795466819411027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 776997919196977879607351 1165496878795466819411027)
    ·
      refine ⟨1748245318193200229116541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1165496878795466819411027 1748245318193200229116541)
      ·
        refine ⟨655591994322450085918703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1748245318193200229116541 655591994322450085918703)
        ·
          refine ⟨983387991483675128878055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655591994322450085918703 983387991483675128878055)
          ·
            refine ⟨1475081987225512693317083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983387991483675128878055 1475081987225512693317083)
            ·
              refine ⟨2212622980838269039975625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475081987225512693317083 2212622980838269039975625)
              ·
                refine ⟨1659467235628701779981719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212622980838269039975625 1659467235628701779981719)
                ·
                  refine ⟨2489200853443052669972579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659467235628701779981719 2489200853443052669972579)
                  ·
                    refine ⟨3733801280164579004958869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2489200853443052669972579 3733801280164579004958869)
                    ·
                      refine ⟨175021935007714640857447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3733801280164579004958869 175021935007714640857447)
                      ·
                        rfl

theorem cell23_340854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_340854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340854 prefixEnd_340854 := by exact prefixLift 340854
  have htrace : WordTrace (prefixWord ++ tailWord_340854) baseStart_340854 baseEnd_340854 := by
    simpa [prefixWord, tailWord_340854, baseEnd_340854] using wordTrace_append hprefix tailTrace_340854
  have hstable : (prefixWord ++ tailWord_340854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340854).length < 2 ^ (prefixWord ++ tailWord_340854).sum := by decide
  have hdescent : baseEnd_340854 < baseStart_340854 := by decide
  rcases family_descends (prefixWord ++ tailWord_340854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340965 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 4, 2, 2]
def baseStart_340965 : Nat := 118140960795 + 340965 * 2 ^ 59
def prefixEnd_340965 : Nat := 4983230072969 + 3 ^ 40 * 340965 * 2
def baseEnd_340965 : Nat := 175078931360363706569437

theorem tailTrace_340965 : CollatzResearch.WordTrace tailWord_340965 prefixEnd_340965 175078931360363706569437 := by
  unfold tailWord_340965
  simp only [CollatzResearch.WordTrace]
  refine ⟨12436015209749512031008349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8290676806499674687338899 12436015209749512031008349)
  ·
    refine ⟨4663505703656067011628131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12436015209749512031008349 4663505703656067011628131)
    ·
      refine ⟨6995258555484100517442197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4663505703656067011628131 6995258555484100517442197)
      ·
        refine ⟨327902744788317211755103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6995258555484100517442197 327902744788317211755103)
        ·
          refine ⟨491854117182475817632655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327902744788317211755103 491854117182475817632655)
          ·
            refine ⟨737781175773713726448983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491854117182475817632655 737781175773713726448983)
            ·
              refine ⟨1106671763660570589673475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737781175773713726448983 1106671763660570589673475)
              ·
                refine ⟨1660007645490855884510213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1106671763660570589673475 1660007645490855884510213)
                ·
                  refine ⟨311251433529535478345665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1660007645490855884510213 311251433529535478345665)
                  ·
                    refine ⟨233438575147151608759249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 311251433529535478345665 233438575147151608759249)
                    ·
                      refine ⟨175078931360363706569437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233438575147151608759249 175078931360363706569437)
                      ·
                        rfl

theorem cell23_340965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_340965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340965 prefixEnd_340965 := by exact prefixLift 340965
  have htrace : WordTrace (prefixWord ++ tailWord_340965) baseStart_340965 baseEnd_340965 := by
    simpa [prefixWord, tailWord_340965, baseEnd_340965] using wordTrace_append hprefix tailTrace_340965
  have hstable : (prefixWord ++ tailWord_340965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340965).length < 2 ^ (prefixWord ++ tailWord_340965).sum := by decide
  have hdescent : baseEnd_340965 < baseStart_340965 := by decide
  rcases family_descends (prefixWord ++ tailWord_340965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340982 : List Nat := [5, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_340982 : Nat := 118140960795 + 340982 * 2 ^ 59
def prefixEnd_340982 : Nat := 4983230072969 + 3 ^ 40 * 340982 * 2
def baseEnd_340982 : Nat := 175087660531490140056859

theorem tailTrace_340982 : CollatzResearch.WordTrace tailWord_340982 prefixEnd_340982 175087660531490140056859 := by
  unfold tailWord_340982
  simp only [CollatzResearch.WordTrace]
  refine ⟨777289703167995245898575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8291090167125282622918133 777289703167995245898575)
  ·
    refine ⟨1165934554751992868847863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 777289703167995245898575 1165934554751992868847863)
    ·
      refine ⟨1748901832127989303271795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1165934554751992868847863 1748901832127989303271795)
      ·
        refine ⟨2623352748191983954907693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1748901832127989303271795 2623352748191983954907693)
        ·
          refine ⟨983757280571993983090385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2623352748191983954907693 983757280571993983090385)
          ·
            refine ⟨737817960428995487317789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 983757280571993983090385 737817960428995487317789)
            ·
              refine ⟨276681735160873307744171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 737817960428995487317789 276681735160873307744171)
              ·
                refine ⟨415022602741309961616257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276681735160873307744171 415022602741309961616257)
                ·
                  refine ⟨311266952055982471212193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415022602741309961616257 311266952055982471212193)
                  ·
                    refine ⟨233450214041986853409145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 311266952055982471212193 233450214041986853409145)
                    ·
                      refine ⟨175087660531490140056859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233450214041986853409145 175087660531490140056859)
                      ·
                        rfl

theorem cell23_340982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_340982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340982 prefixEnd_340982 := by exact prefixLift 340982
  have htrace : WordTrace (prefixWord ++ tailWord_340982) baseStart_340982 baseEnd_340982 := by
    simpa [prefixWord, tailWord_340982, baseEnd_340982] using wordTrace_append hprefix tailTrace_340982
  have hstable : (prefixWord ++ tailWord_340982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340982).length < 2 ^ (prefixWord ++ tailWord_340982).sum := by decide
  have hdescent : baseEnd_340982 < baseStart_340982 := by decide
  rcases family_descends (prefixWord ++ tailWord_340982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340997 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 2, 8]
def baseStart_340997 : Nat := 118140960795 + 340997 * 2 ^ 59
def prefixEnd_340997 : Nat := 4983230072969 + 3 ^ 40 * 340997 * 2
def baseEnd_340997 : Nat := 58365120913769193789763

theorem tailTrace_340997 : CollatzResearch.WordTrace tailWord_340997 prefixEnd_340997 58365120913769193789763 := by
  unfold tailWord_340997
  simp only [CollatzResearch.WordTrace]
  refine ⟨12437182345633581496173245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8291454897089054330782163 12437182345633581496173245)
  ·
    refine ⟨4663943379612593061064967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12437182345633581496173245 4663943379612593061064967)
    ·
      refine ⟨6995915069418889591597451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4663943379612593061064967 6995915069418889591597451)
      ·
        refine ⟨10493872604128334387396177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6995915069418889591597451 10493872604128334387396177)
        ·
          refine ⟨7870404453096250790547133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10493872604128334387396177 7870404453096250790547133)
          ·
            refine ⟨2951401669911094046455175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7870404453096250790547133 2951401669911094046455175)
            ·
              refine ⟨4427102504866641069682763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2951401669911094046455175 4427102504866641069682763)
              ·
                refine ⟨6640653757299961604524145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4427102504866641069682763 6640653757299961604524145)
                ·
                  refine ⟨4980490317974971203393109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6640653757299961604524145 4980490317974971203393109)
                  ·
                    refine ⟨58365120913769193789763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4980490317974971203393109 58365120913769193789763)
                    ·
                      rfl

theorem cell23_340997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_340997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_340997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_340997 prefixEnd_340997 := by exact prefixLift 340997
  have htrace : WordTrace (prefixWord ++ tailWord_340997) baseStart_340997 baseEnd_340997 := by
    simpa [prefixWord, tailWord_340997, baseEnd_340997] using wordTrace_append hprefix tailTrace_340997
  have hstable : (prefixWord ++ tailWord_340997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340997).length < 2 ^ (prefixWord ++ tailWord_340997).sum := by decide
  have hdescent : baseEnd_340997 < baseStart_340997 := by decide
  rcases family_descends (prefixWord ++ tailWord_340997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341004 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_341004 : Nat := 118140960795 + 341004 * 2 ^ 59
def prefixEnd_341004 : Nat := 4983230072969 + 3 ^ 40 * 341004 * 2
def baseEnd_341004 : Nat := 175098957105889053981757

theorem tailTrace_341004 : CollatzResearch.WordTrace tailWord_341004 prefixEnd_341004 175098957105889053981757 := by
  unfold tailWord_341004
  simp only [CollatzResearch.WordTrace]
  refine ⟨6218718828304110845839033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8291625104405481127785377 6218718828304110845839033)
  ·
    refine ⟨4664039121228083134379275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6218718828304110845839033 4664039121228083134379275)
    ·
      refine ⟨6996058681842124701568913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4664039121228083134379275 6996058681842124701568913)
      ·
        refine ⟨5247044011381593526176685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6996058681842124701568913 5247044011381593526176685)
        ·
          refine ⟨1967641504268097572316257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5247044011381593526176685 1967641504268097572316257)
          ·
            refine ⟨1475731128201073179237193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1967641504268097572316257 1475731128201073179237193)
            ·
              refine ⟨1106798346150804884427895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1475731128201073179237193 1106798346150804884427895)
              ·
                refine ⟨1660197519226207326641843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1106798346150804884427895 1660197519226207326641843)
                ·
                  refine ⟨2490296278839310989962765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1660197519226207326641843 2490296278839310989962765)
                  ·
                    refine ⟨933861104564741621236037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2490296278839310989962765 933861104564741621236037)
                    ·
                      refine ⟨175098957105889053981757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 933861104564741621236037 175098957105889053981757)
                      ·
                        rfl

theorem cell23_341004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_341004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341004 prefixEnd_341004 := by exact prefixLift 341004
  have htrace : WordTrace (prefixWord ++ tailWord_341004) baseStart_341004 baseEnd_341004 := by
    simpa [prefixWord, tailWord_341004, baseEnd_341004] using wordTrace_append hprefix tailTrace_341004
  have hstable : (prefixWord ++ tailWord_341004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341004).length < 2 ^ (prefixWord ++ tailWord_341004).sum := by decide
  have hdescent : baseEnd_341004 < baseStart_341004 := by decide
  rcases family_descends (prefixWord ++ tailWord_341004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341017 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 6]
def baseStart_341017 : Nat := 118140960795 + 341017 * 2 ^ 59
def prefixEnd_341017 : Nat := 4983230072969 + 3 ^ 40 * 341017 * 2
def baseEnd_341017 : Nat := 175105632354397503119197

theorem tailTrace_341017 : CollatzResearch.WordTrace tailWord_341017 prefixEnd_341017 175105632354397503119197 := by
  unfold tailWord_341017
  simp only [CollatzResearch.WordTrace]
  refine ⟨12437911805561124911901305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8291941203707416607934203 12437911805561124911901305)
  ·
    refine ⟨9328433854170843683925979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12437911805561124911901305 9328433854170843683925979)
    ·
      refine ⟨13992650781256265525888969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9328433854170843683925979 13992650781256265525888969)
      ·
        refine ⟨10494488085942199144416727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13992650781256265525888969 10494488085942199144416727)
        ·
          refine ⟨15741732128913298716625091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10494488085942199144416727 15741732128913298716625091)
          ·
            refine ⟨23612598193369948074937637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15741732128913298716625091 23612598193369948074937637)
            ·
              refine ⟨4427362161256865264050807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23612598193369948074937637 4427362161256865264050807)
              ·
                refine ⟨6641043241885297896076211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4427362161256865264050807 6641043241885297896076211)
                ·
                  refine ⟨9961564862827946844114317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6641043241885297896076211 9961564862827946844114317)
                  ·
                    refine ⟨3735586823560480066542869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9961564862827946844114317 3735586823560480066542869)
                    ·
                      refine ⟨175105632354397503119197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3735586823560480066542869 175105632354397503119197)
                      ·
                        rfl

theorem cell23_341017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_341017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341017 prefixEnd_341017 := by exact prefixLift 341017
  have htrace : WordTrace (prefixWord ++ tailWord_341017) baseStart_341017 baseEnd_341017 := by
    simpa [prefixWord, tailWord_341017, baseEnd_341017] using wordTrace_append hprefix tailTrace_341017
  have hstable : (prefixWord ++ tailWord_341017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341017).length < 2 ^ (prefixWord ++ tailWord_341017).sum := by decide
  have hdescent : baseEnd_341017 < baseStart_341017 := by decide
  rcases family_descends (prefixWord ++ tailWord_341017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341081 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 4, 3, 2]
def baseStart_341081 : Nat := 118140960795 + 341081 * 2 ^ 59
def prefixEnd_341081 : Nat := 4983230072969 + 3 ^ 40 * 341081 * 2
def baseEnd_341081 : Nat := 175138495116285252718903

theorem tailTrace_341081 : CollatzResearch.WordTrace tailWord_341081 prefixEnd_341081 175138495116285252718903 := by
  unfold tailWord_341081
  simp only [CollatzResearch.WordTrace]
  refine ⟨12440246077329263842231097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8293497384886175894820731 12440246077329263842231097)
  ·
    refine ⟨9330184557996947881673323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12440246077329263842231097 9330184557996947881673323)
    ·
      refine ⟨13995276836995421822509985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9330184557996947881673323 13995276836995421822509985)
      ·
        refine ⟨10496457627746566366882489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13995276836995421822509985 10496457627746566366882489)
        ·
          refine ⟨7872343220809924775161867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10496457627746566366882489 7872343220809924775161867)
          ·
            refine ⟨11808514831214887162742801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7872343220809924775161867 11808514831214887162742801)
            ·
              refine ⟨8856386123411165372057101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11808514831214887162742801 8856386123411165372057101)
              ·
                refine ⟨3321144796279187014521413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8856386123411165372057101 3321144796279187014521413)
                ·
                  refine ⟨622714649302347565222765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3321144796279187014521413 622714649302347565222765)
                  ·
                    refine ⟨233517993488380336958537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 622714649302347565222765 233517993488380336958537)
                    ·
                      refine ⟨175138495116285252718903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233517993488380336958537 175138495116285252718903)
                      ·
                        rfl

theorem cell23_341081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 3, 2].length) (baseStart_341081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341081 prefixEnd_341081 := by exact prefixLift 341081
  have htrace : WordTrace (prefixWord ++ tailWord_341081) baseStart_341081 baseEnd_341081 := by
    simpa [prefixWord, tailWord_341081, baseEnd_341081] using wordTrace_append hprefix tailTrace_341081
  have hstable : (prefixWord ++ tailWord_341081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341081).length < 2 ^ (prefixWord ++ tailWord_341081).sum := by decide
  have hdescent : baseEnd_341081 < baseStart_341081 := by decide
  rcases family_descends (prefixWord ++ tailWord_341081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341111 : List Nat := [1, 1, 3, 1, 1, 4, 2, 4, 1, 1, 4]
def baseStart_341111 : Nat := 118140960795 + 341111 * 2 ^ 59
def prefixEnd_341111 : Nat := 4983230072969 + 3 ^ 40 * 341111 * 2
def baseEnd_341111 : Nat := 175153899535920135343765

theorem tailTrace_341111 : CollatzResearch.WordTrace tailWord_341111 prefixEnd_341111 175153899535920135343765 := by
  unfold tailWord_341111
  simp only [CollatzResearch.WordTrace]
  refine ⟨12441340267220578965823187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8294226844813719310548791 12441340267220578965823187)
  ·
    refine ⟨18662010400830868448734781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12441340267220578965823187 18662010400830868448734781)
    ·
      refine ⟨6998253900311575668275543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18662010400830868448734781 6998253900311575668275543)
      ·
        refine ⟨10497380850467363502413315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6998253900311575668275543 10497380850467363502413315)
        ·
          refine ⟨15746071275701045253619973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10497380850467363502413315 15746071275701045253619973)
          ·
            refine ⟨2952388364193945985053745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15746071275701045253619973 2952388364193945985053745)
            ·
              refine ⟨2214291273145459488790309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2952388364193945985053745 2214291273145459488790309)
              ·
                refine ⟨415179613714773654148183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2214291273145459488790309 415179613714773654148183)
                ·
                  refine ⟨622769420572160481222275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415179613714773654148183 622769420572160481222275)
                  ·
                    refine ⟨934154130858240721833413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 622769420572160481222275 934154130858240721833413)
                    ·
                      refine ⟨175153899535920135343765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 934154130858240721833413 175153899535920135343765)
                      ·
                        rfl

theorem cell23_341111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_341111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341111 prefixEnd_341111 := by exact prefixLift 341111
  have htrace : WordTrace (prefixWord ++ tailWord_341111) baseStart_341111 baseEnd_341111 := by
    simpa [prefixWord, tailWord_341111, baseEnd_341111] using wordTrace_append hprefix tailTrace_341111
  have hstable : (prefixWord ++ tailWord_341111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341111).length < 2 ^ (prefixWord ++ tailWord_341111).sum := by decide
  have hdescent : baseEnd_341111 < baseStart_341111 := by decide
  rcases family_descends (prefixWord ++ tailWord_341111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341121 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 1, 6]
def baseStart_341121 : Nat := 118140960795 + 341121 * 2 ^ 59
def prefixEnd_341121 : Nat := 4983230072969 + 3 ^ 40 * 341121 * 2
def baseEnd_341121 : Nat := 58386344780821698739573

theorem tailTrace_341121 : CollatzResearch.WordTrace tailWord_341121 prefixEnd_341121 58386344780821698739573 := by
  unfold tailWord_341121
  simp only [CollatzResearch.WordTrace]
  refine ⟨12441704997184350673687217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8294469998122900449124811 12441704997184350673687217)
  ·
    refine ⟨9331278747888263005265413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12441704997184350673687217 9331278747888263005265413)
    ·
      refine ⟨1749614765229049313487265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9331278747888263005265413 1749614765229049313487265)
      ·
        refine ⟨1312211073921786985115449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1749614765229049313487265 1312211073921786985115449)
        ·
          refine ⟨984158305441340238836587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1312211073921786985115449 984158305441340238836587)
          ·
            refine ⟨1476237458162010358254881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984158305441340238836587 1476237458162010358254881)
            ·
              refine ⟨1107178093621507768691161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476237458162010358254881 1107178093621507768691161)
              ·
                refine ⟨830383570216130826518371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1107178093621507768691161 830383570216130826518371)
                ·
                  refine ⟨1245575355324196239777557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 830383570216130826518371 1245575355324196239777557)
                  ·
                    refine ⟨58386344780821698739573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1245575355324196239777557 58386344780821698739573)
                    ·
                      rfl

theorem cell23_341121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_341121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341121 prefixEnd_341121 := by exact prefixLift 341121
  have htrace : WordTrace (prefixWord ++ tailWord_341121) baseStart_341121 baseEnd_341121 := by
    simpa [prefixWord, tailWord_341121, baseEnd_341121] using wordTrace_append hprefix tailTrace_341121
  have hstable : (prefixWord ++ tailWord_341121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341121).length < 2 ^ (prefixWord ++ tailWord_341121).sum := by decide
  have hdescent : baseEnd_341121 < baseStart_341121 := by decide
  rcases family_descends (prefixWord ++ tailWord_341121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341125 : List Nat := [1, 3, 1, 1, 6, 2, 2, 1, 1, 5]
def baseStart_341125 : Nat := 118140960795 + 341125 * 2 ^ 59
def prefixEnd_341125 : Nat := 4983230072969 + 3 ^ 40 * 341125 * 2
def baseEnd_341125 : Nat := 58387029421694360189567

theorem tailTrace_341125 : CollatzResearch.WordTrace tailWord_341125 prefixEnd_341125 58387029421694360189567 := by
  unfold tailWord_341125
  simp only [CollatzResearch.WordTrace]
  refine ⟨12441850889169859356832829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8294567259446572904555219 12441850889169859356832829)
  ·
    refine ⟨4665694083438697258812311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12441850889169859356832829 4665694083438697258812311)
    ·
      refine ⟨6998541125158045888218467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4665694083438697258812311 6998541125158045888218467)
      ·
        refine ⟨10497811687737068832327701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6998541125158045888218467 10497811687737068832327701)
        ·
          refine ⟨492084922862675101515361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10497811687737068832327701 492084922862675101515361)
          ·
            refine ⟨369063692147006326136521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492084922862675101515361 369063692147006326136521)
            ·
              refine ⟨276797769110254744602391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369063692147006326136521 276797769110254744602391)
              ·
                refine ⟨415196653665382116903587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276797769110254744602391 415196653665382116903587)
                ·
                  refine ⟨622794980498073175355381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415196653665382116903587 622794980498073175355381)
                  ·
                    refine ⟨58387029421694360189567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 622794980498073175355381 58387029421694360189567)
                    ·
                      rfl

theorem cell23_341125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_341125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341125 prefixEnd_341125 := by exact prefixLift 341125
  have htrace : WordTrace (prefixWord ++ tailWord_341125) baseStart_341125 baseEnd_341125 := by
    simpa [prefixWord, tailWord_341125, baseEnd_341125] using wordTrace_append hprefix tailTrace_341125
  have hstable : (prefixWord ++ tailWord_341125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341125).length < 2 ^ (prefixWord ++ tailWord_341125).sum := by decide
  have hdescent : baseEnd_341125 < baseStart_341125 := by decide
  rcases family_descends (prefixWord ++ tailWord_341125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341138 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_341138 : Nat := 118140960795 + 341138 * 2 ^ 59
def prefixEnd_341138 : Nat := 4983230072969 + 3 ^ 40 * 341138 * 2
def baseEnd_341138 : Nat := 58389254504530509902047

theorem tailTrace_341138 : CollatzResearch.WordTrace tailWord_341138 prefixEnd_341138 58389254504530509902047 := by
  unfold tailWord_341138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3110581259530690644264017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8294883358748508384704045 3110581259530690644264017)
  ·
    refine ⟨2332935944648017983198013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3110581259530690644264017 2332935944648017983198013)
    ·
      refine ⟨874850979243006743699255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2332935944648017983198013 874850979243006743699255)
      ·
        refine ⟨1312276468864510115548883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874850979243006743699255 1312276468864510115548883)
        ·
          refine ⟨1968414703296765173323325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312276468864510115548883 1968414703296765173323325)
          ·
            refine ⟨738155513736286939996247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1968414703296765173323325 738155513736286939996247)
            ·
              refine ⟨1107233270604430409994371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738155513736286939996247 1107233270604430409994371)
              ·
                refine ⟨1660849905906645614991557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107233270604430409994371 1660849905906645614991557)
                ·
                  refine ⟨311409357357496052810917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1660849905906645614991557 311409357357496052810917)
                  ·
                    refine ⟨58389254504530509902047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 311409357357496052810917 58389254504530509902047)
                    ·
                      rfl

theorem cell23_341138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_341138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341138 prefixEnd_341138 := by exact prefixLift 341138
  have htrace : WordTrace (prefixWord ++ tailWord_341138) baseStart_341138 baseEnd_341138 := by
    simpa [prefixWord, tailWord_341138, baseEnd_341138] using wordTrace_append hprefix tailTrace_341138
  have hstable : (prefixWord ++ tailWord_341138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341138).length < 2 ^ (prefixWord ++ tailWord_341138).sum := by decide
  have hdescent : baseEnd_341138 < baseStart_341138 := by decide
  rcases family_descends (prefixWord ++ tailWord_341138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341162 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_341162 : Nat := 118140960795 + 341162 * 2 ^ 59
def prefixEnd_341162 : Nat := 4983230072969 + 3 ^ 40 * 341162 * 2
def baseEnd_341162 : Nat := 175180087049299435806031

theorem tailTrace_341162 : CollatzResearch.WordTrace tailWord_341162 prefixEnd_341162 175180087049299435806031 := by
  unfold tailWord_341162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3110800097508953668982435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8295466926690543117286493 3110800097508953668982435)
  ·
    refine ⟨4666200146263430503473653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3110800097508953668982435 4666200146263430503473653)
    ·
      refine ⟨437456263712196609700655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4666200146263430503473653 437456263712196609700655)
      ·
        refine ⟨656184395568294914550983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437456263712196609700655 656184395568294914550983)
        ·
          refine ⟨984276593352442371826475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656184395568294914550983 984276593352442371826475)
          ·
            refine ⟨1476414890028663557739713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984276593352442371826475 1476414890028663557739713)
            ·
              refine ⟨1107311167521497668304785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476414890028663557739713 1107311167521497668304785)
              ·
                refine ⟨830483375641123251228589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1107311167521497668304785 830483375641123251228589)
                ·
                  refine ⟨311431265865421219210721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 830483375641123251228589 311431265865421219210721)
                  ·
                    refine ⟨233573449399065914408041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 311431265865421219210721 233573449399065914408041)
                    ·
                      refine ⟨175180087049299435806031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233573449399065914408041 175180087049299435806031)
                      ·
                        rfl

theorem cell23_341162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_341162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341162 prefixEnd_341162 := by exact prefixLift 341162
  have htrace : WordTrace (prefixWord ++ tailWord_341162) baseStart_341162 baseEnd_341162 := by
    simpa [prefixWord, tailWord_341162, baseEnd_341162] using wordTrace_append hprefix tailTrace_341162
  have hstable : (prefixWord ++ tailWord_341162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341162).length < 2 ^ (prefixWord ++ tailWord_341162).sum := by decide
  have hdescent : baseEnd_341162 < baseStart_341162 := by decide
  rcases family_descends (prefixWord ++ tailWord_341162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341206 : List Nat := [5, 2, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_341206 : Nat := 118140960795 + 341206 * 2 ^ 59
def prefixEnd_341206 : Nat := 4983230072969 + 3 ^ 40 * 341206 * 2
def baseEnd_341206 : Nat := 58400893399365754551943

theorem tailTrace_341206 : CollatzResearch.WordTrace tailWord_341206 prefixEnd_341206 58400893399365754551943 := by
  unfold tailWord_341206
  simp only [CollatzResearch.WordTrace]
  refine ⟨777800325117275636908217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8296536801250940127020981 777800325117275636908217)
  ·
    refine ⟨583350243837956727681163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 777800325117275636908217 583350243837956727681163)
    ·
      refine ⟨875025365756935091521745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 583350243837956727681163 875025365756935091521745)
      ·
        refine ⟨656269024317701318641309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 875025365756935091521745 656269024317701318641309)
        ·
          refine ⟨246100884119137994490491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 656269024317701318641309 246100884119137994490491)
          ·
            refine ⟨369151326178706991735737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246100884119137994490491 369151326178706991735737)
            ·
              refine ⟨276863494634030243801803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369151326178706991735737 276863494634030243801803)
              ·
                refine ⟨415295241951045365702705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276863494634030243801803 415295241951045365702705)
                ·
                  refine ⟨311471431463284024277029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415295241951045365702705 311471431463284024277029)
                  ·
                    refine ⟨58400893399365754551943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 311471431463284024277029 58400893399365754551943)
                    ·
                      rfl

theorem cell23_341206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_341206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341206 prefixEnd_341206 := by exact prefixLift 341206
  have htrace : WordTrace (prefixWord ++ tailWord_341206) baseStart_341206 baseEnd_341206 := by
    simpa [prefixWord, tailWord_341206, baseEnd_341206] using wordTrace_append hprefix tailTrace_341206
  have hstable : (prefixWord ++ tailWord_341206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341206).length < 2 ^ (prefixWord ++ tailWord_341206).sum := by decide
  have hdescent : baseEnd_341206 < baseStart_341206 := by decide
  rcases family_descends (prefixWord ++ tailWord_341206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341252 : List Nat := [2, 3, 2, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_341252 : Nat := 118140960795 + 341252 * 2 ^ 59
def prefixEnd_341252 : Nat := 4983230072969 + 3 ^ 40 * 341252 * 2
def baseEnd_341252 : Nat := 175226300308204083680617

theorem tailTrace_341252 : CollatzResearch.WordTrace tailWord_341252 prefixEnd_341252 175226300308204083680617 := by
  unfold tailWord_341252
  simp only [CollatzResearch.WordTrace]
  refine ⟨6223241479854880023353005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8297655306473173364470673 6223241479854880023353005)
  ·
    refine ⟨2333715554945580008757377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6223241479854880023353005 2333715554945580008757377)
    ·
      refine ⟨1750286666209185006568033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2333715554945580008757377 1750286666209185006568033)
      ·
        refine ⟨1312714999656888754926025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1750286666209185006568033 1312714999656888754926025)
        ·
          refine ⟨984536249742666566194519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1312714999656888754926025 984536249742666566194519)
          ·
            refine ⟨1476804374613999849291779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984536249742666566194519 1476804374613999849291779)
            ·
              refine ⟨2215206561920999773937669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476804374613999849291779 2215206561920999773937669)
              ·
                refine ⟨415351230360187457613313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2215206561920999773937669 415351230360187457613313)
                ·
                  refine ⟨311513422770140593209985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415351230360187457613313 311513422770140593209985)
                  ·
                    refine ⟨233635067077605444907489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 311513422770140593209985 233635067077605444907489)
                    ·
                      refine ⟨175226300308204083680617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233635067077605444907489 175226300308204083680617)
                      ·
                        rfl

theorem cell23_341252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_341252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341252 prefixEnd_341252 := by exact prefixLift 341252
  have htrace : WordTrace (prefixWord ++ tailWord_341252) baseStart_341252 baseEnd_341252 := by
    simpa [prefixWord, tailWord_341252, baseEnd_341252] using wordTrace_append hprefix tailTrace_341252
  have hstable : (prefixWord ++ tailWord_341252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341252).length < 2 ^ (prefixWord ++ tailWord_341252).sum := by decide
  have hdescent : baseEnd_341252 < baseStart_341252 := by decide
  rcases family_descends (prefixWord ++ tailWord_341252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341271 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 1, 7]
def baseStart_341271 : Nat := 118140960795 + 341271 * 2 ^ 59
def prefixEnd_341271 : Nat := 4983230072969 + 3 ^ 40 * 341271 * 2
def baseEnd_341271 : Nat := 58412018813546503114343

theorem tailTrace_341271 : CollatzResearch.WordTrace tailWord_341271 prefixEnd_341271 58412018813546503114343 := by
  unfold tailWord_341271
  simp only [CollatzResearch.WordTrace]
  refine ⟨12447175946640926291647667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8298117297760617527765111 12447175946640926291647667)
  ·
    refine ⟨18670763919961389437471501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12447175946640926291647667 18670763919961389437471501)
    ·
      refine ⟨7001536469985521039051813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18670763919961389437471501 7001536469985521039051813)
      ·
        refine ⟨1312788088122285194822215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7001536469985521039051813 1312788088122285194822215)
        ·
          refine ⟨1969182132183427792233323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312788088122285194822215 1969182132183427792233323)
          ·
            refine ⟨2953773198275141688349985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969182132183427792233323 2953773198275141688349985)
            ·
              refine ⟨2215329898706356266262489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2953773198275141688349985 2215329898706356266262489)
              ·
                refine ⟨1661497424029767199696867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2215329898706356266262489 1661497424029767199696867)
                ·
                  refine ⟨2492246136044650799545301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1661497424029767199696867 2492246136044650799545301)
                  ·
                    refine ⟨58412018813546503114343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2492246136044650799545301 58412018813546503114343)
                    ·
                      rfl

theorem cell23_341271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_341271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341271 prefixEnd_341271 := by exact prefixLift 341271
  have htrace : WordTrace (prefixWord ++ tailWord_341271) baseStart_341271 baseEnd_341271 := by
    simpa [prefixWord, tailWord_341271, baseEnd_341271] using wordTrace_append hprefix tailTrace_341271
  have hstable : (prefixWord ++ tailWord_341271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341271).length < 2 ^ (prefixWord ++ tailWord_341271).sum := by decide
  have hdescent : baseEnd_341271 < baseStart_341271 := by decide
  rcases family_descends (prefixWord ++ tailWord_341271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341288 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 1, 7]
def baseStart_341288 : Nat := 118140960795 + 341288 * 2 ^ 59
def prefixEnd_341288 : Nat := 4983230072969 + 3 ^ 40 * 341288 * 2
def baseEnd_341288 : Nat := 58414928537255314276817

theorem tailTrace_341288 : CollatzResearch.WordTrace tailWord_341288 prefixEnd_341288 58414928537255314276817 := by
  unfold tailWord_341288
  simp only [CollatzResearch.WordTrace]
  refine ⟨6223897993789669097508259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8298530658386225463344345 6223897993789669097508259)
  ·
    refine ⟨9335846990684503646262389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6223897993789669097508259 9335846990684503646262389)
    ·
      refine ⟨875235655376672216837099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9335846990684503646262389 875235655376672216837099)
      ·
        refine ⟨1312853483065008325255649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 875235655376672216837099 1312853483065008325255649)
        ·
          refine ⟨984640112298756243941737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1312853483065008325255649 984640112298756243941737)
          ·
            refine ⟨738480084224067182956303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 984640112298756243941737 738480084224067182956303)
            ·
              refine ⟨1107720126336100774434455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738480084224067182956303 1107720126336100774434455)
              ·
                refine ⟨1661580189504151161651683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107720126336100774434455 1661580189504151161651683)
                ·
                  refine ⟨2492370284256226742477525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1661580189504151161651683 2492370284256226742477525)
                  ·
                    refine ⟨58414928537255314276817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2492370284256226742477525 58414928537255314276817)
                    ·
                      rfl

theorem cell23_341288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_341288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341288 prefixEnd_341288 := by exact prefixLift 341288
  have htrace : WordTrace (prefixWord ++ tailWord_341288) baseStart_341288 baseEnd_341288 := by
    simpa [prefixWord, tailWord_341288, baseEnd_341288] using wordTrace_append hprefix tailTrace_341288
  have hstable : (prefixWord ++ tailWord_341288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341288).length < 2 ^ (prefixWord ++ tailWord_341288).sum := by decide
  have hdescent : baseEnd_341288 < baseStart_341288 := by decide
  rcases family_descends (prefixWord ++ tailWord_341288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341291 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 4]
def baseStart_341291 : Nat := 118140960795 + 341291 * 2 ^ 59
def prefixEnd_341291 : Nat := 4983230072969 + 3 ^ 40 * 341291 * 2
def baseEnd_341291 : Nat := 175246326053729431092937

theorem tailTrace_341291 : CollatzResearch.WordTrace tailWord_341291 prefixEnd_341291 175246326053729431092937 := by
  unfold tailWord_341291
  simp only [CollatzResearch.WordTrace]
  refine ⟨12447905406568469707375727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8298603604378979804917151 12447905406568469707375727)
  ·
    refine ⟨18671858109852704561063591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12447905406568469707375727 18671858109852704561063591)
    ·
      refine ⟨28007787164779056841595387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18671858109852704561063591 28007787164779056841595387)
      ·
        refine ⟨42011680747168585262393081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28007787164779056841595387 42011680747168585262393081)
        ·
          refine ⟨31508760560376438946794811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42011680747168585262393081 31508760560376438946794811)
          ·
            refine ⟨47263140840564658420192217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31508760560376438946794811 47263140840564658420192217)
            ·
              refine ⟨35447355630423493815144163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47263140840564658420192217 35447355630423493815144163)
              ·
                refine ⟨53171033445635240722716245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35447355630423493815144163 53171033445635240722716245)
                ·
                  refine ⟨623098048191037977219331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 53171033445635240722716245 623098048191037977219331)
                  ·
                    refine ⟨934647072286556965828997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 623098048191037977219331 934647072286556965828997)
                    ·
                      refine ⟨175246326053729431092937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 934647072286556965828997 175246326053729431092937)
                      ·
                        rfl

theorem cell23_341291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 1, 4].length) (baseStart_341291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341291 prefixEnd_341291 := by exact prefixLift 341291
  have htrace : WordTrace (prefixWord ++ tailWord_341291) baseStart_341291 baseEnd_341291 := by
    simpa [prefixWord, tailWord_341291, baseEnd_341291] using wordTrace_append hprefix tailTrace_341291
  have hstable : (prefixWord ++ tailWord_341291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341291).length < 2 ^ (prefixWord ++ tailWord_341291).sum := by decide
  have hdescent : baseEnd_341291 < baseStart_341291 := by decide
  rcases family_descends (prefixWord ++ tailWord_341291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341368 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 2, 9, 2]
def baseStart_341368 : Nat := 118140960795 + 341368 * 2 ^ 59
def prefixEnd_341368 : Nat := 4983230072969 + 3 ^ 40 * 341368 * 2
def baseEnd_341368 : Nat := 175285864064125629830083

theorem tailTrace_341368 : CollatzResearch.WordTrace tailWord_341368 prefixEnd_341368 175285864064125629830083 := by
  unfold tailWord_341368
  simp only [CollatzResearch.WordTrace]
  refine ⟨6225356913644755928964379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8300475884859674571952505 6225356913644755928964379)
  ·
    refine ⟨9338035370467133893446569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6225356913644755928964379 9338035370467133893446569)
    ·
      refine ⟨7003526527850350420084927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9338035370467133893446569 7003526527850350420084927)
      ·
        refine ⟨10505289791775525630127391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7003526527850350420084927 10505289791775525630127391)
        ·
          refine ⟨15757934687663288445191087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10505289791775525630127391 15757934687663288445191087)
          ·
            refine ⟨23636902031494932667786631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15757934687663288445191087 23636902031494932667786631)
            ·
              refine ⟨35455353047242399001679947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23636902031494932667786631 35455353047242399001679947)
              ·
                refine ⟨53183029570863598502519921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35455353047242399001679947 53183029570863598502519921)
                ·
                  refine ⟨39887272178147698876889941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53183029570863598502519921 39887272178147698876889941)
                  ·
                    refine ⟨233714485418834173106777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 39887272178147698876889941 233714485418834173106777)
                    ·
                      refine ⟨175285864064125629830083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233714485418834173106777 175285864064125629830083)
                      ·
                        rfl

theorem cell23_341368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 9, 2].length) (baseStart_341368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341368 prefixEnd_341368 := by exact prefixLift 341368
  have htrace : WordTrace (prefixWord ++ tailWord_341368) baseStart_341368 baseEnd_341368 := by
    simpa [prefixWord, tailWord_341368, baseEnd_341368] using wordTrace_append hprefix tailTrace_341368
  have hstable : (prefixWord ++ tailWord_341368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341368).length < 2 ^ (prefixWord ++ tailWord_341368).sum := by decide
  have hdescent : baseEnd_341368 < baseStart_341368 := by decide
  rcases family_descends (prefixWord ++ tailWord_341368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341402 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2]
def baseStart_341402 : Nat := 118140960795 + 341402 * 2 ^ 59
def prefixEnd_341402 : Nat := 4983230072969 + 3 ^ 40 * 341402 * 2
def baseEnd_341402 : Nat := 175303322406378496804927

theorem tailTrace_341402 : CollatzResearch.WordTrace tailWord_341402 prefixEnd_341402 175303322406378496804927 := by
  unfold tailWord_341402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3112988477291583916166615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8301302606110890443110973 3112988477291583916166615)
  ·
    refine ⟨4669482715937375874249923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3112988477291583916166615 4669482715937375874249923)
    ·
      refine ⟨7004224073906063811374885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4669482715937375874249923 7004224073906063811374885)
      ·
        refine ⟨1313292013857386964632791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7004224073906063811374885 1313292013857386964632791)
        ·
          refine ⟨1969938020786080446949187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313292013857386964632791 1969938020786080446949187)
          ·
            refine ⟨2954907031179120670423781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969938020786080446949187 2954907031179120670423781)
            ·
              refine ⟨554045068346085125704459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2954907031179120670423781 554045068346085125704459)
              ·
                refine ⟨831067602519127688556689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554045068346085125704459 831067602519127688556689)
                ·
                  refine ⟨623300701889345766417517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 831067602519127688556689 623300701889345766417517)
                  ·
                    refine ⟨233737763208504662406569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 623300701889345766417517 233737763208504662406569)
                    ·
                      refine ⟨175303322406378496804927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233737763208504662406569 175303322406378496804927)
                      ·
                        rfl

theorem cell23_341402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_341402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341402 prefixEnd_341402 := by exact prefixLift 341402
  have htrace : WordTrace (prefixWord ++ tailWord_341402) baseStart_341402 baseEnd_341402 := by
    simpa [prefixWord, tailWord_341402, baseEnd_341402] using wordTrace_append hprefix tailTrace_341402
  have hstable : (prefixWord ++ tailWord_341402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341402).length < 2 ^ (prefixWord ++ tailWord_341402).sum := by decide
  have hdescent : baseEnd_341402 < baseStart_341402 := by decide
  rcases family_descends (prefixWord ++ tailWord_341402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341408 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 1, 6]
def baseStart_341408 : Nat := 118140960795 + 341408 * 2 ^ 59
def prefixEnd_341408 : Nat := 4983230072969 + 3 ^ 40 * 341408 * 2
def baseEnd_341408 : Nat := 58435467763435157776633

theorem tailTrace_341408 : CollatzResearch.WordTrace tailWord_341408 prefixEnd_341408 58435467763435157776633 := by
  unfold tailWord_341408
  simp only [CollatzResearch.WordTrace]
  refine ⟨6226086373572299344692439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8301448498096399126256585 6226086373572299344692439)
  ·
    refine ⟨9339129560358449017038659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6226086373572299344692439 9339129560358449017038659)
    ·
      refine ⟨14008694340537673525557989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9339129560358449017038659 14008694340537673525557989)
      ·
        refine ⟨2626630188850813786042123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14008694340537673525557989 2626630188850813786042123)
        ·
          refine ⟨3939945283276220679063185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2626630188850813786042123 3939945283276220679063185)
          ·
            refine ⟨2954958962457165509297389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3939945283276220679063185 2954958962457165509297389)
            ·
              refine ⟨1108109610921437065986521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2954958962457165509297389 1108109610921437065986521)
              ·
                refine ⟨831082208191077799489891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1108109610921437065986521 831082208191077799489891)
                ·
                  refine ⟨1246623312286616699234837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831082208191077799489891 1246623312286616699234837)
                  ·
                    refine ⟨58435467763435157776633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1246623312286616699234837 58435467763435157776633)
                    ·
                      rfl

theorem cell23_341408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 1, 6].length) (baseStart_341408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341408 prefixEnd_341408 := by exact prefixLift 341408
  have htrace : WordTrace (prefixWord ++ tailWord_341408) baseStart_341408 baseEnd_341408 := by
    simpa [prefixWord, tailWord_341408, baseEnd_341408] using wordTrace_append hprefix tailTrace_341408
  have hstable : (prefixWord ++ tailWord_341408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341408).length < 2 ^ (prefixWord ++ tailWord_341408).sum := by decide
  have hdescent : baseEnd_341408 < baseStart_341408 := by decide
  rcases family_descends (prefixWord ++ tailWord_341408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341462 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_341462 : Nat := 118140960795 + 341462 * 2 ^ 59
def prefixEnd_341462 : Nat := 4983230072969 + 3 ^ 40 * 341462 * 2
def baseEnd_341462 : Nat := 175334131245648262054651

theorem tailTrace_341462 : CollatzResearch.WordTrace tailWord_341462 prefixEnd_341462 175334131245648262054651 := by
  unfold tailWord_341462
  simp only [CollatzResearch.WordTrace]
  refine ⟨778383893059310369490665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8302761525965977274567093 778383893059310369490665)
  ·
    refine ⟨583787919794482777117999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 778383893059310369490665 583787919794482777117999)
    ·
      refine ⟨875681879691724165676999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 583787919794482777117999 875681879691724165676999)
      ·
        refine ⟨1313522819537586248515499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 875681879691724165676999 1313522819537586248515499)
        ·
          refine ⟨1970284229306379372773249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313522819537586248515499 1970284229306379372773249)
          ·
            refine ⟨1477713171979784529579937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970284229306379372773249 1477713171979784529579937)
            ·
              refine ⟨1108284878984838397184953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477713171979784529579937 1108284878984838397184953)
              ·
                refine ⟨831213659238628797888715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1108284878984838397184953 831213659238628797888715)
                ·
                  refine ⟨1246820488857943196833073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831213659238628797888715 1246820488857943196833073)
                  ·
                    refine ⟨935115366643457397624805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1246820488857943196833073 935115366643457397624805)
                    ·
                      refine ⟨175334131245648262054651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 935115366643457397624805 175334131245648262054651)
                      ·
                        rfl

theorem cell23_341462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_341462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341462 prefixEnd_341462 := by exact prefixLift 341462
  have htrace : WordTrace (prefixWord ++ tailWord_341462) baseStart_341462 baseEnd_341462 := by
    simpa [prefixWord, tailWord_341462, baseEnd_341462] using wordTrace_append hprefix tailTrace_341462
  have hstable : (prefixWord ++ tailWord_341462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341462).length < 2 ^ (prefixWord ++ tailWord_341462).sum := by decide
  have hdescent : baseEnd_341462 < baseStart_341462 := by decide
  rcases family_descends (prefixWord ++ tailWord_341462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341465 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 1, 3, 3]
def baseStart_341465 : Nat := 118140960795 + 341465 * 2 ^ 59
def prefixEnd_341465 : Nat := 4983230072969 + 3 ^ 40 * 341465 * 2
def baseEnd_341465 : Nat := 175335671687611750317137

theorem tailTrace_341465 : CollatzResearch.WordTrace tailWord_341465 prefixEnd_341465 175335671687611750317137 := by
  unfold tailWord_341465
  simp only [CollatzResearch.WordTrace]
  refine ⟨12454251707938097424209849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8302834471958731616139899 12454251707938097424209849)
  ·
    refine ⟨9340688780953573068157387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12454251707938097424209849 9340688780953573068157387)
    ·
      refine ⟨14011033171430359602236081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9340688780953573068157387 14011033171430359602236081)
      ·
        refine ⟨10508274878572769701677061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14011033171430359602236081 10508274878572769701677061)
        ·
          refine ⟨1970301539732394319064449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10508274878572769701677061 1970301539732394319064449)
          ·
            refine ⟨1477726154799295739298337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970301539732394319064449 1477726154799295739298337)
            ·
              refine ⟨1108294616099471804473753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477726154799295739298337 1108294616099471804473753)
              ·
                refine ⟨831220962074603853355315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1108294616099471804473753 831220962074603853355315)
                ·
                  refine ⟨1246831443111905780032973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831220962074603853355315 1246831443111905780032973)
                  ·
                    refine ⟨467561791166964667512365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1246831443111905780032973 467561791166964667512365)
                    ·
                      refine ⟨175335671687611750317137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 467561791166964667512365 175335671687611750317137)
                      ·
                        rfl

theorem cell23_341465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_341465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341465 prefixEnd_341465 := by exact prefixLift 341465
  have htrace : WordTrace (prefixWord ++ tailWord_341465) baseStart_341465 baseEnd_341465 := by
    simpa [prefixWord, tailWord_341465, baseEnd_341465] using wordTrace_append hprefix tailTrace_341465
  have hstable : (prefixWord ++ tailWord_341465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341465).length < 2 ^ (prefixWord ++ tailWord_341465).sum := by decide
  have hdescent : baseEnd_341465 < baseStart_341465 := by decide
  rcases family_descends (prefixWord ++ tailWord_341465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341466 : List Nat := [3, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2]
def baseStart_341466 : Nat := 118140960795 + 341466 * 2 ^ 59
def prefixEnd_341466 : Nat := 4983230072969 + 3 ^ 40 * 341466 * 2
def baseEnd_341466 : Nat := 175336185168266246404633

theorem tailTrace_341466 : CollatzResearch.WordTrace tailWord_341466 prefixEnd_341466 175336185168266246404633 := by
  unfold tailWord_341466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3113572045233618648749063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8302858787289649729997501 3113572045233618648749063)
  ·
    refine ⟨4670358067850427973123595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3113572045233618648749063 4670358067850427973123595)
    ·
      refine ⟨7005537101775641959685393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4670358067850427973123595 7005537101775641959685393)
      ·
        refine ⟨5254152826331731469764045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7005537101775641959685393 5254152826331731469764045)
        ·
          refine ⟨1970307309874399301161517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5254152826331731469764045 1970307309874399301161517)
          ·
            refine ⟨738865241202899737935569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1970307309874399301161517 738865241202899737935569)
            ·
              refine ⟨554148930902174803451677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738865241202899737935569 554148930902174803451677)
              ·
                refine ⟨207805849088315551294379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 554148930902174803451677 207805849088315551294379)
                ·
                  refine ⟨311708773632473326941569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207805849088315551294379 311708773632473326941569)
                  ·
                    refine ⟨233781580224354995206177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 311708773632473326941569 233781580224354995206177)
                    ·
                      refine ⟨175336185168266246404633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233781580224354995206177 175336185168266246404633)
                      ·
                        rfl

theorem cell23_341466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_341466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341466 prefixEnd_341466 := by exact prefixLift 341466
  have htrace : WordTrace (prefixWord ++ tailWord_341466) baseStart_341466 baseEnd_341466 := by
    simpa [prefixWord, tailWord_341466, baseEnd_341466] using wordTrace_append hprefix tailTrace_341466
  have hstable : (prefixWord ++ tailWord_341466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341466).length < 2 ^ (prefixWord ++ tailWord_341466).sum := by decide
  have hdescent : baseEnd_341466 < baseStart_341466 := by decide
  rcases family_descends (prefixWord ++ tailWord_341466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341469 : List Nat := [1, 4, 3, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_341469 : Nat := 118140960795 + 341469 * 2 ^ 59
def prefixEnd_341469 : Nat := 4983230072969 + 3 ^ 40 * 341469 * 2
def baseEnd_341469 : Nat := 175337725610229734667119

theorem tailTrace_341469 : CollatzResearch.WordTrace tailWord_341469 prefixEnd_341469 175337725610229734667119 := by
  unfold tailWord_341469
  simp only [CollatzResearch.WordTrace]
  refine ⟨12454397599923606107355461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8302931733282404071570307 12454397599923606107355461)
  ·
    refine ⟨2335199549985676145129149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12454397599923606107355461 2335199549985676145129149)
    ·
      refine ⟨875699831244628554423431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2335199549985676145129149 875699831244628554423431)
      ·
        refine ⟨1313549746866942831635147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 875699831244628554423431 1313549746866942831635147)
        ·
          refine ⟨1970324620300414247452721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313549746866942831635147 1970324620300414247452721)
          ·
            refine ⟨1477743465225310685589541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1970324620300414247452721 1477743465225310685589541)
            ·
              refine ⟨277076899729745753548039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1477743465225310685589541 277076899729745753548039)
              ·
                refine ⟨415615349594618630322059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277076899729745753548039 415615349594618630322059)
                ·
                  refine ⟨623423024391927945483089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415615349594618630322059 623423024391927945483089)
                  ·
                    refine ⟨467567268293945959112317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 623423024391927945483089 467567268293945959112317)
                    ·
                      refine ⟨175337725610229734667119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 467567268293945959112317 175337725610229734667119)
                      ·
                        rfl

theorem cell23_341469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_341469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341469 prefixEnd_341469 := by exact prefixLift 341469
  have htrace : WordTrace (prefixWord ++ tailWord_341469) baseStart_341469 baseEnd_341469 := by
    simpa [prefixWord, tailWord_341469, baseEnd_341469] using wordTrace_append hprefix tailTrace_341469
  have hstable : (prefixWord ++ tailWord_341469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341469).length < 2 ^ (prefixWord ++ tailWord_341469).sum := by decide
  have hdescent : baseEnd_341469 < baseStart_341469 := by decide
  rcases family_descends (prefixWord ++ tailWord_341469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341498 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 2, 6]
def baseStart_341498 : Nat := 118140960795 + 341498 * 2 ^ 59
def prefixEnd_341498 : Nat := 4983230072969 + 3 ^ 40 * 341498 * 2
def baseEnd_341498 : Nat := 58450872183070040401495

theorem tailTrace_341498 : CollatzResearch.WordTrace tailWord_341498 prefixEnd_341498 58450872183070040401495 := by
  unfold tailWord_341498
  simp only [CollatzResearch.WordTrace]
  refine ⟨3113863829204636015040287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8303636877879029373440765 3113863829204636015040287)
  ·
    refine ⟨4670795743806954022560431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3113863829204636015040287 4670795743806954022560431)
    ·
      refine ⟨7006193615710431033840647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4670795743806954022560431 7006193615710431033840647)
      ·
        refine ⟨10509290423565646550760971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7006193615710431033840647 10509290423565646550760971)
        ·
          refine ⟨15763935635348469826141457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10509290423565646550760971 15763935635348469826141457)
          ·
            refine ⟨11822951726511352369606093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15763935635348469826141457 11822951726511352369606093)
            ·
              refine ⟨4433606897441757138602285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11822951726511352369606093 4433606897441757138602285)
              ·
                refine ⟨1662602586540658926975857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4433606897441757138602285 1662602586540658926975857)
                ·
                  refine ⟨1246951939905494195231893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1662602586540658926975857 1246951939905494195231893)
                  ·
                    refine ⟨58450872183070040401495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1246951939905494195231893 58450872183070040401495)
                    ·
                      rfl

theorem cell23_341498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_341498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341498 prefixEnd_341498 := by exact prefixLift 341498
  have htrace : WordTrace (prefixWord ++ tailWord_341498) baseStart_341498 baseEnd_341498 := by
    simpa [prefixWord, tailWord_341498, baseEnd_341498] using wordTrace_append hprefix tailTrace_341498
  have hstable : (prefixWord ++ tailWord_341498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341498).length < 2 ^ (prefixWord ++ tailWord_341498).sum := by decide
  have hdescent : baseEnd_341498 < baseStart_341498 := by decide
  rcases family_descends (prefixWord ++ tailWord_341498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341517 : List Nat := [1, 7, 1, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_341517 : Nat := 118140960795 + 341517 * 2 ^ 59
def prefixEnd_341517 : Nat := 4983230072969 + 3 ^ 40 * 341517 * 2
def baseEnd_341517 : Nat := 175362372681645546866899

theorem tailTrace_341517 : CollatzResearch.WordTrace tailWord_341517 prefixEnd_341517 175362372681645546866899 := by
  unfold tailWord_341517
  simp only [CollatzResearch.WordTrace]
  refine ⟨12456148303749710305102805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8304098869166473536735203 12456148303749710305102805)
  ·
    refine ⟨291940975869133835275847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12456148303749710305102805 291940975869133835275847)
    ·
      refine ⟨437911463803700752913771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291940975869133835275847 437911463803700752913771)
      ·
        refine ⟨656867195705551129370657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437911463803700752913771 656867195705551129370657)
        ·
          refine ⟨492650396779163347027993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 656867195705551129370657 492650396779163347027993)
          ·
            refine ⟨369487797584372510270995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492650396779163347027993 369487797584372510270995)
            ·
              refine ⟨554231696376558765406493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369487797584372510270995 554231696376558765406493)
              ·
                refine ⟨207836886141209537027435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 554231696376558765406493 207836886141209537027435)
                ·
                  refine ⟨311755329211814305541153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207836886141209537027435 311755329211814305541153)
                  ·
                    refine ⟨233816496908860729155865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 311755329211814305541153 233816496908860729155865)
                    ·
                      refine ⟨175362372681645546866899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233816496908860729155865 175362372681645546866899)
                      ·
                        rfl

theorem cell23_341517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_341517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341517 prefixEnd_341517 := by exact prefixLift 341517
  have htrace : WordTrace (prefixWord ++ tailWord_341517) baseStart_341517 baseEnd_341517 := by
    simpa [prefixWord, tailWord_341517, baseEnd_341517] using wordTrace_append hprefix tailTrace_341517
  have hstable : (prefixWord ++ tailWord_341517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341517).length < 2 ^ (prefixWord ++ tailWord_341517).sum := by decide
  have hdescent : baseEnd_341517 < baseStart_341517 := by decide
  rcases family_descends (prefixWord ++ tailWord_341517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341525 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_341525 : Nat := 118140960795 + 341525 * 2 ^ 59
def prefixEnd_341525 : Nat := 4983230072969 + 3 ^ 40 * 341525 * 2
def baseEnd_341525 : Nat := 175366480526881515566861

theorem tailTrace_341525 : CollatzResearch.WordTrace tailWord_341525 prefixEnd_341525 175366480526881515566861 := by
  unfold tailWord_341525
  simp only [CollatzResearch.WordTrace]
  refine ⟨12456440087720727671394029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8304293391813818447596019 12456440087720727671394029)
  ·
    refine ⟨4671165032895272876772761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12456440087720727671394029 4671165032895272876772761)
    ·
      refine ⟨3503373774671454657579571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4671165032895272876772761 3503373774671454657579571)
      ·
        refine ⟨5255060662007181986369357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3503373774671454657579571 5255060662007181986369357)
        ·
          refine ⟨1970647748252693244888509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5255060662007181986369357 1970647748252693244888509)
          ·
            refine ⟨738992905594759966833191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1970647748252693244888509 738992905594759966833191)
            ·
              refine ⟨1108489358392139950249787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738992905594759966833191 1108489358392139950249787)
              ·
                refine ⟨1662734037588209925374681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1108489358392139950249787 1662734037588209925374681)
                ·
                  refine ⟨1247050528191157444031011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1662734037588209925374681 1247050528191157444031011)
                  ·
                    refine ⟨1870575792286736166046517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1247050528191157444031011 1870575792286736166046517)
                    ·
                      refine ⟨175366480526881515566861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1870575792286736166046517 175366480526881515566861)
                      ·
                        rfl

theorem cell23_341525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_341525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341525 prefixEnd_341525 := by exact prefixLift 341525
  have htrace : WordTrace (prefixWord ++ tailWord_341525) baseStart_341525 baseEnd_341525 := by
    simpa [prefixWord, tailWord_341525, baseEnd_341525] using wordTrace_append hprefix tailTrace_341525
  have hstable : (prefixWord ++ tailWord_341525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341525).length < 2 ^ (prefixWord ++ tailWord_341525).sum := by decide
  have hdescent : baseEnd_341525 < baseStart_341525 := by decide
  rcases family_descends (prefixWord ++ tailWord_341525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341534 : List Nat := [4, 3, 3, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_341534 : Nat := 118140960795 + 341534 * 2 ^ 59
def prefixEnd_341534 : Nat := 4983230072969 + 3 ^ 40 * 341534 * 2
def baseEnd_341534 : Nat := 175371101852771980354321

theorem tailTrace_341534 : CollatzResearch.WordTrace tailWord_341534 prefixEnd_341534 175371101852771980354321 := by
  unfold tailWord_341534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1557096043086015276058957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8304512229792081472314437 1557096043086015276058957)
  ·
    refine ⟨583911016157255728522109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1557096043086015276058957 583911016157255728522109)
    ·
      refine ⟨218966631058970898195791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 583911016157255728522109 218966631058970898195791)
      ·
        refine ⟨328449946588456347293687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218966631058970898195791 328449946588456347293687)
        ·
          refine ⟨492674919882684520940531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328449946588456347293687 492674919882684520940531)
          ·
            refine ⟨739012379824026781410797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492674919882684520940531 739012379824026781410797)
            ·
              refine ⟨277129642434010043029049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 739012379824026781410797 277129642434010043029049)
              ·
                refine ⟨207847231825507532271787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277129642434010043029049 207847231825507532271787)
                ·
                  refine ⟨311770847738261298407681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207847231825507532271787 311770847738261298407681)
                  ·
                    refine ⟨233828135803695973805761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 311770847738261298407681 233828135803695973805761)
                    ·
                      refine ⟨175371101852771980354321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233828135803695973805761 175371101852771980354321)
                      ·
                        rfl

theorem cell23_341534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_341534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341534 prefixEnd_341534 := by exact prefixLift 341534
  have htrace : WordTrace (prefixWord ++ tailWord_341534) baseStart_341534 baseEnd_341534 := by
    simpa [prefixWord, tailWord_341534, baseEnd_341534] using wordTrace_append hprefix tailTrace_341534
  have hstable : (prefixWord ++ tailWord_341534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341534).length < 2 ^ (prefixWord ++ tailWord_341534).sum := by decide
  have hdescent : baseEnd_341534 < baseStart_341534 := by decide
  rcases family_descends (prefixWord ++ tailWord_341534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341568 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 7]
def baseStart_341568 : Nat := 118140960795 + 341568 * 2 ^ 59
def prefixEnd_341568 : Nat := 4983230072969 + 3 ^ 40 * 341568 * 2
def baseEnd_341568 : Nat := 175388560195024847329163

theorem tailTrace_341568 : CollatzResearch.WordTrace tailWord_341568 prefixEnd_341568 175388560195024847329163 := by
  unfold tailWord_341568
  simp only [CollatzResearch.WordTrace]
  refine ⟨6229004213282473007604679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8305338951043297343472905 6229004213282473007604679)
  ·
    refine ⟨9343506319923709511407019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6229004213282473007604679 9343506319923709511407019)
    ·
      refine ⟨14015259479885564267110529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9343506319923709511407019 14015259479885564267110529)
      ·
        refine ⟨10511444609914173200332897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14015259479885564267110529 10511444609914173200332897)
        ·
          refine ⟨7883583457435629900249673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10511444609914173200332897 7883583457435629900249673)
          ·
            refine ⟨5912687593076722425187255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7883583457435629900249673 5912687593076722425187255)
            ·
              refine ⟨8869031389615083637780883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5912687593076722425187255 8869031389615083637780883)
              ·
                refine ⟨13303547084422625456671325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8869031389615083637780883 13303547084422625456671325)
                ·
                  refine ⟨4988830156658484546251747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13303547084422625456671325 4988830156658484546251747)
                  ·
                    refine ⟨7483245234987726819377621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4988830156658484546251747 7483245234987726819377621)
                    ·
                      refine ⟨175388560195024847329163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7483245234987726819377621 175388560195024847329163)
                      ·
                        rfl

theorem cell23_341568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_341568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341568 prefixEnd_341568 := by exact prefixLift 341568
  have htrace : WordTrace (prefixWord ++ tailWord_341568) baseStart_341568 baseEnd_341568 := by
    simpa [prefixWord, tailWord_341568, baseEnd_341568] using wordTrace_append hprefix tailTrace_341568
  have hstable : (prefixWord ++ tailWord_341568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341568).length < 2 ^ (prefixWord ++ tailWord_341568).sum := by decide
  have hdescent : baseEnd_341568 < baseStart_341568 := by decide
  rcases family_descends (prefixWord ++ tailWord_341568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341596 : List Nat := [2, 2, 4, 1, 2, 3, 2, 2, 5]
def baseStart_341596 : Nat := 118140960795 + 341596 * 2 ^ 59
def prefixEnd_341596 : Nat := 4983230072969 + 3 ^ 40 * 341596 * 2
def baseEnd_341596 : Nat := 19489215294816748642115

theorem tailTrace_341596 : CollatzResearch.WordTrace tailWord_341596 prefixEnd_341596 19489215294816748642115 := by
  unfold tailWord_341596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6229514835231753398614321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8306019780309004531485761 6229514835231753398614321)
  ·
    refine ⟨4672136126423815048960741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6229514835231753398614321 4672136126423815048960741)
    ·
      refine ⟨876025523704465321680139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4672136126423815048960741 876025523704465321680139)
      ·
        refine ⟨1314038285556697982520209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 876025523704465321680139 1314038285556697982520209)
        ·
          refine ⟨985528714167523486890157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1314038285556697982520209 985528714167523486890157)
          ·
            refine ⟨369573267812821307583809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 985528714167523486890157 369573267812821307583809)
            ·
              refine ⟨277179950859615980687857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369573267812821307583809 277179950859615980687857)
              ·
                refine ⟨207884963144711985515893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277179950859615980687857 207884963144711985515893)
                ·
                  refine ⟨19489215294816748642115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 207884963144711985515893 19489215294816748642115)
                  ·
                    rfl

theorem cell23_341596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 5].length) (baseStart_341596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341596 prefixEnd_341596 := by exact prefixLift 341596
  have htrace : WordTrace (prefixWord ++ tailWord_341596) baseStart_341596 baseEnd_341596 := by
    simpa [prefixWord, tailWord_341596, baseEnd_341596] using wordTrace_append hprefix tailTrace_341596
  have hstable : (prefixWord ++ tailWord_341596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341596).length < 2 ^ (prefixWord ++ tailWord_341596).sum := by decide
  have hdescent : baseEnd_341596 < baseStart_341596 := by decide
  rcases family_descends (prefixWord ++ tailWord_341596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341615 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 3]
def baseStart_341615 : Nat := 118140960795 + 341615 * 2 ^ 59
def prefixEnd_341615 : Nat := 4983230072969 + 3 ^ 40 * 341615 * 2
def baseEnd_341615 : Nat := 175412693785786163441447

theorem tailTrace_341615 : CollatzResearch.WordTrace tailWord_341615 prefixEnd_341615 175412693785786163441447 := by
  unfold tailWord_341615
  simp only [CollatzResearch.WordTrace]
  refine ⟨12459722657394673042170299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8306481771596448694780199 12459722657394673042170299)
  ·
    refine ⟨18689583986092009563255449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12459722657394673042170299 18689583986092009563255449)
    ·
      refine ⟨14017187989569007172441587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18689583986092009563255449 14017187989569007172441587)
      ·
        refine ⟨21025781984353510758662381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14017187989569007172441587 21025781984353510758662381)
        ·
          refine ⟨7884668244132566534498393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21025781984353510758662381 7884668244132566534498393)
          ·
            refine ⟨5913501183099424900873795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7884668244132566534498393 5913501183099424900873795)
            ·
              refine ⟨8870251774649137351310693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5913501183099424900873795 8870251774649137351310693)
              ·
                refine ⟨1663172207746713253370755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8870251774649137351310693 1663172207746713253370755)
                ·
                  refine ⟨2494758311620069880056133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1663172207746713253370755 2494758311620069880056133)
                  ·
                    refine ⟨467767183428763102510525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2494758311620069880056133 467767183428763102510525)
                    ·
                      refine ⟨175412693785786163441447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 467767183428763102510525 175412693785786163441447)
                      ·
                        rfl

theorem cell23_341615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 3].length) (baseStart_341615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341615 prefixEnd_341615 := by exact prefixLift 341615
  have htrace : WordTrace (prefixWord ++ tailWord_341615) baseStart_341615 baseEnd_341615 := by
    simpa [prefixWord, tailWord_341615, baseEnd_341615] using wordTrace_append hprefix tailTrace_341615
  have hstable : (prefixWord ++ tailWord_341615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341615).length < 2 ^ (prefixWord ++ tailWord_341615).sum := by decide
  have hdescent : baseEnd_341615 < baseStart_341615 := by decide
  rcases family_descends (prefixWord ++ tailWord_341615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341629 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 2, 1, 4]
def baseStart_341629 : Nat := 118140960795 + 341629 * 2 ^ 59
def prefixEnd_341629 : Nat := 4983230072969 + 3 ^ 40 * 341629 * 2
def baseEnd_341629 : Nat := 175419882514949108666383

theorem tailTrace_341629 : CollatzResearch.WordTrace tailWord_341629 prefixEnd_341629 175419882514949108666383 := by
  unfold tailWord_341629
  simp only [CollatzResearch.WordTrace]
  refine ⟨12460233279343953433179941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8306822186229302288786627 12460233279343953433179941)
  ·
    refine ⟨2336293739876991268721239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12460233279343953433179941 2336293739876991268721239)
    ·
      refine ⟨3504440609815486903081859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2336293739876991268721239 3504440609815486903081859)
      ·
        refine ⟨5256660914723230354622789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3504440609815486903081859 5256660914723230354622789)
        ·
          refine ⟨985623921510605691491773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5256660914723230354622789 985623921510605691491773)
          ·
            refine ⟨369608970566477134309415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 985623921510605691491773 369608970566477134309415)
            ·
              refine ⟨554413455849715701464123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369608970566477134309415 554413455849715701464123)
              ·
                refine ⟨831620183774573552196185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554413455849715701464123 831620183774573552196185)
                ·
                  refine ⟨623715137830930164147139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 831620183774573552196185 623715137830930164147139)
                  ·
                    refine ⟨935572706746395246220709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 623715137830930164147139 935572706746395246220709)
                    ·
                      refine ⟨175419882514949108666383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 935572706746395246220709 175419882514949108666383)
                      ·
                        rfl

theorem cell23_341629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_341629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341629 prefixEnd_341629 := by exact prefixLift 341629
  have htrace : WordTrace (prefixWord ++ tailWord_341629) baseStart_341629 baseEnd_341629 := by
    simpa [prefixWord, tailWord_341629, baseEnd_341629] using wordTrace_append hprefix tailTrace_341629
  have hstable : (prefixWord ++ tailWord_341629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341629).length < 2 ^ (prefixWord ++ tailWord_341629).sum := by decide
  have hdescent : baseEnd_341629 < baseStart_341629 := by decide
  rcases family_descends (prefixWord ++ tailWord_341629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341639 : List Nat := [1, 1, 4, 2, 1, 3, 1, 5, 1, 4]
def baseStart_341639 : Nat := 118140960795 + 341639 * 2 ^ 59
def prefixEnd_341639 : Nat := 4983230072969 + 3 ^ 40 * 341639 * 2
def baseEnd_341639 : Nat := 58475005773831356513779

theorem tailTrace_341639 : CollatzResearch.WordTrace tailWord_341639 prefixEnd_341639 58475005773831356513779 := by
  unfold tailWord_341639
  simp only [CollatzResearch.WordTrace]
  refine ⟨12460598009307725141043971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8307065339538483427362647 12460598009307725141043971)
  ·
    refine ⟨18690897013961587711565957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12460598009307725141043971 18690897013961587711565957)
    ·
      refine ⟨3504543190117797695918617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18690897013961587711565957 3504543190117797695918617)
      ·
        refine ⟨2628407392588348271938963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3504543190117797695918617 2628407392588348271938963)
        ·
          refine ⟨3942611088882522407908445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2628407392588348271938963 3942611088882522407908445)
          ·
            refine ⟨1478479158330945902965667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3942611088882522407908445 1478479158330945902965667)
            ·
              refine ⟨2217718737496418854448501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478479158330945902965667 2217718737496418854448501)
              ·
                refine ⟨207911131640289267604547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2217718737496418854448501 207911131640289267604547)
                ·
                  refine ⟨311866697460433901406821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207911131640289267604547 311866697460433901406821)
                  ·
                    refine ⟨58475005773831356513779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 311866697460433901406821 58475005773831356513779)
                    ·
                      rfl

theorem cell23_341639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_341639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341639 prefixEnd_341639 := by exact prefixLift 341639
  have htrace : WordTrace (prefixWord ++ tailWord_341639) baseStart_341639 baseEnd_341639 := by
    simpa [prefixWord, tailWord_341639, baseEnd_341639] using wordTrace_append hprefix tailTrace_341639
  have hstable : (prefixWord ++ tailWord_341639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341639).length < 2 ^ (prefixWord ++ tailWord_341639).sum := by decide
  have hdescent : baseEnd_341639 < baseStart_341639 := by decide
  rcases family_descends (prefixWord ++ tailWord_341639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341655 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_341655 : Nat := 118140960795 + 341655 * 2 ^ 59
def prefixEnd_341655 : Nat := 4983230072969 + 3 ^ 40 * 341655 * 2
def baseEnd_341655 : Nat := 175433233011966006941263

theorem tailTrace_341655 : CollatzResearch.WordTrace tailWord_341655 prefixEnd_341655 175433233011966006941263 := by
  unfold tailWord_341655
  simp only [CollatzResearch.WordTrace]
  refine ⟨12461181577249759873626419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8307454384833173249084279 12461181577249759873626419)
  ·
    refine ⟨18691772365874639810439629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12461181577249759873626419 18691772365874639810439629)
    ·
      refine ⟨7009414637202989928914861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18691772365874639810439629 7009414637202989928914861)
      ·
        refine ⟨2628530488951121223343073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7009414637202989928914861 2628530488951121223343073)
        ·
          refine ⟨1971397866713340917507305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2628530488951121223343073 1971397866713340917507305)
          ·
            refine ⟨1478548400035005688130479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1971397866713340917507305 1478548400035005688130479)
            ·
              refine ⟨2217822600052508532195719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1478548400035005688130479 2217822600052508532195719)
              ·
                refine ⟨3326733900078762798293579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2217822600052508532195719 3326733900078762798293579)
                ·
                  refine ⟨4990100850118144197440369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3326733900078762798293579 4990100850118144197440369)
                  ·
                    refine ⟨3742575637588608148080277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4990100850118144197440369 3742575637588608148080277)
                    ·
                      refine ⟨175433233011966006941263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3742575637588608148080277 175433233011966006941263)
                      ·
                        rfl

theorem cell23_341655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_341655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341655 prefixEnd_341655 := by exact prefixLift 341655
  have htrace : WordTrace (prefixWord ++ tailWord_341655) baseStart_341655 baseEnd_341655 := by
    simpa [prefixWord, tailWord_341655, baseEnd_341655] using wordTrace_append hprefix tailTrace_341655
  have hstable : (prefixWord ++ tailWord_341655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341655).length < 2 ^ (prefixWord ++ tailWord_341655).sum := by decide
  have hdescent : baseEnd_341655 < baseStart_341655 := by decide
  rcases family_descends (prefixWord ++ tailWord_341655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341682 : List Nat := [3, 2, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_341682 : Nat := 118140960795 + 341682 * 2 ^ 59
def prefixEnd_341682 : Nat := 4983230072969 + 3 ^ 40 * 341682 * 2
def baseEnd_341682 : Nat := 58482365663212467101213

theorem tailTrace_341682 : CollatzResearch.WordTrace tailWord_341682 prefixEnd_341682 58482365663212467101213 := by
  unfold tailWord_341682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3115541587037985871214825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8308110898767962323239533 3115541587037985871214825)
  ·
    refine ⟨2336656190278489403411119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3115541587037985871214825 2336656190278489403411119)
    ·
      refine ⟨3504984285417734105116679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2336656190278489403411119 3504984285417734105116679)
      ·
        refine ⟨5257476428126601157675019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3504984285417734105116679 5257476428126601157675019)
        ·
          refine ⟨7886214642189901736512529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5257476428126601157675019 7886214642189901736512529)
          ·
            refine ⟨5914660981642426302384397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7886214642189901736512529 5914660981642426302384397)
            ·
              refine ⟨2217997868115909863394149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5914660981642426302384397 2217997868115909863394149)
              ·
                refine ⟨415874600271733099386403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2217997868115909863394149 415874600271733099386403)
                ·
                  refine ⟨623811900407599649079605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415874600271733099386403 623811900407599649079605)
                  ·
                    refine ⟨58482365663212467101213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 623811900407599649079605 58482365663212467101213)
                    ·
                      rfl

theorem cell23_341682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_341682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341682 prefixEnd_341682 := by exact prefixLift 341682
  have htrace : WordTrace (prefixWord ++ tailWord_341682) baseStart_341682 baseEnd_341682 := by
    simpa [prefixWord, tailWord_341682, baseEnd_341682] using wordTrace_append hprefix tailTrace_341682
  have hstable : (prefixWord ++ tailWord_341682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341682).length < 2 ^ (prefixWord ++ tailWord_341682).sum := by decide
  have hdescent : baseEnd_341682 < baseStart_341682 := by decide
  rcases family_descends (prefixWord ++ tailWord_341682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341695 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 3, 6]
def baseStart_341695 : Nat := 118140960795 + 341695 * 2 ^ 59
def prefixEnd_341695 : Nat := 4983230072969 + 3 ^ 40 * 341695 * 2
def baseEnd_341695 : Nat := 58484590746048616813693

theorem tailTrace_341695 : CollatzResearch.WordTrace tailWord_341695 prefixEnd_341695 58484590746048616813693 := by
  unfold tailWord_341695
  simp only [CollatzResearch.WordTrace]
  refine ⟨12462640497104846705082539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8308426998069897803388359 12462640497104846705082539)
  ·
    refine ⟨18693960745657270057623809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12462640497104846705082539 18693960745657270057623809)
    ·
      refine ⟨14020470559242952543217857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18693960745657270057623809 14020470559242952543217857)
      ·
        refine ⟨10515352919432214407413393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14020470559242952543217857 10515352919432214407413393)
        ·
          refine ⟨7886514689574160805560045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10515352919432214407413393 7886514689574160805560045)
          ·
            refine ⟨2957443008590310302085017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7886514689574160805560045 2957443008590310302085017)
            ·
              refine ⟨2218082256442732726563763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2957443008590310302085017 2218082256442732726563763)
              ·
                refine ⟨3327123384664099089845645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2218082256442732726563763 3327123384664099089845645)
                ·
                  refine ⟨1247671269249037158692117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3327123384664099089845645 1247671269249037158692117)
                  ·
                    refine ⟨58484590746048616813693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1247671269249037158692117 58484590746048616813693)
                    ·
                      rfl

theorem cell23_341695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 6].length) (baseStart_341695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341695 prefixEnd_341695 := by exact prefixLift 341695
  have htrace : WordTrace (prefixWord ++ tailWord_341695) baseStart_341695 baseEnd_341695 := by
    simpa [prefixWord, tailWord_341695, baseEnd_341695] using wordTrace_append hprefix tailTrace_341695
  have hstable : (prefixWord ++ tailWord_341695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341695).length < 2 ^ (prefixWord ++ tailWord_341695).sum := by decide
  have hdescent : baseEnd_341695 < baseStart_341695 := by decide
  rcases family_descends (prefixWord ++ tailWord_341695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341706 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 2, 3, 2]
def baseStart_341706 : Nat := 118140960795 + 341706 * 2 ^ 59
def prefixEnd_341706 : Nat := 4983230072969 + 3 ^ 40 * 341706 * 2
def baseEnd_341706 : Nat := 175459420525345307403529

theorem tailTrace_341706 : CollatzResearch.WordTrace tailWord_341706 prefixEnd_341706 175459420525345307403529 := by
  unfold tailWord_341706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3115760425016248895933243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8308694466709997055821981 3115760425016248895933243)
  ·
    refine ⟨4673640637524373343899865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3115760425016248895933243 4673640637524373343899865)
    ·
      refine ⟨3505230478143280007924899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4673640637524373343899865 3505230478143280007924899)
      ·
        refine ⟨5257845717214920011887349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3505230478143280007924899 5257845717214920011887349)
        ·
          refine ⟨492923035988898751114439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5257845717214920011887349 492923035988898751114439)
          ·
            refine ⟨739384553983348126671659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492923035988898751114439 739384553983348126671659)
            ·
              refine ⟨1109076830975022190007489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739384553983348126671659 1109076830975022190007489)
              ·
                refine ⟨831807623231266642505617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1109076830975022190007489 831807623231266642505617)
                ·
                  refine ⟨623855717423449981879213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 831807623231266642505617 623855717423449981879213)
                  ·
                    refine ⟨233945894033793743204705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 623855717423449981879213 233945894033793743204705)
                    ·
                      refine ⟨175459420525345307403529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233945894033793743204705 175459420525345307403529)
                      ·
                        rfl

theorem cell23_341706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_341706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341706 prefixEnd_341706 := by exact prefixLift 341706
  have htrace : WordTrace (prefixWord ++ tailWord_341706) baseStart_341706 baseEnd_341706 := by
    simpa [prefixWord, tailWord_341706, baseEnd_341706] using wordTrace_append hprefix tailTrace_341706
  have hstable : (prefixWord ++ tailWord_341706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341706).length < 2 ^ (prefixWord ++ tailWord_341706).sum := by decide
  have hdescent : baseEnd_341706 < baseStart_341706 := by decide
  rcases family_descends (prefixWord ++ tailWord_341706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341713 : List Nat := [1, 2, 2, 1, 2, 5, 3, 2, 1, 1, 3]
def baseStart_341713 : Nat := 118140960795 + 341713 * 2 ^ 59
def prefixEnd_341713 : Nat := 4983230072969 + 3 ^ 40 * 341713 * 2
def baseEnd_341713 : Nat := 175463014889926780015997

theorem tailTrace_341713 : CollatzResearch.WordTrace tailWord_341713 prefixEnd_341713 175463014889926780015997 := by
  unfold tailWord_341713
  simp only [CollatzResearch.WordTrace]
  refine ⟨12463297011039635779237793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8308864674026423852825195 12463297011039635779237793)
  ·
    refine ⟨9347472758279726834428345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12463297011039635779237793 9347472758279726834428345)
    ·
      refine ⟨7010604568709795125821259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9347472758279726834428345 7010604568709795125821259)
      ·
        refine ⟨10515906853064692688731889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7010604568709795125821259 10515906853064692688731889)
        ·
          refine ⟨7886930139798519516548917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10515906853064692688731889 7886930139798519516548917)
          ·
            refine ⟨739399700606111204676461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7886930139798519516548917 739399700606111204676461)
            ·
              refine ⟨277274887727291701753673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 739399700606111204676461 277274887727291701753673)
              ·
                refine ⟨207956165795468776315255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277274887727291701753673 207956165795468776315255)
                ·
                  refine ⟨311934248693203164472883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207956165795468776315255 311934248693203164472883)
                  ·
                    refine ⟨467901373039804746709325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 311934248693203164472883 467901373039804746709325)
                    ·
                      refine ⟨175463014889926780015997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 467901373039804746709325 175463014889926780015997)
                      ·
                        rfl

theorem cell23_341713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 1, 1, 3].length) (baseStart_341713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341713 prefixEnd_341713 := by exact prefixLift 341713
  have htrace : WordTrace (prefixWord ++ tailWord_341713) baseStart_341713 baseEnd_341713 := by
    simpa [prefixWord, tailWord_341713, baseEnd_341713] using wordTrace_append hprefix tailTrace_341713
  have hstable : (prefixWord ++ tailWord_341713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341713).length < 2 ^ (prefixWord ++ tailWord_341713).sum := by decide
  have hdescent : baseEnd_341713 < baseStart_341713 := by decide
  rcases family_descends (prefixWord ++ tailWord_341713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341722 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5]
def baseStart_341722 : Nat := 118140960795 + 341722 * 2 ^ 59
def prefixEnd_341722 : Nat := 4983230072969 + 3 ^ 40 * 341722 * 2
def baseEnd_341722 : Nat := 175467636215817244803455

theorem tailTrace_341722 : CollatzResearch.WordTrace tailWord_341722 prefixEnd_341722 175467636215817244803455 := by
  unfold tailWord_341722
  simp only [CollatzResearch.WordTrace]
  refine ⟨3115906317001757579078855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8309083512004686877543613 3115906317001757579078855)
  ·
    refine ⟨4673859475502636368618283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3115906317001757579078855 4673859475502636368618283)
    ·
      refine ⟨7010789213253954552927425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4673859475502636368618283 7010789213253954552927425)
      ·
        refine ⟨5258091909940465914695569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7010789213253954552927425 5258091909940465914695569)
        ·
          refine ⟨3943568932455349436021677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5258091909940465914695569 3943568932455349436021677)
          ·
            refine ⟨1478838349670756038508129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3943568932455349436021677 1478838349670756038508129)
            ·
              refine ⟨1109128762253067028881097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1478838349670756038508129 1109128762253067028881097)
              ·
                refine ⟨831846571689800271660823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1109128762253067028881097 831846571689800271660823)
                ·
                  refine ⟨1247769857534700407491235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831846571689800271660823 1247769857534700407491235)
                  ·
                    refine ⟨1871654786302050611236853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1247769857534700407491235 1871654786302050611236853)
                    ·
                      refine ⟨175467636215817244803455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1871654786302050611236853 175467636215817244803455)
                      ·
                        rfl

theorem cell23_341722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_341722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341722 prefixEnd_341722 := by exact prefixLift 341722
  have htrace : WordTrace (prefixWord ++ tailWord_341722) baseStart_341722 baseEnd_341722 := by
    simpa [prefixWord, tailWord_341722, baseEnd_341722] using wordTrace_append hprefix tailTrace_341722
  have hstable : (prefixWord ++ tailWord_341722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341722).length < 2 ^ (prefixWord ++ tailWord_341722).sum := by decide
  have hdescent : baseEnd_341722 < baseStart_341722 := by decide
  rcases family_descends (prefixWord ++ tailWord_341722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341732 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_341732 : Nat := 118140960795 + 341732 * 2 ^ 59
def prefixEnd_341732 : Nat := 4983230072969 + 3 ^ 40 * 341732 * 2
def baseEnd_341732 : Nat := 175472771022362205678409

theorem tailTrace_341732 : CollatzResearch.WordTrace tailWord_341732 prefixEnd_341732 175472771022362205678409 := by
  unfold tailWord_341732
  simp only [CollatzResearch.WordTrace]
  refine ⟨6231994998985401012089725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8309326665313868016119633 6231994998985401012089725)
  ·
    refine ⟨2336998124619525379533647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6231994998985401012089725 2336998124619525379533647)
    ·
      refine ⟨3505497186929288069300471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2336998124619525379533647 3505497186929288069300471)
      ·
        refine ⟨5258245780393932103950707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3505497186929288069300471 5258245780393932103950707)
        ·
          refine ⟨7887368670590898155926061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5258245780393932103950707 7887368670590898155926061)
          ·
            refine ⟨2957763251471586808472273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7887368670590898155926061 2957763251471586808472273)
            ·
              refine ⟨2218322438603690106354205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2957763251471586808472273 2218322438603690106354205)
              ·
                refine ⟨831870914476383789882827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2218322438603690106354205 831870914476383789882827)
                ·
                  refine ⟨1247806371714575684824241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 831870914476383789882827 1247806371714575684824241)
                  ·
                    refine ⟨935854778785931763618181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1247806371714575684824241 935854778785931763618181)
                    ·
                      refine ⟨175472771022362205678409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 935854778785931763618181 175472771022362205678409)
                      ·
                        rfl

theorem cell23_341732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_341732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341732 prefixEnd_341732 := by exact prefixLift 341732
  have htrace : WordTrace (prefixWord ++ tailWord_341732) baseStart_341732 baseEnd_341732 := by
    simpa [prefixWord, tailWord_341732, baseEnd_341732] using wordTrace_append hprefix tailTrace_341732
  have hstable : (prefixWord ++ tailWord_341732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341732).length < 2 ^ (prefixWord ++ tailWord_341732).sum := by decide
  have hdescent : baseEnd_341732 < baseStart_341732 := by decide
  rcases family_descends (prefixWord ++ tailWord_341732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341736 : List Nat := [2, 1, 4, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_341736 : Nat := 118140960795 + 341736 * 2 ^ 59
def prefixEnd_341736 : Nat := 4983230072969 + 3 ^ 40 * 341736 * 2
def baseEnd_341736 : Nat := 175474824944980190028391

theorem tailTrace_341736 : CollatzResearch.WordTrace tailWord_341736 prefixEnd_341736 175474824944980190028391 := by
  unfold tailWord_341736
  simp only [CollatzResearch.WordTrace]
  refine ⟨6232067944978155353662531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8309423926637540471550041 6232067944978155353662531)
  ·
    refine ⟨9348101917467233030493797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6232067944978155353662531 9348101917467233030493797)
    ·
      refine ⟨1752769109525106193217587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9348101917467233030493797 1752769109525106193217587)
      ·
        refine ⟨2629153664287659289826381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1752769109525106193217587 2629153664287659289826381)
        ·
          refine ⟨985932624107872233684893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2629153664287659289826381 985932624107872233684893)
          ·
            refine ⟨369724734040452087631835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 985932624107872233684893 369724734040452087631835)
            ·
              refine ⟨554587101060678131447753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369724734040452087631835 554587101060678131447753)
              ·
                refine ⟨415940325795508598585815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 554587101060678131447753 415940325795508598585815)
                ·
                  refine ⟨623910488693262897878723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415940325795508598585815 623910488693262897878723)
                  ·
                    refine ⟨935865733039894346818085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 623910488693262897878723 935865733039894346818085)
                    ·
                      refine ⟨175474824944980190028391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 935865733039894346818085 175474824944980190028391)
                      ·
                        rfl

theorem cell23_341736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_341736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341736 prefixEnd_341736 := by exact prefixLift 341736
  have htrace : WordTrace (prefixWord ++ tailWord_341736) baseStart_341736 baseEnd_341736 := by
    simpa [prefixWord, tailWord_341736, baseEnd_341736] using wordTrace_append hprefix tailTrace_341736
  have hstable : (prefixWord ++ tailWord_341736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341736).length < 2 ^ (prefixWord ++ tailWord_341736).sum := by decide
  have hdescent : baseEnd_341736 < baseStart_341736 := by decide
  rcases family_descends (prefixWord ++ tailWord_341736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341739 : List Nat := [1, 1, 1, 1, 2, 4, 5, 2, 1, 2, 3]
def baseStart_341739 : Nat := 118140960795 + 341739 * 2 ^ 59
def prefixEnd_341739 : Nat := 4983230072969 + 3 ^ 40 * 341739 * 2
def baseEnd_341739 : Nat := 175476365386943678290877

theorem tailTrace_341739 : CollatzResearch.WordTrace tailWord_341739 prefixEnd_341739 175476365386943678290877 := by
  unfold tailWord_341739
  simp only [CollatzResearch.WordTrace]
  refine ⟨12464245308945442219684271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8309496872630294813122847 12464245308945442219684271)
  ·
    refine ⟨18696367963418163329526407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12464245308945442219684271 18696367963418163329526407)
    ·
      refine ⟨28044551945127244994289611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18696367963418163329526407 28044551945127244994289611)
      ·
        refine ⟨42066827917690867491434417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28044551945127244994289611 42066827917690867491434417)
        ·
          refine ⟨31550120938268150618575813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42066827917690867491434417 31550120938268150618575813)
          ·
            refine ⟨5915647675925278240982965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31550120938268150618575813 5915647675925278240982965)
            ·
              refine ⟨554591969617994835092153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5915647675925278240982965 554591969617994835092153)
              ·
                refine ⟨415943977213496126319115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 554591969617994835092153 415943977213496126319115)
                ·
                  refine ⟨623915965820244189478673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415943977213496126319115 623915965820244189478673)
                  ·
                    refine ⟨467936974365183142109005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 623915965820244189478673 467936974365183142109005)
                    ·
                      refine ⟨175476365386943678290877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 467936974365183142109005 175476365386943678290877)
                      ·
                        rfl

theorem cell23_341739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 2, 3].length) (baseStart_341739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341739 prefixEnd_341739 := by exact prefixLift 341739
  have htrace : WordTrace (prefixWord ++ tailWord_341739) baseStart_341739 baseEnd_341739 := by
    simpa [prefixWord, tailWord_341739, baseEnd_341739] using wordTrace_append hprefix tailTrace_341739
  have hstable : (prefixWord ++ tailWord_341739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341739).length < 2 ^ (prefixWord ++ tailWord_341739).sum := by decide
  have hdescent : baseEnd_341739 < baseStart_341739 := by decide
  rcases family_descends (prefixWord ++ tailWord_341739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341756 : List Nat := [2, 2, 2, 1, 3, 1, 5, 1, 1, 2, 3]
def baseStart_341756 : Nat := 118140960795 + 341756 * 2 ^ 59
def prefixEnd_341756 : Nat := 4983230072969 + 3 ^ 40 * 341756 * 2
def baseEnd_341756 : Nat := 175485094558070111778299

theorem tailTrace_341756 : CollatzResearch.WordTrace tailWord_341756 prefixEnd_341756 175485094558070111778299 := by
  unfold tailWord_341756
  simp only [CollatzResearch.WordTrace]
  refine ⟨6232432674941927061526561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8309910233255902748702081 6232432674941927061526561)
  ·
    refine ⟨4674324506206445296144921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6232432674941927061526561 4674324506206445296144921)
    ·
      refine ⟨3505743379654833972108691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4674324506206445296144921 3505743379654833972108691)
      ·
        refine ⟨5258615069482250958163037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3505743379654833972108691 5258615069482250958163037)
        ·
          refine ⟨1971980651055844109311139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5258615069482250958163037 1971980651055844109311139)
          ·
            refine ⟨2957970976583766163966709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1971980651055844109311139 2957970976583766163966709)
            ·
              refine ⟨277309779054728077871879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2957970976583766163966709 277309779054728077871879)
              ·
                refine ⟨415964668582092116807819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277309779054728077871879 415964668582092116807819)
                ·
                  refine ⟨623947002873138175211729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 415964668582092116807819 623947002873138175211729)
                  ·
                    refine ⟨467960252154853631408797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 623947002873138175211729 467960252154853631408797)
                    ·
                      refine ⟨175485094558070111778299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 467960252154853631408797 175485094558070111778299)
                      ·
                        rfl

theorem cell23_341756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_341756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341756 prefixEnd_341756 := by exact prefixLift 341756
  have htrace : WordTrace (prefixWord ++ tailWord_341756) baseStart_341756 baseEnd_341756 := by
    simpa [prefixWord, tailWord_341756, baseEnd_341756] using wordTrace_append hprefix tailTrace_341756
  have hstable : (prefixWord ++ tailWord_341756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341756).length < 2 ^ (prefixWord ++ tailWord_341756).sum := by decide
  have hdescent : baseEnd_341756 < baseStart_341756 := by decide
  rcases family_descends (prefixWord ++ tailWord_341756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341765 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_341765 : Nat := 118140960795 + 341765 * 2 ^ 59
def prefixEnd_341765 : Nat := 4983230072969 + 3 ^ 40 * 341765 * 2
def baseEnd_341765 : Nat := 175489715883960576565757

theorem tailTrace_341765 : CollatzResearch.WordTrace tailWord_341765 prefixEnd_341765 175489715883960576565757 := by
  unfold tailWord_341765
  simp only [CollatzResearch.WordTrace]
  refine ⟨12465193606851248660130749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8310129071234165773420499 12465193606851248660130749)
  ·
    refine ⟨4674447602569218247549031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12465193606851248660130749 4674447602569218247549031)
    ·
      refine ⟨7011671403853827371323547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4674447602569218247549031 7011671403853827371323547)
      ·
        refine ⟨10517507105780741056985321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7011671403853827371323547 10517507105780741056985321)
        ·
          refine ⟨7888130329335555792738991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10517507105780741056985321 7888130329335555792738991)
          ·
            refine ⟨11832195494003333689108487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7888130329335555792738991 11832195494003333689108487)
            ·
              refine ⟨17748293241005000533662731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11832195494003333689108487 17748293241005000533662731)
              ·
                refine ⟨26622439861507500800494097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17748293241005000533662731 26622439861507500800494097)
                ·
                  refine ⟨19966829896130625600370573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26622439861507500800494097 19966829896130625600370573)
                  ·
                    refine ⟨7487561211048984600138965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19966829896130625600370573 7487561211048984600138965)
                    ·
                      refine ⟨175489715883960576565757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7487561211048984600138965 175489715883960576565757)
                      ·
                        rfl

theorem cell23_341765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_341765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341765 prefixEnd_341765 := by exact prefixLift 341765
  have htrace : WordTrace (prefixWord ++ tailWord_341765) baseStart_341765 baseEnd_341765 := by
    simpa [prefixWord, tailWord_341765, baseEnd_341765] using wordTrace_append hprefix tailTrace_341765
  have hstable : (prefixWord ++ tailWord_341765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341765).length < 2 ^ (prefixWord ++ tailWord_341765).sum := by decide
  have hdescent : baseEnd_341765 < baseStart_341765 := by decide
  rcases family_descends (prefixWord ++ tailWord_341765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341770 : List Nat := [3, 1, 2, 2, 1, 3, 4, 2, 1, 2, 2]
def baseStart_341770 : Nat := 118140960795 + 341770 * 2 ^ 59
def prefixEnd_341770 : Nat := 4983230072969 + 3 ^ 40 * 341770 * 2
def baseEnd_341770 : Nat := 175492283287233057003235

theorem tailTrace_341770 : CollatzResearch.WordTrace tailWord_341770 prefixEnd_341770 175492283287233057003235 := by
  unfold tailWord_341770
  simp only [CollatzResearch.WordTrace]
  refine ⟨3116343992958283628515691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8310250647888756342708509 3116343992958283628515691)
  ·
    refine ⟨4674515989437425442773537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3116343992958283628515691 4674515989437425442773537)
    ·
      refine ⟨3505886992078069082080153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4674515989437425442773537 3505886992078069082080153)
      ·
        refine ⟨2629415244058551811560115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3505886992078069082080153 2629415244058551811560115)
        ·
          refine ⟨3944122866087827717340173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2629415244058551811560115 3944122866087827717340173)
          ·
            refine ⟨1479046074782935394002565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3944122866087827717340173 1479046074782935394002565)
            ·
              refine ⟨277321139021800386375481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1479046074782935394002565 277321139021800386375481)
              ·
                refine ⟨207990854266350289781611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277321139021800386375481 207990854266350289781611)
                ·
                  refine ⟨311986281399525434672417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207990854266350289781611 311986281399525434672417)
                  ·
                    refine ⟨233989711049644076004313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 311986281399525434672417 233989711049644076004313)
                    ·
                      refine ⟨175492283287233057003235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 233989711049644076004313 175492283287233057003235)
                      ·
                        rfl

theorem cell23_341770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_341770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341770 prefixEnd_341770 := by exact prefixLift 341770
  have htrace : WordTrace (prefixWord ++ tailWord_341770) baseStart_341770 baseEnd_341770 := by
    simpa [prefixWord, tailWord_341770, baseEnd_341770] using wordTrace_append hprefix tailTrace_341770
  have hstable : (prefixWord ++ tailWord_341770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341770).length < 2 ^ (prefixWord ++ tailWord_341770).sum := by decide
  have hdescent : baseEnd_341770 < baseStart_341770 := by decide
  rcases family_descends (prefixWord ++ tailWord_341770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341786 : List Nat := [3, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3]
def baseStart_341786 : Nat := 118140960795 + 341786 * 2 ^ 59
def prefixEnd_341786 : Nat := 4983230072969 + 3 ^ 40 * 341786 * 2
def baseEnd_341786 : Nat := 175500498977704994403161

theorem tailTrace_341786 : CollatzResearch.WordTrace tailWord_341786 prefixEnd_341786 175500498977704994403161 := by
  unfold tailWord_341786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3116489884943792311661303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8310639693183446164430141 3116489884943792311661303)
  ·
    refine ⟨4674734827415688467491955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3116489884943792311661303 4674734827415688467491955)
    ·
      refine ⟨7012102241123532701237933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4674734827415688467491955 7012102241123532701237933)
      ·
        refine ⟨2629538340421324762964225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7012102241123532701237933 2629538340421324762964225)
        ·
          refine ⟨1972153755315993572223169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2629538340421324762964225 1972153755315993572223169)
          ·
            refine ⟨1479115316486995179167377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1972153755315993572223169 1479115316486995179167377)
            ·
              refine ⟨1109336487365246384375533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1479115316486995179167377 1109336487365246384375533)
              ·
                refine ⟨416001182761967394140825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1109336487365246384375533 416001182761967394140825)
                ·
                  refine ⟨312000887071475545605619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416001182761967394140825 312000887071475545605619)
                  ·
                    refine ⟨468001330607213318408429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 312000887071475545605619 468001330607213318408429)
                    ·
                      refine ⟨175500498977704994403161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 468001330607213318408429 175500498977704994403161)
                      ·
                        rfl

theorem cell23_341786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_341786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341786 prefixEnd_341786 := by exact prefixLift 341786
  have htrace : WordTrace (prefixWord ++ tailWord_341786) baseStart_341786 baseEnd_341786 := by
    simpa [prefixWord, tailWord_341786, baseEnd_341786] using wordTrace_append hprefix tailTrace_341786
  have hstable : (prefixWord ++ tailWord_341786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341786).length < 2 ^ (prefixWord ++ tailWord_341786).sum := by decide
  have hdescent : baseEnd_341786 < baseStart_341786 := by decide
  rcases family_descends (prefixWord ++ tailWord_341786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341792 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 4]
def baseStart_341792 : Nat := 118140960795 + 341792 * 2 ^ 59
def prefixEnd_341792 : Nat := 4983230072969 + 3 ^ 40 * 341792 * 2
def baseEnd_341792 : Nat := 175503579861631970928133

theorem tailTrace_341792 : CollatzResearch.WordTrace tailWord_341792 prefixEnd_341792 175503579861631970928133 := by
  unfold tailWord_341792
  simp only [CollatzResearch.WordTrace]
  refine ⟨6233089188876716135681815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8310785585168954847575753 6233089188876716135681815)
  ·
    refine ⟨9349633783315074203522723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6233089188876716135681815 9349633783315074203522723)
    ·
      refine ⟨14024450674972611305284085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9349633783315074203522723 14024450674972611305284085)
      ·
        refine ⟨1314792250778682309870383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14024450674972611305284085 1314792250778682309870383)
        ·
          refine ⟨1972188376168023464805575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1314792250778682309870383 1972188376168023464805575)
          ·
            refine ⟨2958282564252035197208363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1972188376168023464805575 2958282564252035197208363)
            ·
              refine ⟨4437423846378052795812545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2958282564252035197208363 4437423846378052795812545)
              ·
                refine ⟨3328067884783539596859409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4437423846378052795812545 3328067884783539596859409)
                ·
                  refine ⟨2496050913587654697644557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3328067884783539596859409 2496050913587654697644557)
                  ·
                    refine ⟨936019092595370511616709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2496050913587654697644557 936019092595370511616709)
                    ·
                      refine ⟨175503579861631970928133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 936019092595370511616709 175503579861631970928133)
                      ·
                        rfl

theorem cell23_341792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_341792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341792 prefixEnd_341792 := by exact prefixLift 341792
  have htrace : WordTrace (prefixWord ++ tailWord_341792) baseStart_341792 baseEnd_341792 := by
    simpa [prefixWord, tailWord_341792, baseEnd_341792] using wordTrace_append hprefix tailTrace_341792
  have hstable : (prefixWord ++ tailWord_341792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341792).length < 2 ^ (prefixWord ++ tailWord_341792).sum := by decide
  have hdescent : baseEnd_341792 < baseStart_341792 := by decide
  rcases family_descends (prefixWord ++ tailWord_341792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341796 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 3, 3, 2]
def baseStart_341796 : Nat := 118140960795 + 341796 * 2 ^ 59
def prefixEnd_341796 : Nat := 4983230072969 + 3 ^ 40 * 341796 * 2
def baseEnd_341796 : Nat := 175505633784249955278115

theorem tailTrace_341796 : CollatzResearch.WordTrace tailWord_341796 prefixEnd_341796 175505633784249955278115 := by
  unfold tailWord_341796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6233162134869470477254621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8310882846492627303006161 6233162134869470477254621)
  ·
    refine ⟨2337435800576051428970483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6233162134869470477254621 2337435800576051428970483)
    ·
      refine ⟨3506153700864077143455725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2337435800576051428970483 3506153700864077143455725)
      ·
        refine ⟨1314807637824028928795897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3506153700864077143455725 1314807637824028928795897)
        ·
          refine ⟨986105728368021696596923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1314807637824028928795897 986105728368021696596923)
          ·
            refine ⟨1479158592552032544895385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986105728368021696596923 1479158592552032544895385)
            ·
              refine ⟨1109368944414024408671539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1479158592552032544895385 1109368944414024408671539)
              ·
                refine ⟨1664053416621036613007309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109368944414024408671539 1664053416621036613007309)
                ·
                  refine ⟨624020031232888729877741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1664053416621036613007309 624020031232888729877741)
                  ·
                    refine ⟨234007511712333273704153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 624020031232888729877741 234007511712333273704153)
                    ·
                      refine ⟨175505633784249955278115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 234007511712333273704153 175505633784249955278115)
                      ·
                        rfl

theorem cell23_341796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_341796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341796 prefixEnd_341796 := by exact prefixLift 341796
  have htrace : WordTrace (prefixWord ++ tailWord_341796) baseStart_341796 baseEnd_341796 := by
    simpa [prefixWord, tailWord_341796, baseEnd_341796] using wordTrace_append hprefix tailTrace_341796
  have hstable : (prefixWord ++ tailWord_341796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341796).length < 2 ^ (prefixWord ++ tailWord_341796).sum := by decide
  have hdescent : baseEnd_341796 < baseStart_341796 := by decide
  rcases family_descends (prefixWord ++ tailWord_341796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341813 : List Nat := [1, 3, 3, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_341813 : Nat := 118140960795 + 341813 * 2 ^ 59
def prefixEnd_341813 : Nat := 4983230072969 + 3 ^ 40 * 341813 * 2
def baseEnd_341813 : Nat := 175514362955376388765537

theorem tailTrace_341813 : CollatzResearch.WordTrace tailWord_341813 prefixEnd_341813 175514362955376388765537 := by
  unfold tailWord_341813
  simp only [CollatzResearch.WordTrace]
  refine ⟨12466944310677352857878093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8311296207118235238585395 12466944310677352857878093)
  ·
    refine ⟨4675104116504007321704285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12466944310677352857878093 4675104116504007321704285)
    ·
      refine ⟨1753164043689002745639107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4675104116504007321704285 1753164043689002745639107)
      ·
        refine ⟨2629746065533504118458661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1753164043689002745639107 2629746065533504118458661)
        ·
          refine ⟨493077387287532022210999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2629746065533504118458661 493077387287532022210999)
          ·
            refine ⟨739616080931298033316499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493077387287532022210999 739616080931298033316499)
            ·
              refine ⟨1109424121396947049974749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 739616080931298033316499 1109424121396947049974749)
              ·
                refine ⟨416034045523855143740531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1109424121396947049974749 416034045523855143740531)
                ·
                  refine ⟨624051068285782715610797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416034045523855143740531 624051068285782715610797)
                  ·
                    refine ⟨234019150607168518354049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 624051068285782715610797 234019150607168518354049)
                    ·
                      refine ⟨175514362955376388765537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 234019150607168518354049 175514362955376388765537)
                      ·
                        rfl

theorem cell23_341813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_341813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341813 prefixEnd_341813 := by exact prefixLift 341813
  have htrace : WordTrace (prefixWord ++ tailWord_341813) baseStart_341813 baseEnd_341813 := by
    simpa [prefixWord, tailWord_341813, baseEnd_341813] using wordTrace_append hprefix tailTrace_341813
  have hstable : (prefixWord ++ tailWord_341813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341813).length < 2 ^ (prefixWord ++ tailWord_341813).sum := by decide
  have hdescent : baseEnd_341813 < baseStart_341813 := by decide
  rcases family_descends (prefixWord ++ tailWord_341813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341832 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 7]
def baseStart_341832 : Nat := 118140960795 + 341832 * 2 ^ 59
def prefixEnd_341832 : Nat := 4983230072969 + 3 ^ 40 * 341832 * 2
def baseEnd_341832 : Nat := 19502679898645757158661

theorem tailTrace_341832 : CollatzResearch.WordTrace tailWord_341832 prefixEnd_341832 19502679898645757158661 := by
  unfold tailWord_341832
  simp only [CollatzResearch.WordTrace]
  refine ⟨6233818648804259551409875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8311758198405679401879833 6233818648804259551409875)
  ·
    refine ⟨9350727973206389327114813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6233818648804259551409875 9350727973206389327114813)
    ·
      refine ⟨3506522989952395997668055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9350727973206389327114813 3506522989952395997668055)
      ·
        refine ⟨5259784484928593996502083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3506522989952395997668055 5259784484928593996502083)
        ·
          refine ⟨7889676727392890994753125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5259784484928593996502083 7889676727392890994753125)
          ·
            refine ⟨1479314386386167061516211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7889676727392890994753125 1479314386386167061516211)
            ·
              refine ⟨2218971579579250592274317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1479314386386167061516211 2218971579579250592274317)
              ·
                refine ⟨832114342342218972102869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2218971579579250592274317 832114342342218972102869)
                ·
                  refine ⟨19502679898645757158661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 832114342342218972102869 19502679898645757158661)
                  ·
                    rfl

theorem cell23_341832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 7].length) (baseStart_341832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341832 prefixEnd_341832 := by exact prefixLift 341832
  have htrace : WordTrace (prefixWord ++ tailWord_341832) baseStart_341832 baseEnd_341832 := by
    simpa [prefixWord, tailWord_341832, baseEnd_341832] using wordTrace_append hprefix tailTrace_341832
  have hstable : (prefixWord ++ tailWord_341832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341832).length < 2 ^ (prefixWord ++ tailWord_341832).sum := by decide
  have hdescent : baseEnd_341832 < baseStart_341832 := by decide
  rcases family_descends (prefixWord ++ tailWord_341832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341872 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 5]
def baseStart_341872 : Nat := 118140960795 + 341872 * 2 ^ 59
def prefixEnd_341872 : Nat := 4983230072969 + 3 ^ 40 * 341872 * 2
def baseEnd_341872 : Nat := 175544658313991657927765

theorem tailTrace_341872 : CollatzResearch.WordTrace tailWord_341872 prefixEnd_341872 175544658313991657927765 := by
  unfold tailWord_341872
  simp only [CollatzResearch.WordTrace]
  refine ⟨6234548108731802967137935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8312730811642403956183913 6234548108731802967137935)
  ·
    refine ⟨9351822163097704450706903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6234548108731802967137935 9351822163097704450706903)
    ·
      refine ⟨14027733244646556676060355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9351822163097704450706903 14027733244646556676060355)
      ·
        refine ⟨21041599866969835014090533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14027733244646556676060355 21041599866969835014090533)
        ·
          refine ⟨3945299975056844065141975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21041599866969835014090533 3945299975056844065141975)
          ·
            refine ⟨5917949962585266097712963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3945299975056844065141975 5917949962585266097712963)
            ·
              refine ⟨8876924943877899146569445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5917949962585266097712963 8876924943877899146569445)
              ·
                refine ⟨1664423426977106089981771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8876924943877899146569445 1664423426977106089981771)
                ·
                  refine ⟨2496635140465659134972657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664423426977106089981771 2496635140465659134972657)
                  ·
                    refine ⟨1872476355349244351229493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2496635140465659134972657 1872476355349244351229493)
                    ·
                      refine ⟨175544658313991657927765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1872476355349244351229493 175544658313991657927765)
                      ·
                        rfl

theorem cell23_341872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_341872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341872 prefixEnd_341872 := by exact prefixLift 341872
  have htrace : WordTrace (prefixWord ++ tailWord_341872) baseStart_341872 baseEnd_341872 := by
    simpa [prefixWord, tailWord_341872, baseEnd_341872] using wordTrace_append hprefix tailTrace_341872
  have hstable : (prefixWord ++ tailWord_341872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341872).length < 2 ^ (prefixWord ++ tailWord_341872).sum := by decide
  have hdescent : baseEnd_341872 < baseStart_341872 := by decide
  rcases family_descends (prefixWord ++ tailWord_341872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341899 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 1, 6, 2]
def baseStart_341899 : Nat := 118140960795 + 341899 * 2 ^ 59
def prefixEnd_341899 : Nat := 4983230072969 + 3 ^ 40 * 341899 * 2
def baseEnd_341899 : Nat := 175558522291663052290141

theorem tailTrace_341899 : CollatzResearch.WordTrace tailWord_341899 prefixEnd_341899 175558522291663052290141 := by
  unfold tailWord_341899
  simp only [CollatzResearch.WordTrace]
  refine ⟨12470080988365789545508751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8313387325577193030339167 12470080988365789545508751)
  ·
    refine ⟨18705121482548684318263127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12470080988365789545508751 18705121482548684318263127)
    ·
      refine ⟨28057682223823026477394691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18705121482548684318263127 28057682223823026477394691)
      ·
        refine ⟨42086523335734539716092037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28057682223823026477394691 42086523335734539716092037)
        ·
          refine ⟨7891223125450226196767257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42086523335734539716092037 7891223125450226196767257)
          ·
            refine ⟨5918417344087669647575443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7891223125450226196767257 5918417344087669647575443)
            ·
              refine ⟨8877626016131504471363165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5918417344087669647575443 8877626016131504471363165)
              ·
                refine ⟨3329109756049314176761187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8877626016131504471363165 3329109756049314176761187)
                ·
                  refine ⟨4993664634073971265141781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3329109756049314176761187 4993664634073971265141781)
                  ·
                    refine ⟨234078029722217403053521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4993664634073971265141781 234078029722217403053521)
                    ·
                      refine ⟨175558522291663052290141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 234078029722217403053521 175558522291663052290141)
                      ·
                        rfl

theorem cell23_341899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 6, 2].length) (baseStart_341899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341899 prefixEnd_341899 := by exact prefixLift 341899
  have htrace : WordTrace (prefixWord ++ tailWord_341899) baseStart_341899 baseEnd_341899 := by
    simpa [prefixWord, tailWord_341899, baseEnd_341899] using wordTrace_append hprefix tailTrace_341899
  have hstable : (prefixWord ++ tailWord_341899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341899).length < 2 ^ (prefixWord ++ tailWord_341899).sum := by decide
  have hdescent : baseEnd_341899 < baseStart_341899 := by decide
  rcases family_descends (prefixWord ++ tailWord_341899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341909 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 5, 4]
def baseStart_341909 : Nat := 118140960795 + 341909 * 2 ^ 59
def prefixEnd_341909 : Nat := 4983230072969 + 3 ^ 40 * 341909 * 2
def baseEnd_341909 : Nat := 58521219032736004388365

theorem tailTrace_341909 : CollatzResearch.WordTrace tailWord_341909 prefixEnd_341909 58521219032736004388365 := by
  unfold tailWord_341909
  simp only [CollatzResearch.WordTrace]
  refine ⟨12470445718329561253372781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8313630478886374168915187 12470445718329561253372781)
  ·
    refine ⟨4676417144373585470014793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12470445718329561253372781 4676417144373585470014793)
    ·
      refine ⟨3507312858280189102511095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4676417144373585470014793 3507312858280189102511095)
      ·
        refine ⟨5260969287420283653766643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3507312858280189102511095 5260969287420283653766643)
        ·
          refine ⟨7891453931130425480649965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5260969287420283653766643 7891453931130425480649965)
          ·
            refine ⟨2959295224173909555243737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7891453931130425480649965 2959295224173909555243737)
            ·
              refine ⟨2219471418130432166432803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2959295224173909555243737 2219471418130432166432803)
              ·
                refine ⟨3329207127195648249649205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2219471418130432166432803 3329207127195648249649205)
                ·
                  refine ⟨312113168174592023404613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3329207127195648249649205 312113168174592023404613)
                  ·
                    refine ⟨58521219032736004388365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 312113168174592023404613 58521219032736004388365)
                    ·
                      rfl

theorem cell23_341909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_341909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341909 prefixEnd_341909 := by exact prefixLift 341909
  have htrace : WordTrace (prefixWord ++ tailWord_341909) baseStart_341909 baseEnd_341909 := by
    simpa [prefixWord, tailWord_341909, baseEnd_341909] using wordTrace_append hprefix tailTrace_341909
  have hstable : (prefixWord ++ tailWord_341909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341909).length < 2 ^ (prefixWord ++ tailWord_341909).sum := by decide
  have hdescent : baseEnd_341909 < baseStart_341909 := by decide
  rcases family_descends (prefixWord ++ tailWord_341909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341916 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_341916 : Nat := 118140960795 + 341916 * 2 ^ 59
def prefixEnd_341916 : Nat := 4983230072969 + 3 ^ 40 * 341916 * 2
def baseEnd_341916 : Nat := 175567251462789485777563

theorem tailTrace_341916 : CollatzResearch.WordTrace tailWord_341916 prefixEnd_341916 175567251462789485777563 := by
  unfold tailWord_341916
  simp only [CollatzResearch.WordTrace]
  refine ⟨6235350514652100724438801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8313800686202800965918401 6235350514652100724438801)
  ·
    refine ⟨4676512885989075543329101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6235350514652100724438801 4676512885989075543329101)
    ·
      refine ⟨1753692332245903328748413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4676512885989075543329101 1753692332245903328748413)
      ·
        refine ⟨657634624592213748280655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1753692332245903328748413 657634624592213748280655)
        ·
          refine ⟨986451936888320622420983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 657634624592213748280655 986451936888320622420983)
          ·
            refine ⟨1479677905332480933631475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 986451936888320622420983 1479677905332480933631475)
            ·
              refine ⟨2219516857998721400447213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1479677905332480933631475 2219516857998721400447213)
              ·
                refine ⟨832318821749520525167705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2219516857998721400447213 832318821749520525167705)
                ·
                  refine ⟨624239116312140393875779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 832318821749520525167705 624239116312140393875779)
                  ·
                    refine ⟨936358674468210590813669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 624239116312140393875779 936358674468210590813669)
                    ·
                      refine ⟨175567251462789485777563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 936358674468210590813669 175567251462789485777563)
                      ·
                        rfl

theorem cell23_341916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_341916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341916 prefixEnd_341916 := by exact prefixLift 341916
  have htrace : WordTrace (prefixWord ++ tailWord_341916) baseStart_341916 baseEnd_341916 := by
    simpa [prefixWord, tailWord_341916, baseEnd_341916] using wordTrace_append hprefix tailTrace_341916
  have hstable : (prefixWord ++ tailWord_341916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341916).length < 2 ^ (prefixWord ++ tailWord_341916).sum := by decide
  have hdescent : baseEnd_341916 < baseStart_341916 := by decide
  rcases family_descends (prefixWord ++ tailWord_341916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341934 : List Nat := [4, 1, 5, 1, 1, 2, 2, 2, 5]
def baseStart_341934 : Nat := 118140960795 + 341934 * 2 ^ 59
def prefixEnd_341934 : Nat := 4983230072969 + 3 ^ 40 * 341934 * 2
def baseEnd_341934 : Nat := 19508499346063379483609

theorem tailTrace_341934 : CollatzResearch.WordTrace tailWord_341934 prefixEnd_341934 19508499346063379483609 := by
  unfold tailWord_341934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1558919692904873815379107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8314238362159327015355237 1558919692904873815379107)
  ·
    refine ⟨2338379539357310723068661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1558919692904873815379107 2338379539357310723068661)
    ·
      refine ⟨219223081814747880287687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2338379539357310723068661 219223081814747880287687)
      ·
        refine ⟨328834622722121820431531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219223081814747880287687 328834622722121820431531)
        ·
          refine ⟨493251934083182730647297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328834622722121820431531 493251934083182730647297)
          ·
            refine ⟨369938950562387047985473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493251934083182730647297 369938950562387047985473)
            ·
              refine ⟨277454212921790285989105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369938950562387047985473 277454212921790285989105)
              ·
                refine ⟨208090659691342714491829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277454212921790285989105 208090659691342714491829)
                ·
                  refine ⟨19508499346063379483609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 208090659691342714491829 19508499346063379483609)
                  ·
                    rfl

theorem cell23_341934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_341934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341934 prefixEnd_341934 := by exact prefixLift 341934
  have htrace : WordTrace (prefixWord ++ tailWord_341934) baseStart_341934 baseEnd_341934 := by
    simpa [prefixWord, tailWord_341934, baseEnd_341934] using wordTrace_append hprefix tailTrace_341934
  have hstable : (prefixWord ++ tailWord_341934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341934).length < 2 ^ (prefixWord ++ tailWord_341934).sum := by decide
  have hdescent : baseEnd_341934 < baseStart_341934 := by decide
  rcases family_descends (prefixWord ++ tailWord_341934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341939 : List Nat := [1, 1, 1, 2, 3, 1, 6, 2, 6]
def baseStart_341939 : Nat := 118140960795 + 341939 * 2 ^ 59
def prefixEnd_341939 : Nat := 4983230072969 + 3 ^ 40 * 341939 * 2
def baseEnd_341939 : Nat := 19508784613093655087773

theorem tailTrace_341939 : CollatzResearch.WordTrace tailWord_341939 prefixEnd_341939 19508784613093655087773 := by
  unfold tailWord_341939
  simp only [CollatzResearch.WordTrace]
  refine ⟨12471539908220876376964871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8314359938813917584643247 12471539908220876376964871)
  ·
    refine ⟨18707309862331314565447307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12471539908220876376964871 18707309862331314565447307)
    ·
      refine ⟨28060964793496971848170961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18707309862331314565447307 28060964793496971848170961)
      ·
        refine ⟨21045723595122728886128221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28060964793496971848170961 21045723595122728886128221)
        ·
          refine ⟨7892146348171023332298083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21045723595122728886128221 7892146348171023332298083)
          ·
            refine ⟨11838219522256534998447125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7892146348171023332298083 11838219522256534998447125)
            ·
              refine ⟨554916540105775078052209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11838219522256534998447125 554916540105775078052209)
              ·
                refine ⟨416187405079331308539157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 554916540105775078052209 416187405079331308539157)
                ·
                  refine ⟨19508784613093655087773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 416187405079331308539157 19508784613093655087773)
                  ·
                    rfl

theorem cell23_341939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 6].length) (baseStart_341939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341939 prefixEnd_341939 := by exact prefixLift 341939
  have htrace : WordTrace (prefixWord ++ tailWord_341939) baseStart_341939 baseEnd_341939 := by
    simpa [prefixWord, tailWord_341939, baseEnd_341939] using wordTrace_append hprefix tailTrace_341939
  have hstable : (prefixWord ++ tailWord_341939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341939).length < 2 ^ (prefixWord ++ tailWord_341939).sum := by decide
  have hdescent : baseEnd_341939 < baseStart_341939 := by decide
  rcases family_descends (prefixWord ++ tailWord_341939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341970 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_341970 : Nat := 118140960795 + 341970 * 2 ^ 59
def prefixEnd_341970 : Nat := 4983230072969 + 3 ^ 40 * 341970 * 2
def baseEnd_341970 : Nat := 175594979418132274502315

theorem tailTrace_341970 : CollatzResearch.WordTrace tailWord_341970 prefixEnd_341970 175594979418132274502315 := by
  unfold tailWord_341970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3118167642777142167835841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8315113714072379114228909 3118167642777142167835841)
  ·
    refine ⟨2338625732082856625876881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3118167642777142167835841 2338625732082856625876881)
    ·
      refine ⟨1753969299062142469407661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2338625732082856625876881 1753969299062142469407661)
      ·
        refine ⟨657738487148303426027873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1753969299062142469407661 657738487148303426027873)
        ·
          refine ⟨493303865361227569520905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657738487148303426027873 493303865361227569520905)
          ·
            refine ⟨369977899020920677140679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493303865361227569520905 369977899020920677140679)
            ·
              refine ⟨554966848531381015711019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369977899020920677140679 554966848531381015711019)
              ·
                refine ⟨832450272797071523566529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554966848531381015711019 832450272797071523566529)
                ·
                  refine ⟨624337704597803642674897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 832450272797071523566529 624337704597803642674897)
                  ·
                    refine ⟨468253278448352732006173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 624337704597803642674897 468253278448352732006173)
                    ·
                      refine ⟨175594979418132274502315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 468253278448352732006173 175594979418132274502315)
                      ·
                        rfl

theorem cell23_341970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_341970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341970 prefixEnd_341970 := by exact prefixLift 341970
  have htrace : WordTrace (prefixWord ++ tailWord_341970) baseStart_341970 baseEnd_341970 := by
    simpa [prefixWord, tailWord_341970, baseEnd_341970] using wordTrace_append hprefix tailTrace_341970
  have hstable : (prefixWord ++ tailWord_341970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341970).length < 2 ^ (prefixWord ++ tailWord_341970).sum := by decide
  have hdescent : baseEnd_341970 < baseStart_341970 := by decide
  rcases family_descends (prefixWord ++ tailWord_341970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341976 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 1, 5, 2]
def baseStart_341976 : Nat := 118140960795 + 341976 * 2 ^ 59
def prefixEnd_341976 : Nat := 4983230072969 + 3 ^ 40 * 341976 * 2
def baseEnd_341976 : Nat := 175598060302059251027287

theorem tailTrace_341976 : CollatzResearch.WordTrace tailWord_341976 prefixEnd_341976 175598060302059251027287 := by
  unfold tailWord_341976
  simp only [CollatzResearch.WordTrace]
  refine ⟨6236444704543415848030891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8315259606057887797374521 6236444704543415848030891)
  ·
    refine ⟨9354667056815123772046337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6236444704543415848030891 9354667056815123772046337)
    ·
      refine ⟨7016000292611342829034753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9354667056815123772046337 7016000292611342829034753)
      ·
        refine ⟨5262000219458507121776065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7016000292611342829034753 5262000219458507121776065)
        ·
          refine ⟨3946500164593880341332049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5262000219458507121776065 3946500164593880341332049)
          ·
            refine ⟨2959875123445410255999037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3946500164593880341332049 2959875123445410255999037)
            ·
              refine ⟨1109953171292028845999639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2959875123445410255999037 1109953171292028845999639)
              ·
                refine ⟨1664929756938043268999459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1109953171292028845999639 1664929756938043268999459)
                ·
                  refine ⟨2497394635407064903499189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1664929756938043268999459 2497394635407064903499189)
                  ·
                    refine ⟨234130747069412334703049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2497394635407064903499189 234130747069412334703049)
                    ·
                      refine ⟨175598060302059251027287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 234130747069412334703049 175598060302059251027287)
                      ·
                        rfl

theorem cell23_341976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_341976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_341976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_341976 prefixEnd_341976 := by exact prefixLift 341976
  have htrace : WordTrace (prefixWord ++ tailWord_341976) baseStart_341976 baseEnd_341976 := by
    simpa [prefixWord, tailWord_341976, baseEnd_341976] using wordTrace_append hprefix tailTrace_341976
  have hstable : (prefixWord ++ tailWord_341976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341976).length < 2 ^ (prefixWord ++ tailWord_341976).sum := by decide
  have hdescent : baseEnd_341976 < baseStart_341976 := by decide
  rcases family_descends (prefixWord ++ tailWord_341976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342009 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 3, 1, 5]
def baseStart_342009 : Nat := 118140960795 + 342009 * 2 ^ 59
def prefixEnd_342009 : Nat := 4983230072969 + 3 ^ 40 * 342009 * 2
def baseEnd_342009 : Nat := 175615005163657621914635

theorem tailTrace_342009 : CollatzResearch.WordTrace tailWord_342009 prefixEnd_342009 175615005163657621914635 := by
  unfold tailWord_342009
  simp only [CollatzResearch.WordTrace]
  refine ⟨12474093017967278332013081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8316062011978185554675387 12474093017967278332013081)
  ·
    refine ⟨9355569763475458749009811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12474093017967278332013081 9355569763475458749009811)
    ·
      refine ⟨14033354645213188123514717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9355569763475458749009811 14033354645213188123514717)
      ·
        refine ⟨5262507991954945546318019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14033354645213188123514717 5262507991954945546318019)
        ·
          refine ⟨7893761987932418319477029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5262507991954945546318019 7893761987932418319477029)
          ·
            refine ⟨1480080372737328434901943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7893761987932418319477029 1480080372737328434901943)
            ·
              refine ⟨2220120559105992652352915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480080372737328434901943 2220120559105992652352915)
              ·
                refine ⟨3330180838658988978529373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220120559105992652352915 3330180838658988978529373)
                ·
                  refine ⟨1248817814497120866948515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3330180838658988978529373 1248817814497120866948515)
                  ·
                    refine ⟨1873226721745681300422773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1248817814497120866948515 1873226721745681300422773)
                    ·
                      refine ⟨175615005163657621914635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1873226721745681300422773 175615005163657621914635)
                      ·
                        rfl

theorem cell23_342009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_342009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342009 prefixEnd_342009 := by exact prefixLift 342009
  have htrace : WordTrace (prefixWord ++ tailWord_342009) baseStart_342009 baseEnd_342009 := by
    simpa [prefixWord, tailWord_342009, baseEnd_342009] using wordTrace_append hprefix tailTrace_342009
  have hstable : (prefixWord ++ tailWord_342009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342009).length < 2 ^ (prefixWord ++ tailWord_342009).sum := by decide
  have hdescent : baseEnd_342009 < baseStart_342009 := by decide
  rcases family_descends (prefixWord ++ tailWord_342009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342020 : List Nat := [2, 3, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_342020 : Nat := 118140960795 + 342020 * 2 ^ 59
def prefixEnd_342020 : Nat := 4983230072969 + 3 ^ 40 * 342020 * 2
def baseEnd_342020 : Nat := 58540217816952359625695

theorem tailTrace_342020 : CollatzResearch.WordTrace tailWord_342020 prefixEnd_342020 58540217816952359625695 := by
  unfold tailWord_342020
  simp only [CollatzResearch.WordTrace]
  refine ⟨6237247110463713605331757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8316329480618284807109009 6237247110463713605331757)
  ·
    refine ⟨2338967666423892601999409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6237247110463713605331757 2338967666423892601999409)
    ·
      refine ⟨1754225749817919451499557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2338967666423892601999409 1754225749817919451499557)
      ·
        refine ⟨328917328090859897156167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1754225749817919451499557 328917328090859897156167)
        ·
          refine ⟨493375992136289845734251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328917328090859897156167 493375992136289845734251)
          ·
            refine ⟨740063988204434768601377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493375992136289845734251 740063988204434768601377)
            ·
              refine ⟨555047991153326076451033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740063988204434768601377 555047991153326076451033)
              ·
                refine ⟨416285993364994557338275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555047991153326076451033 416285993364994557338275)
                ·
                  refine ⟨624428990047491836007413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416285993364994557338275 624428990047491836007413)
                  ·
                    refine ⟨58540217816952359625695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 624428990047491836007413 58540217816952359625695)
                    ·
                      rfl

theorem cell23_342020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_342020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342020 prefixEnd_342020 := by exact prefixLift 342020
  have htrace : WordTrace (prefixWord ++ tailWord_342020) baseStart_342020 baseEnd_342020 := by
    simpa [prefixWord, tailWord_342020, baseEnd_342020] using wordTrace_append hprefix tailTrace_342020
  have hstable : (prefixWord ++ tailWord_342020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342020).length < 2 ^ (prefixWord ++ tailWord_342020).sum := by decide
  have hdescent : baseEnd_342020 < baseStart_342020 := by decide
  rcases family_descends (prefixWord ++ tailWord_342020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342023 : List Nat := [1, 1, 4, 3, 1, 3, 2, 2, 1, 1, 4]
def baseStart_342023 : Nat := 118140960795 + 342023 * 2 ^ 59
def prefixEnd_342023 : Nat := 4983230072969 + 3 ^ 40 * 342023 * 2
def baseEnd_342023 : Nat := 175622193892820567139571

theorem tailTrace_342023 : CollatzResearch.WordTrace tailWord_342023 prefixEnd_342023 175622193892820567139571 := by
  unfold tailWord_342023
  simp only [CollatzResearch.WordTrace]
  refine ⟨12474603639916558723022723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8316402426611039148681815 12474603639916558723022723)
  ·
    refine ⟨18711905459874838084534085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12474603639916558723022723 18711905459874838084534085)
    ·
      refine ⟨3508482273726532140850141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18711905459874838084534085 3508482273726532140850141)
      ·
        refine ⟨1315680852647449552818803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3508482273726532140850141 1315680852647449552818803)
        ·
          refine ⟨1973521278971174329228205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1315680852647449552818803 1973521278971174329228205)
          ·
            refine ⟨740070479614190373460577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1973521278971174329228205 740070479614190373460577)
            ·
              refine ⟨555052859710642780095433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740070479614190373460577 555052859710642780095433)
              ·
                refine ⟨416289644782982085071575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555052859710642780095433 416289644782982085071575)
                ·
                  refine ⟨624434467174473127607363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416289644782982085071575 624434467174473127607363)
                  ·
                    refine ⟨936651700761709691411045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 624434467174473127607363 936651700761709691411045)
                    ·
                      refine ⟨175622193892820567139571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 936651700761709691411045 175622193892820567139571)
                      ·
                        rfl

theorem cell23_342023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_342023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342023 prefixEnd_342023 := by exact prefixLift 342023
  have htrace : WordTrace (prefixWord ++ tailWord_342023) baseStart_342023 baseEnd_342023 := by
    simpa [prefixWord, tailWord_342023, baseEnd_342023] using wordTrace_append hprefix tailTrace_342023
  have hstable : (prefixWord ++ tailWord_342023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342023).length < 2 ^ (prefixWord ++ tailWord_342023).sum := by decide
  have hdescent : baseEnd_342023 < baseStart_342023 := by decide
  rcases family_descends (prefixWord ++ tailWord_342023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342083 : List Nat := [1, 1, 1, 3, 1, 2, 2, 6, 1, 3, 2]
def baseStart_342083 : Nat := 118140960795 + 342083 * 2 ^ 59
def prefixEnd_342083 : Nat := 4983230072969 + 3 ^ 40 * 342083 * 2
def baseEnd_342083 : Nat := 175653002732090332389295

theorem tailTrace_342083 : CollatzResearch.WordTrace tailWord_342083 prefixEnd_342083 175653002732090332389295 := by
  unfold tailWord_342083
  simp only [CollatzResearch.WordTrace]
  refine ⟨12476792019699188970206903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8317861346466125980137935 12476792019699188970206903)
  ·
    refine ⟨18715188029548783455310355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12476792019699188970206903 18715188029548783455310355)
    ·
      refine ⟨28072782044323175182965533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18715188029548783455310355 28072782044323175182965533)
      ·
        refine ⟨10527293266621190693612075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28072782044323175182965533 10527293266621190693612075)
        ·
          refine ⟨15790939899931786040418113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10527293266621190693612075 15790939899931786040418113)
          ·
            refine ⟨11843204924948839530313585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15790939899931786040418113 11843204924948839530313585)
            ·
              refine ⟨8882403693711629647735189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11843204924948839530313585 8882403693711629647735189)
              ·
                refine ⟨416362673142732639737587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8882403693711629647735189 416362673142732639737587)
                ·
                  refine ⟨624544009714098959606381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416362673142732639737587 624544009714098959606381)
                  ·
                    refine ⟨234204003642787109852393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 624544009714098959606381 234204003642787109852393)
                    ·
                      refine ⟨175653002732090332389295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 234204003642787109852393 175653002732090332389295)
                      ·
                        rfl

theorem cell23_342083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 3, 2].length) (baseStart_342083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342083 prefixEnd_342083 := by exact prefixLift 342083
  have htrace : WordTrace (prefixWord ++ tailWord_342083) baseStart_342083 baseEnd_342083 := by
    simpa [prefixWord, tailWord_342083, baseEnd_342083] using wordTrace_append hprefix tailTrace_342083
  have hstable : (prefixWord ++ tailWord_342083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342083).length < 2 ^ (prefixWord ++ tailWord_342083).sum := by decide
  have hdescent : baseEnd_342083 < baseStart_342083 := by decide
  rcases family_descends (prefixWord ++ tailWord_342083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342099 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 5]
def baseStart_342099 : Nat := 118140960795 + 342099 * 2 ^ 59
def prefixEnd_342099 : Nat := 4983230072969 + 3 ^ 40 * 342099 * 2
def baseEnd_342099 : Nat := 175661218422562269789221

theorem tailTrace_342099 : CollatzResearch.WordTrace tailWord_342099 prefixEnd_342099 175661218422562269789221 := by
  unfold tailWord_342099
  simp only [CollatzResearch.WordTrace]
  refine ⟨12477375587641223702789351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8318250391760815801859567 12477375587641223702789351)
  ·
    refine ⟨18716063381461835554184027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12477375587641223702789351 18716063381461835554184027)
    ·
      refine ⟨28074095072192753331276041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18716063381461835554184027 28074095072192753331276041)
      ·
        refine ⟨21055571304144564998457031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28074095072192753331276041 21055571304144564998457031)
        ·
          refine ⟨31583356956216847497685547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21055571304144564998457031 31583356956216847497685547)
          ·
            refine ⟨47375035434325271246528321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31583356956216847497685547 47375035434325271246528321)
            ·
              refine ⟨35531276575743953434896241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47375035434325271246528321 35531276575743953434896241)
              ·
                refine ⟨26648457431807965076172181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35531276575743953434896241 26648457431807965076172181)
                ·
                  refine ⟨1249146442115998362945571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26648457431807965076172181 1249146442115998362945571)
                  ·
                    refine ⟨1873719663173997544418357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1249146442115998362945571 1873719663173997544418357)
                    ·
                      refine ⟨175661218422562269789221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1873719663173997544418357 175661218422562269789221)
                      ·
                        rfl

theorem cell23_342099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_342099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342099 prefixEnd_342099 := by exact prefixLift 342099
  have htrace : WordTrace (prefixWord ++ tailWord_342099) baseStart_342099 baseEnd_342099 := by
    simpa [prefixWord, tailWord_342099, baseEnd_342099] using wordTrace_append hprefix tailTrace_342099
  have hstable : (prefixWord ++ tailWord_342099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342099).length < 2 ^ (prefixWord ++ tailWord_342099).sum := by decide
  have hdescent : baseEnd_342099 < baseStart_342099 := by decide
  rcases family_descends (prefixWord ++ tailWord_342099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342116 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_342116 : Nat := 118140960795 + 342116 * 2 ^ 59
def prefixEnd_342116 : Nat := 4983230072969 + 3 ^ 40 * 342116 * 2
def baseEnd_342116 : Nat := 175669947593688703276643

theorem tailTrace_342116 : CollatzResearch.WordTrace tailWord_342116 prefixEnd_342116 175669947593688703276643 := by
  unfold tailWord_342116
  simp only [CollatzResearch.WordTrace]
  refine ⟨6238997814289817803079101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8318663752386423737438801 6238997814289817803079101)
  ·
    refine ⟨2339624180358681676154663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6238997814289817803079101 2339624180358681676154663)
    ·
      refine ⟨3509436270538022514231995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2339624180358681676154663 3509436270538022514231995)
      ·
        refine ⟨5264154405807033771347993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509436270538022514231995 5264154405807033771347993)
        ·
          refine ⟨3948115804355275328510995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5264154405807033771347993 3948115804355275328510995)
          ·
            refine ⟨5922173706532912992766493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3948115804355275328510995 5922173706532912992766493)
            ·
              refine ⟨2220815139949842372287435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5922173706532912992766493 2220815139949842372287435)
              ·
                refine ⟨3331222709924763558431153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2220815139949842372287435 3331222709924763558431153)
                ·
                  refine ⟨2498417032443572668823365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3331222709924763558431153 2498417032443572668823365)
                  ·
                    refine ⟨468453193583169875404381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2498417032443572668823365 468453193583169875404381)
                    ·
                      refine ⟨175669947593688703276643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 468453193583169875404381 175669947593688703276643)
                      ·
                        rfl

theorem cell23_342116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_342116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342116 prefixEnd_342116 := by exact prefixLift 342116
  have htrace : WordTrace (prefixWord ++ tailWord_342116) baseStart_342116 baseEnd_342116 := by
    simpa [prefixWord, tailWord_342116, baseEnd_342116] using wordTrace_append hprefix tailTrace_342116
  have hstable : (prefixWord ++ tailWord_342116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342116).length < 2 ^ (prefixWord ++ tailWord_342116).sum := by decide
  have hdescent : baseEnd_342116 < baseStart_342116 := by decide
  rcases family_descends (prefixWord ++ tailWord_342116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342130 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 1, 4, 2]
def baseStart_342130 : Nat := 118140960795 + 342130 * 2 ^ 59
def prefixEnd_342130 : Nat := 4983230072969 + 3 ^ 40 * 342130 * 2
def baseEnd_342130 : Nat := 175677136322851648501579

theorem tailTrace_342130 : CollatzResearch.WordTrace tailWord_342130 prefixEnd_342130 175677136322851648501579 := by
  unfold tailWord_342130
  simp only [CollatzResearch.WordTrace]
  refine ⟨3119626562632228999291961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8319004167019277331445229 3119626562632228999291961)
  ·
    refine ⟨2339719921974171749468971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3119626562632228999291961 2339719921974171749468971)
    ·
      refine ⟨3509579882961257624203457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2339719921974171749468971 3509579882961257624203457)
      ·
        refine ⟨2632184912220943218152593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3509579882961257624203457 2632184912220943218152593)
        ·
          refine ⟨1974138684165707413614445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2632184912220943218152593 1974138684165707413614445)
          ·
            refine ⟨740302006562140280105417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1974138684165707413614445 740302006562140280105417)
            ·
              refine ⟨555226504921605210079063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740302006562140280105417 555226504921605210079063)
              ·
                refine ⟨832839757382407815118595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 555226504921605210079063 832839757382407815118595)
                ·
                  refine ⟨1249259636073611722677893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832839757382407815118595 1249259636073611722677893)
                  ·
                    refine ⟨234236181763802198002105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1249259636073611722677893 234236181763802198002105)
                    ·
                      refine ⟨175677136322851648501579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 234236181763802198002105 175677136322851648501579)
                      ·
                        rfl

theorem cell23_342130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_342130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342130 prefixEnd_342130 := by exact prefixLift 342130
  have htrace : WordTrace (prefixWord ++ tailWord_342130) baseStart_342130 baseEnd_342130 := by
    simpa [prefixWord, tailWord_342130, baseEnd_342130] using wordTrace_append hprefix tailTrace_342130
  have hstable : (prefixWord ++ tailWord_342130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342130).length < 2 ^ (prefixWord ++ tailWord_342130).sum := by decide
  have hdescent : baseEnd_342130 < baseStart_342130 := by decide
  rcases family_descends (prefixWord ++ tailWord_342130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342153 : List Nat := [1, 2, 1, 1, 4, 2, 4, 3, 5]
def baseStart_342153 : Nat := 118140960795 + 342153 * 2 ^ 59
def prefixEnd_342153 : Nat := 4983230072969 + 3 ^ 40 * 342153 * 2
def baseEnd_342153 : Nat := 19520994041989450945997

theorem tailTrace_342153 : CollatzResearch.WordTrace tailWord_342153 prefixEnd_342153 19520994041989450945997 := by
  unfold tailWord_342153
  simp only [CollatzResearch.WordTrace]
  refine ⟨12479345129445590925255113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8319563419630393950170075 12479345129445590925255113)
  ·
    refine ⟨9359508847084193193941335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12479345129445590925255113 9359508847084193193941335)
    ·
      refine ⟨14039263270626289790912003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9359508847084193193941335 14039263270626289790912003)
      ·
        refine ⟨21058894905939434686368005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14039263270626289790912003 21058894905939434686368005)
        ·
          refine ⟨3948542794863644003694001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21058894905939434686368005 3948542794863644003694001)
          ·
            refine ⟨2961407096147733002770501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3948542794863644003694001 2961407096147733002770501)
            ·
              refine ⟨555263830527699938019469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2961407096147733002770501 555263830527699938019469)
              ·
                refine ⟨208223936447887476757301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 555263830527699938019469 208223936447887476757301)
                ·
                  refine ⟨19520994041989450945997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 208223936447887476757301 19520994041989450945997)
                  ·
                    rfl

theorem cell23_342153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 5].length) (baseStart_342153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342153 prefixEnd_342153 := by exact prefixLift 342153
  have htrace : WordTrace (prefixWord ++ tailWord_342153) baseStart_342153 baseEnd_342153 := by
    simpa [prefixWord, tailWord_342153, baseEnd_342153] using wordTrace_append hprefix tailTrace_342153
  have hstable : (prefixWord ++ tailWord_342153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342153).length < 2 ^ (prefixWord ++ tailWord_342153).sum := by decide
  have hdescent : baseEnd_342153 < baseStart_342153 := by decide
  rcases family_descends (prefixWord ++ tailWord_342153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342164 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_342164 : Nat := 118140960795 + 342164 * 2 ^ 59
def prefixEnd_342164 : Nat := 4983230072969 + 3 ^ 40 * 342164 * 2
def baseEnd_342164 : Nat := 175694594665104515476423

theorem tailTrace_342164 : CollatzResearch.WordTrace tailWord_342164 prefixEnd_342164 175694594665104515476423 := by
  unfold tailWord_342164
  simp only [CollatzResearch.WordTrace]
  refine ⟨6239873166202869901952773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8319830888270493202603697 6239873166202869901952773)
  ·
    refine ⟨1169976218663038106616145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6239873166202869901952773 1169976218663038106616145)
    ·
      refine ⟨877482163997278579962109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1169976218663038106616145 877482163997278579962109)
      ·
        refine ⟨329055811498979467485791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 877482163997278579962109 329055811498979467485791)
        ·
          refine ⟨493583717248469201228687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329055811498979467485791 493583717248469201228687)
          ·
            refine ⟨740375575872703801843031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493583717248469201228687 740375575872703801843031)
            ·
              refine ⟨1110563363809055702764547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740375575872703801843031 1110563363809055702764547)
              ·
                refine ⟨1665845045713583554146821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110563363809055702764547 1665845045713583554146821)
                ·
                  refine ⟨312345946071296916402529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1665845045713583554146821 312345946071296916402529)
                  ·
                    refine ⟨234259459553472687301897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 312345946071296916402529 234259459553472687301897)
                    ·
                      refine ⟨175694594665104515476423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 234259459553472687301897 175694594665104515476423)
                      ·
                        rfl

theorem cell23_342164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_342164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342164 prefixEnd_342164 := by exact prefixLift 342164
  have htrace : WordTrace (prefixWord ++ tailWord_342164) baseStart_342164 baseEnd_342164 := by
    simpa [prefixWord, tailWord_342164, baseEnd_342164] using wordTrace_append hprefix tailTrace_342164
  have hstable : (prefixWord ++ tailWord_342164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342164).length < 2 ^ (prefixWord ++ tailWord_342164).sum := by decide
  have hdescent : baseEnd_342164 < baseStart_342164 := by decide
  rcases family_descends (prefixWord ++ tailWord_342164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342223 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 3]
def baseStart_342223 : Nat := 118140960795 + 342223 * 2 ^ 59
def prefixEnd_342223 : Nat := 4983230072969 + 3 ^ 40 * 342223 * 2
def baseEnd_342223 : Nat := 175724890023719784638651

theorem tailTrace_342223 : CollatzResearch.WordTrace tailWord_342223 prefixEnd_342223 175724890023719784638651 := by
  unfold tailWord_342223
  simp only [CollatzResearch.WordTrace]
  refine ⟨12481898239191992880303323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8321265492794661920202215 12481898239191992880303323)
  ·
    refine ⟨18722847358787989320454985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12481898239191992880303323 18722847358787989320454985)
    ·
      refine ⟨14042135519090991990341239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18722847358787989320454985 14042135519090991990341239)
      ·
        refine ⟨21063203278636487985511859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14042135519090991990341239 21063203278636487985511859)
        ·
          refine ⟨31594804917954731978267789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21063203278636487985511859 31594804917954731978267789)
          ·
            refine ⟨11848051844233024491850421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31594804917954731978267789 11848051844233024491850421)
            ·
              refine ⟨1110754860396846046110977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11848051844233024491850421 1110754860396846046110977)
              ·
                refine ⟨833066145297634534583233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1110754860396846046110977 833066145297634534583233)
                ·
                  refine ⟨624799608973225900937425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 833066145297634534583233 624799608973225900937425)
                  ·
                    refine ⟨468599706729919425703069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 624799608973225900937425 468599706729919425703069)
                    ·
                      refine ⟨175724890023719784638651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 468599706729919425703069 175724890023719784638651)
                      ·
                        rfl

theorem cell23_342223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 3].length) (baseStart_342223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342223 prefixEnd_342223 := by exact prefixLift 342223
  have htrace : WordTrace (prefixWord ++ tailWord_342223) baseStart_342223 baseEnd_342223 := by
    simpa [prefixWord, tailWord_342223, baseEnd_342223] using wordTrace_append hprefix tailTrace_342223
  have hstable : (prefixWord ++ tailWord_342223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342223).length < 2 ^ (prefixWord ++ tailWord_342223).sum := by decide
  have hdescent : baseEnd_342223 < baseStart_342223 := by decide
  rcases family_descends (prefixWord ++ tailWord_342223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342293 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_342293 : Nat := 118140960795 + 342293 * 2 ^ 59
def prefixEnd_342293 : Nat := 4983230072969 + 3 ^ 40 * 342293 * 2
def baseEnd_342293 : Nat := 175760833669534510763329

theorem tailTrace_342293 : CollatzResearch.WordTrace tailWord_342293 prefixEnd_342293 175760833669534510763329 := by
  unfold tailWord_342293
  simp only [CollatzResearch.WordTrace]
  refine ⟨12484451348938394835351533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8322967565958929890234355 12484451348938394835351533)
  ·
    refine ⟨4681669255851898063256825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12484451348938394835351533 4681669255851898063256825)
    ·
      refine ⟨3511251941888923547442619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4681669255851898063256825 3511251941888923547442619)
      ·
        refine ⟨5266877912833385321163929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3511251941888923547442619 5266877912833385321163929)
        ·
          refine ⟨3950158434625038990872947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5266877912833385321163929 3950158434625038990872947)
          ·
            refine ⟨5925237651937558486309421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3950158434625038990872947 5925237651937558486309421)
            ·
              refine ⟨2221964119476584432366033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5925237651937558486309421 2221964119476584432366033)
              ·
                refine ⟨1666473089607438324274525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2221964119476584432366033 1666473089607438324274525)
                ·
                  refine ⟨624927408602789371602947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1666473089607438324274525 624927408602789371602947)
                  ·
                    refine ⟨937391112904184057404421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 624927408602789371602947 937391112904184057404421)
                    ·
                      refine ⟨175760833669534510763329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 937391112904184057404421 175760833669534510763329)
                      ·
                        rfl

theorem cell23_342293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_342293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342293 prefixEnd_342293 := by exact prefixLift 342293
  have htrace : WordTrace (prefixWord ++ tailWord_342293) baseStart_342293 baseEnd_342293 := by
    simpa [prefixWord, tailWord_342293, baseEnd_342293] using wordTrace_append hprefix tailTrace_342293
  have hstable : (prefixWord ++ tailWord_342293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342293).length < 2 ^ (prefixWord ++ tailWord_342293).sum := by decide
  have hdescent : baseEnd_342293 < baseStart_342293 := by decide
  rcases family_descends (prefixWord ++ tailWord_342293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342303 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 1, 6]
def baseStart_342303 : Nat := 118140960795 + 342303 * 2 ^ 59
def prefixEnd_342303 : Nat := 4983230072969 + 3 ^ 40 * 342303 * 2
def baseEnd_342303 : Nat := 58588656158693157212761

theorem tailTrace_342303 : CollatzResearch.WordTrace tailWord_342303 prefixEnd_342303 58588656158693157212761 := by
  unfold tailWord_342303
  simp only [CollatzResearch.WordTrace]
  refine ⟨12484816078902166543215563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8323210719268111028810375 12484816078902166543215563)
  ·
    refine ⟨18727224118353249814823345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12484816078902166543215563 18727224118353249814823345)
    ·
      refine ⟨14045418088764937361117509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18727224118353249814823345 14045418088764937361117509)
      ·
        refine ⟨2633515891643425755209533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14045418088764937361117509 2633515891643425755209533)
        ·
          refine ⟨987568459366284658203575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2633515891643425755209533 987568459366284658203575)
          ·
            refine ⟨1481352689049426987305363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987568459366284658203575 1481352689049426987305363)
            ·
              refine ⟨2222029033574140480958045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481352689049426987305363 2222029033574140480958045)
              ·
                refine ⟨833260887590302680359267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2222029033574140480958045 833260887590302680359267)
                ·
                  refine ⟨1249891331385454020538901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833260887590302680359267 1249891331385454020538901)
                  ·
                    refine ⟨58588656158693157212761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1249891331385454020538901 58588656158693157212761)
                    ·
                      rfl

theorem cell23_342303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 6].length) (baseStart_342303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342303 prefixEnd_342303 := by exact prefixLift 342303
  have htrace : WordTrace (prefixWord ++ tailWord_342303) baseStart_342303 baseEnd_342303 := by
    simpa [prefixWord, tailWord_342303, baseEnd_342303] using wordTrace_append hprefix tailTrace_342303
  have hstable : (prefixWord ++ tailWord_342303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342303).length < 2 ^ (prefixWord ++ tailWord_342303).sum := by decide
  have hdescent : baseEnd_342303 < baseStart_342303 := by decide
  rcases family_descends (prefixWord ++ tailWord_342303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342316 : List Nat := [2, 2, 1, 1, 1, 3, 2, 11]
def baseStart_342316 : Nat := 118140960795 + 342316 * 2 ^ 59
def prefixEnd_342316 : Nat := 4983230072969 + 3 ^ 40 * 342316 * 2
def baseEnd_342316 : Nat := 6510097915725478547249

theorem tailTrace_342316 : CollatzResearch.WordTrace tailWord_342316 prefixEnd_342316 6510097915725478547249 := by
  unfold tailWord_342316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6242645113927534881719401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8323526818570046508959201 6242645113927534881719401)
  ·
    refine ⟨4681983835445651161289551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6242645113927534881719401 4681983835445651161289551)
    ·
      refine ⟨7022975753168476741934327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4681983835445651161289551 7022975753168476741934327)
      ·
        refine ⟨10534463629752715112901491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7022975753168476741934327 10534463629752715112901491)
        ·
          refine ⟨15801695444629072669352237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10534463629752715112901491 15801695444629072669352237)
          ·
            refine ⟨5925635791735902251007089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15801695444629072669352237 5925635791735902251007089)
            ·
              refine ⟨4444226843801926688255317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5925635791735902251007089 4444226843801926688255317)
              ·
                refine ⟨6510097915725478547249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 4444226843801926688255317 6510097915725478547249)
                ·
                  rfl

theorem cell23_342316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 11].length) (baseStart_342316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342316 prefixEnd_342316 := by exact prefixLift 342316
  have htrace : WordTrace (prefixWord ++ tailWord_342316) baseStart_342316 baseEnd_342316 := by
    simpa [prefixWord, tailWord_342316, baseEnd_342316] using wordTrace_append hprefix tailTrace_342316
  have hstable : (prefixWord ++ tailWord_342316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342316).length < 2 ^ (prefixWord ++ tailWord_342316).sum := by decide
  have hdescent : baseEnd_342316 < baseStart_342316 := by decide
  rcases family_descends (prefixWord ++ tailWord_342316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342323 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 4]
def baseStart_342323 : Nat := 118140960795 + 342323 * 2 ^ 59
def prefixEnd_342323 : Nat := 4983230072969 + 3 ^ 40 * 342323 * 2
def baseEnd_342323 : Nat := 175776238089169393388191

theorem tailTrace_342323 : CollatzResearch.WordTrace tailWord_342323 prefixEnd_342323 175776238089169393388191 := by
  unfold tailWord_342323
  simp only [CollatzResearch.WordTrace]
  refine ⟨12485545538829709958943623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8323697025886473305962415 12485545538829709958943623)
  ·
    refine ⟨18728318308244564938415435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12485545538829709958943623 18728318308244564938415435)
    ·
      refine ⟨28092477462366847407623153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18728318308244564938415435 28092477462366847407623153)
      ·
        refine ⟨21069358096775135555717365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28092477462366847407623153 21069358096775135555717365)
        ·
          refine ⟨1975252321572668958348503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21069358096775135555717365 1975252321572668958348503)
          ·
            refine ⟨2962878482359003437522755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1975252321572668958348503 2962878482359003437522755)
            ·
              refine ⟨4444317723538505156284133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2962878482359003437522755 4444317723538505156284133)
              ·
                refine ⟨833309573163469716803275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4444317723538505156284133 833309573163469716803275)
                ·
                  refine ⟨1249964359745204575204913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833309573163469716803275 1249964359745204575204913)
                  ·
                    refine ⟨937473269808903431403685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1249964359745204575204913 937473269808903431403685)
                    ·
                      refine ⟨175776238089169393388191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 937473269808903431403685 175776238089169393388191)
                      ·
                        rfl

theorem cell23_342323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_342323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342323 prefixEnd_342323 := by exact prefixLift 342323
  have htrace : WordTrace (prefixWord ++ tailWord_342323) baseStart_342323 baseEnd_342323 := by
    simpa [prefixWord, tailWord_342323, baseEnd_342323] using wordTrace_append hprefix tailTrace_342323
  have hstable : (prefixWord ++ tailWord_342323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342323).length < 2 ^ (prefixWord ++ tailWord_342323).sum := by decide
  have hdescent : baseEnd_342323 < baseStart_342323 := by decide
  rcases family_descends (prefixWord ++ tailWord_342323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342324 : List Nat := [2, 5, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_342324 : Nat := 118140960795 + 342324 * 2 ^ 59
def prefixEnd_342324 : Nat := 4983230072969 + 3 ^ 40 * 342324 * 2
def baseEnd_342324 : Nat := 58592250523274629825229

theorem tailTrace_342324 : CollatzResearch.WordTrace tailWord_342324 prefixEnd_342324 58592250523274629825229 := by
  unfold tailWord_342324
  simp only [CollatzResearch.WordTrace]
  refine ⟨6242791005913043564865013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8323721341217391419820017 6242791005913043564865013)
  ·
    refine ⟨585261656804347834206095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6242791005913043564865013 585261656804347834206095)
    ·
      refine ⟨877892485206521751309143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 585261656804347834206095 877892485206521751309143)
      ·
        refine ⟨1316838727809782626963715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 877892485206521751309143 1316838727809782626963715)
        ·
          refine ⟨1975258091714673940445573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316838727809782626963715 1975258091714673940445573)
          ·
            refine ⟨370360892196501363833545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1975258091714673940445573 370360892196501363833545)
            ·
              refine ⟨277770669147376022875159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370360892196501363833545 277770669147376022875159)
              ·
                refine ⟨416656003721064034312739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277770669147376022875159 416656003721064034312739)
                ·
                  refine ⟨624984005581596051469109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416656003721064034312739 624984005581596051469109)
                  ·
                    refine ⟨58592250523274629825229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 624984005581596051469109 58592250523274629825229)
                    ·
                      rfl

theorem cell23_342324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_342324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342324 prefixEnd_342324 := by exact prefixLift 342324
  have htrace : WordTrace (prefixWord ++ tailWord_342324) baseStart_342324 baseEnd_342324 := by
    simpa [prefixWord, tailWord_342324, baseEnd_342324] using wordTrace_append hprefix tailTrace_342324
  have hstable : (prefixWord ++ tailWord_342324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342324).length < 2 ^ (prefixWord ++ tailWord_342324).sum := by decide
  have hdescent : baseEnd_342324 < baseStart_342324 := by decide
  rcases family_descends (prefixWord ++ tailWord_342324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342337 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 4, 4]
def baseStart_342337 : Nat := 118140960795 + 342337 * 2 ^ 59
def prefixEnd_342337 : Nat := 4983230072969 + 3 ^ 40 * 342337 * 2
def baseEnd_342337 : Nat := 58594475606110779537709

theorem tailTrace_342337 : CollatzResearch.WordTrace tailWord_342337 prefixEnd_342337 58594475606110779537709 := by
  unfold tailWord_342337
  simp only [CollatzResearch.WordTrace]
  refine ⟨12486056160778990349953265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8324037440519326899968843 12486056160778990349953265)
  ·
    refine ⟨9364542120584242762464949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12486056160778990349953265 9364542120584242762464949)
    ·
      refine ⟨877925823804772758981089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9364542120584242762464949 877925823804772758981089)
      ·
        refine ⟨658444367853579569235817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 877925823804772758981089 658444367853579569235817)
        ·
          refine ⟨493833275890184676926863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 658444367853579569235817 493833275890184676926863)
          ·
            refine ⟨740749913835277015390295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493833275890184676926863 740749913835277015390295)
            ·
              refine ⟨1111124870752915523085443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740749913835277015390295 1111124870752915523085443)
              ·
                refine ⟨1666687306129373284628165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111124870752915523085443 1666687306129373284628165)
                ·
                  refine ⟨312503869899257490867781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1666687306129373284628165 312503869899257490867781)
                  ·
                    refine ⟨58594475606110779537709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 312503869899257490867781 58594475606110779537709)
                    ·
                      rfl

theorem cell23_342337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_342337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342337 prefixEnd_342337 := by exact prefixLift 342337
  have htrace : WordTrace (prefixWord ++ tailWord_342337) baseStart_342337 baseEnd_342337 := by
    simpa [prefixWord, tailWord_342337, baseEnd_342337] using wordTrace_append hprefix tailTrace_342337
  have hstable : (prefixWord ++ tailWord_342337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342337).length < 2 ^ (prefixWord ++ tailWord_342337).sum := by decide
  have hdescent : baseEnd_342337 < baseStart_342337 := by decide
  rcases family_descends (prefixWord ++ tailWord_342337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342344 : List Nat := [2, 1, 3, 1, 1, 2, 4, 4, 1, 2, 2]
def baseStart_342344 : Nat := 118140960795 + 342344 * 2 ^ 59
def prefixEnd_342344 : Nat := 4983230072969 + 3 ^ 40 * 342344 * 2
def baseEnd_342344 : Nat := 175787021182913811225595

theorem tailTrace_342344 : CollatzResearch.WordTrace tailWord_342344 prefixEnd_342344 175787021182913811225595 := by
  unfold tailWord_342344
  simp only [CollatzResearch.WordTrace]
  refine ⟨6243155735876815272729043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8324207647835753696972057 6243155735876815272729043)
  ·
    refine ⟨9364733603815222909093565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6243155735876815272729043 9364733603815222909093565)
    ·
      refine ⟨3511775101430708590910087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9364733603815222909093565 3511775101430708590910087)
      ·
        refine ⟨5267662652146062886365131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3511775101430708590910087 5267662652146062886365131)
        ·
          refine ⟨7901493978219094329547697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5267662652146062886365131 7901493978219094329547697)
          ·
            refine ⟨5926120483664320747160773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7901493978219094329547697 5926120483664320747160773)
            ·
              refine ⟨1111147590687060140092645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5926120483664320747160773 1111147590687060140092645)
              ·
                refine ⟨208340173253823776267371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1111147590687060140092645 208340173253823776267371)
                ·
                  refine ⟨312510259880735664401057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208340173253823776267371 312510259880735664401057)
                  ·
                    refine ⟨234382694910551748300793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 312510259880735664401057 234382694910551748300793)
                    ·
                      refine ⟨175787021182913811225595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 234382694910551748300793 175787021182913811225595)
                      ·
                        rfl

theorem cell23_342344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_342344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342344 prefixEnd_342344 := by exact prefixLift 342344
  have htrace : WordTrace (prefixWord ++ tailWord_342344) baseStart_342344 baseEnd_342344 := by
    simpa [prefixWord, tailWord_342344, baseEnd_342344] using wordTrace_append hprefix tailTrace_342344
  have hstable : (prefixWord ++ tailWord_342344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342344).length < 2 ^ (prefixWord ++ tailWord_342344).sum := by decide
  have hdescent : baseEnd_342344 < baseStart_342344 := by decide
  rcases family_descends (prefixWord ++ tailWord_342344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342357 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 1, 2, 4]
def baseStart_342357 : Nat := 118140960795 + 342357 * 2 ^ 59
def prefixEnd_342357 : Nat := 4983230072969 + 3 ^ 40 * 342357 * 2
def baseEnd_342357 : Nat := 175793696431422260363035

theorem tailTrace_342357 : CollatzResearch.WordTrace tailWord_342357 prefixEnd_342357 175793696431422260363035 := by
  unfold tailWord_342357
  simp only [CollatzResearch.WordTrace]
  refine ⟨12486785620706533765681325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8324523747137689177120883 12486785620706533765681325)
  ·
    refine ⟨4682544607764950162130497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12486785620706533765681325 4682544607764950162130497)
    ·
      refine ⟨3511908455823712621597873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4682544607764950162130497 3511908455823712621597873)
      ·
        refine ⟨2633931341867784466198405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3511908455823712621597873 2633931341867784466198405)
        ·
          refine ⟨493862126600209587412201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2633931341867784466198405 493862126600209587412201)
          ·
            refine ⟨370396594950157190559151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493862126600209587412201 370396594950157190559151)
            ·
              refine ⟨555594892425235785838727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370396594950157190559151 555594892425235785838727)
              ·
                refine ⟨833392338637853678758091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 555594892425235785838727 833392338637853678758091)
                ·
                  refine ⟨1250088507956780518137137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 833392338637853678758091 1250088507956780518137137)
                  ·
                    refine ⟨937566380967585388602853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1250088507956780518137137 937566380967585388602853)
                    ·
                      refine ⟨175793696431422260363035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 937566380967585388602853 175793696431422260363035)
                      ·
                        rfl

theorem cell23_342357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_342357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342357 prefixEnd_342357 := by exact prefixLift 342357
  have htrace : WordTrace (prefixWord ++ tailWord_342357) baseStart_342357 baseEnd_342357 := by
    simpa [prefixWord, tailWord_342357, baseEnd_342357] using wordTrace_append hprefix tailTrace_342357
  have hstable : (prefixWord ++ tailWord_342357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342357).length < 2 ^ (prefixWord ++ tailWord_342357).sum := by decide
  have hdescent : baseEnd_342357 < baseStart_342357 := by decide
  rcases family_descends (prefixWord ++ tailWord_342357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342373 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_342373 : Nat := 118140960795 + 342373 * 2 ^ 59
def prefixEnd_342373 : Nat := 4983230072969 + 3 ^ 40 * 342373 * 2
def baseEnd_342373 : Nat := 175801912121894197762961

theorem tailTrace_342373 : CollatzResearch.WordTrace tailWord_342373 prefixEnd_342373 175801912121894197762961 := by
  unfold tailWord_342373
  simp only [CollatzResearch.WordTrace]
  refine ⟨12487369188648568498263773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8324912792432378998842515 12487369188648568498263773)
  ·
    refine ⟨4682763445743213186848915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12487369188648568498263773 4682763445743213186848915)
    ·
      refine ⟨7024145168614819780273373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4682763445743213186848915 7024145168614819780273373)
      ·
        refine ⟨2634054438230557417602515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7024145168614819780273373 2634054438230557417602515)
        ·
          refine ⟨3951081657345836126403773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2634054438230557417602515 3951081657345836126403773)
          ·
            refine ⟨1481655621504688547401415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3951081657345836126403773 1481655621504688547401415)
            ·
              refine ⟨2222483432257032821102123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1481655621504688547401415 2222483432257032821102123)
              ·
                refine ⟨3333725148385549231653185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2222483432257032821102123 3333725148385549231653185)
                ·
                  refine ⟨2500293861289161923739889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3333725148385549231653185 2500293861289161923739889)
                  ·
                    refine ⟨1875220395966871442804917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2500293861289161923739889 1875220395966871442804917)
                    ·
                      refine ⟨175801912121894197762961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1875220395966871442804917 175801912121894197762961)
                      ·
                        rfl

theorem cell23_342373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_342373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342373 prefixEnd_342373 := by exact prefixLift 342373
  have htrace : WordTrace (prefixWord ++ tailWord_342373) baseStart_342373 baseEnd_342373 := by
    simpa [prefixWord, tailWord_342373, baseEnd_342373] using wordTrace_append hprefix tailTrace_342373
  have hstable : (prefixWord ++ tailWord_342373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342373).length < 2 ^ (prefixWord ++ tailWord_342373).sum := by decide
  have hdescent : baseEnd_342373 < baseStart_342373 := by decide
  rcases family_descends (prefixWord ++ tailWord_342373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342378 : List Nat := [3, 1, 3, 3, 1, 3, 1, 3, 1, 2, 2]
def baseStart_342378 : Nat := 118140960795 + 342378 * 2 ^ 59
def prefixEnd_342378 : Nat := 4983230072969 + 3 ^ 40 * 342378 * 2
def baseEnd_342378 : Nat := 175804479525166678200439

theorem tailTrace_342378 : CollatzResearch.WordTrace tailWord_342378 prefixEnd_342378 175804479525166678200439 := by
  unfold tailWord_342378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3121887888407613588048947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8325034369086969568130525 3121887888407613588048947)
  ·
    refine ⟨4682831832611420382073421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3121887888407613588048947 4682831832611420382073421)
    ·
      refine ⟨1756061937229282643277533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4682831832611420382073421 1756061937229282643277533)
      ·
        refine ⟨658523226460980991229075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1756061937229282643277533 658523226460980991229075)
        ·
          refine ⟨987784839691471486843613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658523226460980991229075 987784839691471486843613)
          ·
            refine ⟨370419314884301807566355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 987784839691471486843613 370419314884301807566355)
            ·
              refine ⟨555628972326452711349533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370419314884301807566355 555628972326452711349533)
              ·
                refine ⟨208360864622419766756075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 555628972326452711349533 208360864622419766756075)
                ·
                  refine ⟨312541296933629650134113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208360864622419766756075 312541296933629650134113)
                  ·
                    refine ⟨234405972700222237600585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 312541296933629650134113 234405972700222237600585)
                    ·
                      refine ⟨175804479525166678200439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 234405972700222237600585 175804479525166678200439)
                      ·
                        rfl

theorem cell23_342378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_342378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342378 prefixEnd_342378 := by exact prefixLift 342378
  have htrace : WordTrace (prefixWord ++ tailWord_342378) baseStart_342378 baseEnd_342378 := by
    simpa [prefixWord, tailWord_342378, baseEnd_342378] using wordTrace_append hprefix tailTrace_342378
  have hstable : (prefixWord ++ tailWord_342378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342378).length < 2 ^ (prefixWord ++ tailWord_342378).sum := by decide
  have hdescent : baseEnd_342378 < baseStart_342378 := by decide
  rcases family_descends (prefixWord ++ tailWord_342378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342423 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 7]
def baseStart_342423 : Nat := 118140960795 + 342423 * 2 ^ 59
def prefixEnd_342423 : Nat := 4983230072969 + 3 ^ 40 * 342423 * 2
def baseEnd_342423 : Nat := 19536398461624333570859

theorem tailTrace_342423 : CollatzResearch.WordTrace tailWord_342423 prefixEnd_342423 19536398461624333570859 := by
  unfold tailWord_342423
  simp only [CollatzResearch.WordTrace]
  refine ⟨12489192838467427037583923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8326128558978284691722615 12489192838467427037583923)
  ·
    refine ⟨18733789257701140556375885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12489192838467427037583923 18733789257701140556375885)
    ·
      refine ⟨7025170971637927708640957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18733789257701140556375885 7025170971637927708640957)
      ·
        refine ⟨2634439114364222890740359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7025170971637927708640957 2634439114364222890740359)
        ·
          refine ⟨3951658671546334336110539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2634439114364222890740359 3951658671546334336110539)
          ·
            refine ⟨5927488007319501504165809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3951658671546334336110539 5927488007319501504165809)
            ·
              refine ⟨4445616005489626128124357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5927488007319501504165809 4445616005489626128124357)
              ·
                refine ⟨833553001029304899023317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4445616005489626128124357 833553001029304899023317)
                ·
                  refine ⟨19536398461624333570859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 833553001029304899023317 19536398461624333570859)
                  ·
                    rfl

theorem cell23_342423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 7].length) (baseStart_342423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342423 prefixEnd_342423 := by exact prefixLift 342423
  have htrace : WordTrace (prefixWord ++ tailWord_342423) baseStart_342423 baseEnd_342423 := by
    simpa [prefixWord, tailWord_342423, baseEnd_342423] using wordTrace_append hprefix tailTrace_342423
  have hstable : (prefixWord ++ tailWord_342423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342423).length < 2 ^ (prefixWord ++ tailWord_342423).sum := by decide
  have hdescent : baseEnd_342423 < baseStart_342423 := by decide
  rcases family_descends (prefixWord ++ tailWord_342423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342450 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_342450 : Nat := 118140960795 + 342450 * 2 ^ 59
def prefixEnd_342450 : Nat := 4983230072969 + 3 ^ 40 * 342450 * 2
def baseEnd_342450 : Nat := 175841450132290396500107

theorem tailTrace_342450 : CollatzResearch.WordTrace tailWord_342450 prefixEnd_342450 175841450132290396500107 := by
  unfold tailWord_342450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3122544402342402662204201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8326785072913073765877869 3122544402342402662204201)
  ·
    refine ⟨2341908301756801996653151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3122544402342402662204201 2341908301756801996653151)
    ·
      refine ⟨3512862452635202994979727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2341908301756801996653151 3512862452635202994979727)
      ·
        refine ⟨5269293678952804492469591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512862452635202994979727 5269293678952804492469591)
        ·
          refine ⟨7903940518429206738704387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5269293678952804492469591 7903940518429206738704387)
          ·
            refine ⟨11855910777643810108056581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7903940518429206738704387 11855910777643810108056581)
            ·
              refine ⟨2222983270808214395260609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11855910777643810108056581 2222983270808214395260609)
              ·
                refine ⟨1667237453106160796445457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2222983270808214395260609 1667237453106160796445457)
                ·
                  refine ⟨1250428089829620597334093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1667237453106160796445457 1250428089829620597334093)
                  ·
                    refine ⟨468910533686107724000285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1250428089829620597334093 468910533686107724000285)
                    ·
                      refine ⟨175841450132290396500107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 468910533686107724000285 175841450132290396500107)
                      ·
                        rfl

theorem cell23_342450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_342450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342450 prefixEnd_342450 := by exact prefixLift 342450
  have htrace : WordTrace (prefixWord ++ tailWord_342450) baseStart_342450 baseEnd_342450 := by
    simpa [prefixWord, tailWord_342450, baseEnd_342450] using wordTrace_append hprefix tailTrace_342450
  have hstable : (prefixWord ++ tailWord_342450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342450).length < 2 ^ (prefixWord ++ tailWord_342450).sum := by decide
  have hdescent : baseEnd_342450 < baseStart_342450 := by decide
  rcases family_descends (prefixWord ++ tailWord_342450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342457 : List Nat := [1, 2, 1, 4, 3, 2, 1, 4, 5]
def baseStart_342457 : Nat := 118140960795 + 342457 * 2 ^ 59
def prefixEnd_342457 : Nat := 4983230072969 + 3 ^ 40 * 342457 * 2
def baseEnd_342457 : Nat := 19538338277430207679175

theorem tailTrace_342457 : CollatzResearch.WordTrace tailWord_342457 prefixEnd_342457 19538338277430207679175 := by
  unfold tailWord_342457
  simp only [CollatzResearch.WordTrace]
  refine ⟨12490432920344250844321625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8326955280229500562881083 12490432920344250844321625)
  ·
    refine ⟨9367824690258188133241219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12490432920344250844321625 9367824690258188133241219)
    ·
      refine ⟨14051737035387282199861829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9367824690258188133241219 14051737035387282199861829)
      ·
        refine ⟨2634700694135115412474093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14051737035387282199861829 2634700694135115412474093)
        ·
          refine ⟨988012760300668279677785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2634700694135115412474093 988012760300668279677785)
          ·
            refine ⟨741009570225501209758339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 988012760300668279677785 741009570225501209758339)
            ·
              refine ⟨1111514355338251814637509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741009570225501209758339 1111514355338251814637509)
              ·
                refine ⟨208408941625922215244533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1111514355338251814637509 208408941625922215244533)
                ·
                  refine ⟨19538338277430207679175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 208408941625922215244533 19538338277430207679175)
                  ·
                    rfl

theorem cell23_342457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 5].length) (baseStart_342457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342457 prefixEnd_342457 := by exact prefixLift 342457
  have htrace : WordTrace (prefixWord ++ tailWord_342457) baseStart_342457 baseEnd_342457 := by
    simpa [prefixWord, tailWord_342457, baseEnd_342457] using wordTrace_append hprefix tailTrace_342457
  have hstable : (prefixWord ++ tailWord_342457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342457).length < 2 ^ (prefixWord ++ tailWord_342457).sum := by decide
  have hdescent : baseEnd_342457 < baseStart_342457 := by decide
  rcases family_descends (prefixWord ++ tailWord_342457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342490 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_342490 : Nat := 118140960795 + 342490 * 2 ^ 59
def prefixEnd_342490 : Nat := 4983230072969 + 3 ^ 40 * 342490 * 2
def baseEnd_342490 : Nat := 175861989358470239999923

theorem tailTrace_342490 : CollatzResearch.WordTrace tailWord_342490 prefixEnd_342490 175861989358470239999923 := by
  unfold tailWord_342490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3122909132306174370068231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8327757686149798320181949 3122909132306174370068231)
  ·
    refine ⟨4684363698459261555102347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3122909132306174370068231 4684363698459261555102347)
    ·
      refine ⟨7026545547688892332653521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4684363698459261555102347 7026545547688892332653521)
      ·
        refine ⟨5269909160766669249490141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7026545547688892332653521 5269909160766669249490141)
        ·
          refine ⟨1976215935287500968558803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5269909160766669249490141 1976215935287500968558803)
          ·
            refine ⟨2964323902931251452838205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1976215935287500968558803 2964323902931251452838205)
            ·
              refine ⟨1111621463599219294814327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2964323902931251452838205 1111621463599219294814327)
              ·
                refine ⟨1667432195398828942221491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111621463599219294814327 1667432195398828942221491)
                ·
                  refine ⟨2501148293098243413332237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1667432195398828942221491 2501148293098243413332237)
                  ·
                    refine ⟨937930609911841279999589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2501148293098243413332237 937930609911841279999589)
                    ·
                      refine ⟨175861989358470239999923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 937930609911841279999589 175861989358470239999923)
                      ·
                        rfl

theorem cell23_342490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_342490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342490 prefixEnd_342490 := by exact prefixLift 342490
  have htrace : WordTrace (prefixWord ++ tailWord_342490) baseStart_342490 baseEnd_342490 := by
    simpa [prefixWord, tailWord_342490, baseEnd_342490] using wordTrace_append hprefix tailTrace_342490
  have hstable : (prefixWord ++ tailWord_342490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342490).length < 2 ^ (prefixWord ++ tailWord_342490).sum := by decide
  have hdescent : baseEnd_342490 < baseStart_342490 := by decide
  rcases family_descends (prefixWord ++ tailWord_342490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342568 : List Nat := [2, 1, 5, 2, 1, 2, 3, 2, 1, 4]
def baseStart_342568 : Nat := 118140960795 + 342568 * 2 ^ 59
def prefixEnd_342568 : Nat := 4983230072969 + 3 ^ 40 * 342568 * 2
def baseEnd_342568 : Nat := 58634013616506978274855

theorem tailTrace_342568 : CollatzResearch.WordTrace tailWord_342568 prefixEnd_342568 58634013616506978274855 := by
  unfold tailWord_342568
  simp only [CollatzResearch.WordTrace]
  refine ⟨6247240711471058400806179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8329654281961411201074905 6247240711471058400806179)
  ·
    refine ⟨9370861067206587601209269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6247240711471058400806179 9370861067206587601209269)
    ·
      refine ⟨878518225050617587613369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9370861067206587601209269 878518225050617587613369)
      ·
        refine ⟨658888668787963190710027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 878518225050617587613369 658888668787963190710027)
        ·
          refine ⟨988333003181944786065041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658888668787963190710027 988333003181944786065041)
          ·
            refine ⟨741249752386458589548781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 988333003181944786065041 741249752386458589548781)
            ·
              refine ⟨277968657144921971080793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 741249752386458589548781 277968657144921971080793)
              ·
                refine ⟨208476492858691478310595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277968657144921971080793 208476492858691478310595)
                ·
                  refine ⟨312714739288037217465893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208476492858691478310595 312714739288037217465893)
                  ·
                    refine ⟨58634013616506978274855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 312714739288037217465893 58634013616506978274855)
                    ·
                      rfl

theorem cell23_342568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_342568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342568 prefixEnd_342568 := by exact prefixLift 342568
  have htrace : WordTrace (prefixWord ++ tailWord_342568) baseStart_342568 baseEnd_342568 := by
    simpa [prefixWord, tailWord_342568, baseEnd_342568] using wordTrace_append hprefix tailTrace_342568
  have hstable : (prefixWord ++ tailWord_342568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342568).length < 2 ^ (prefixWord ++ tailWord_342568).sum := by decide
  have hdescent : baseEnd_342568 < baseStart_342568 := by decide
  rcases family_descends (prefixWord ++ tailWord_342568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342597 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 3, 1, 4]
def baseStart_342597 : Nat := 118140960795 + 342597 * 2 ^ 59
def prefixEnd_342597 : Nat := 4983230072969 + 3 ^ 40 * 342597 * 2
def baseEnd_342597 : Nat := 175916931788501321361931

theorem tailTrace_342597 : CollatzResearch.WordTrace tailWord_342597 prefixEnd_342597 175916931788501321361931 := by
  unfold tailWord_342597
  simp only [CollatzResearch.WordTrace]
  refine ⟨12495539139837054754418045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8330359426558036502945363 12495539139837054754418045)
  ·
    refine ⟨4685827177438895532906767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12495539139837054754418045 4685827177438895532906767)
    ·
      refine ⟨7028740766158343299360151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4685827177438895532906767 7028740766158343299360151)
      ·
        refine ⟨10543111149237514949040227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7028740766158343299360151 10543111149237514949040227)
        ·
          refine ⟨15814666723856272423560341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10543111149237514949040227 15814666723856272423560341)
          ·
            refine ⟨741312502680762769854391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15814666723856272423560341 741312502680762769854391)
            ·
              refine ⟨1111968754021144154781587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741312502680762769854391 1111968754021144154781587)
              ·
                refine ⟨1667953131031716232172381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111968754021144154781587 1667953131031716232172381)
                ·
                  refine ⟨625482424136893587064643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1667953131031716232172381 625482424136893587064643)
                  ·
                    refine ⟨938223636205340380596965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 625482424136893587064643 938223636205340380596965)
                    ·
                      refine ⟨175916931788501321361931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 938223636205340380596965 175916931788501321361931)
                      ·
                        rfl

theorem cell23_342597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_342597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342597 prefixEnd_342597 := by exact prefixLift 342597
  have htrace : WordTrace (prefixWord ++ tailWord_342597) baseStart_342597 baseEnd_342597 := by
    simpa [prefixWord, tailWord_342597, baseEnd_342597] using wordTrace_append hprefix tailTrace_342597
  have hstable : (prefixWord ++ tailWord_342597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342597).length < 2 ^ (prefixWord ++ tailWord_342597).sum := by decide
  have hdescent : baseEnd_342597 < baseStart_342597 := by decide
  rcases family_descends (prefixWord ++ tailWord_342597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342600 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_342600 : Nat := 118140960795 + 342600 * 2 ^ 59
def prefixEnd_342600 : Nat := 4983230072969 + 3 ^ 40 * 342600 * 2
def baseEnd_342600 : Nat := 175918472230464809624417

theorem tailTrace_342600 : CollatzResearch.WordTrace tailWord_342600 prefixEnd_342600 175918472230464809624417 := by
  unfold tailWord_342600
  simp only [CollatzResearch.WordTrace]
  refine ⟨6247824279413093133388627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8330432372550790844518169 6247824279413093133388627)
  ·
    refine ⟨9371736419119639700082941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6247824279413093133388627 9371736419119639700082941)
    ·
      refine ⟨3514401157169864887531103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9371736419119639700082941 3514401157169864887531103)
      ·
        refine ⟨5271601735754797331296655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3514401157169864887531103 5271601735754797331296655)
        ·
          refine ⟨7907402603632195996944983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5271601735754797331296655 7907402603632195996944983)
          ·
            refine ⟨11861103905448293995417475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7907402603632195996944983 11861103905448293995417475)
            ·
              refine ⟨17791655858172440993126213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11861103905448293995417475 17791655858172440993126213)
              ·
                refine ⟨3335935473407332686211165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17791655858172440993126213 3335935473407332686211165)
                ·
                  refine ⟨1250975802527749757329187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3335935473407332686211165 1250975802527749757329187)
                  ·
                    refine ⟨1876463703791624635993781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1250975802527749757329187 1876463703791624635993781)
                    ·
                      refine ⟨175918472230464809624417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1876463703791624635993781 175918472230464809624417)
                      ·
                        rfl

theorem cell23_342600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_342600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342600 prefixEnd_342600 := by exact prefixLift 342600
  have htrace : WordTrace (prefixWord ++ tailWord_342600) baseStart_342600 baseEnd_342600 := by
    simpa [prefixWord, tailWord_342600, baseEnd_342600] using wordTrace_append hprefix tailTrace_342600
  have hstable : (prefixWord ++ tailWord_342600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342600).length < 2 ^ (prefixWord ++ tailWord_342600).sum := by decide
  have hdescent : baseEnd_342600 < baseStart_342600 := by decide
  rcases family_descends (prefixWord ++ tailWord_342600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342620 : List Nat := [2, 2, 4, 1, 14]
def baseStart_342620 : Nat := 118140960795 + 342620 * 2 ^ 59
def prefixEnd_342620 : Nat := 4983230072969 + 3 ^ 40 * 342620 * 2
def baseEnd_342620 : Nat := 241328863982928300925

theorem tailTrace_342620 : CollatzResearch.WordTrace tailWord_342620 prefixEnd_342620 241328863982928300925 := by
  unfold tailWord_342620
  simp only [CollatzResearch.WordTrace]
  refine ⟨6248189009376864841252657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8330918679169153121670209 6248189009376864841252657)
  ·
    refine ⟨4686141757032648630939493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6248189009376864841252657 4686141757032648630939493)
    ·
      refine ⟨878651579443621618301155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4686141757032648630939493 878651579443621618301155)
      ·
        refine ⟨1317977369165432427451733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878651579443621618301155 1317977369165432427451733)
        ·
          refine ⟨241328863982928300925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 1317977369165432427451733 241328863982928300925)
          ·
            rfl

theorem cell23_342620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 14].length) (baseStart_342620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342620 prefixEnd_342620 := by exact prefixLift 342620
  have htrace : WordTrace (prefixWord ++ tailWord_342620) baseStart_342620 baseEnd_342620 := by
    simpa [prefixWord, tailWord_342620, baseEnd_342620] using wordTrace_append hprefix tailTrace_342620
  have hstable : (prefixWord ++ tailWord_342620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342620).length < 2 ^ (prefixWord ++ tailWord_342620).sum := by decide
  have hdescent : baseEnd_342620 < baseStart_342620 := by decide
  rcases family_descends (prefixWord ++ tailWord_342620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342637 : List Nat := [1, 5, 1, 1, 3, 1, 3, 8]
def baseStart_342637 : Nat := 118140960795 + 342637 * 2 ^ 59
def prefixEnd_342637 : Nat := 4983230072969 + 3 ^ 40 * 342637 * 2
def baseEnd_342637 : Nat := 6516202630173376476361

theorem tailTrace_342637 : CollatzResearch.WordTrace tailWord_342637 prefixEnd_342637 6516202630173376476361 := by
  unfold tailWord_342637
  simp only [CollatzResearch.WordTrace]
  refine ⟨12496998059692141585874165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8331332039794761057249443 12496998059692141585874165)
  ·
    refine ⟨1171593568096138273675703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12496998059692141585874165 1171593568096138273675703)
    ·
      refine ⟨1757390352144207410513555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1171593568096138273675703 1757390352144207410513555)
      ·
        refine ⟨2636085528216311115770333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1757390352144207410513555 2636085528216311115770333)
        ·
          refine ⟨988532073081116668413875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2636085528216311115770333 988532073081116668413875)
          ·
            refine ⟨1482798109621675002620813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988532073081116668413875 1482798109621675002620813)
            ·
              refine ⟨556049291108128125982805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1482798109621675002620813 556049291108128125982805)
              ·
                refine ⟨6516202630173376476361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 556049291108128125982805 6516202630173376476361)
                ·
                  rfl

theorem cell23_342637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 8].length) (baseStart_342637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342637 prefixEnd_342637 := by exact prefixLift 342637
  have htrace : WordTrace (prefixWord ++ tailWord_342637) baseStart_342637 baseEnd_342637 := by
    simpa [prefixWord, tailWord_342637, baseEnd_342637] using wordTrace_append hprefix tailTrace_342637
  have hstable : (prefixWord ++ tailWord_342637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342637).length < 2 ^ (prefixWord ++ tailWord_342637).sum := by decide
  have hdescent : baseEnd_342637 < baseStart_342637 := by decide
  rcases family_descends (prefixWord ++ tailWord_342637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342647 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 3]
def baseStart_342647 : Nat := 118140960795 + 342647 * 2 ^ 59
def prefixEnd_342647 : Nat := 4983230072969 + 3 ^ 40 * 342647 * 2
def baseEnd_342647 : Nat := 175942605821226125736701

theorem tailTrace_342647 : CollatzResearch.WordTrace tailWord_342647 prefixEnd_342647 175942605821226125736701 := by
  unfold tailWord_342647
  simp only [CollatzResearch.WordTrace]
  refine ⟨12497362789655913293738195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8331575193103942195825463 12497362789655913293738195)
  ·
    refine ⟨18746044184483869940607293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12497362789655913293738195 18746044184483869940607293)
    ·
      refine ⟨7029766569181451227727735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18746044184483869940607293 7029766569181451227727735)
      ·
        refine ⟨10544649853772176841591603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7029766569181451227727735 10544649853772176841591603)
        ·
          refine ⟨15816974780658265262387405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10544649853772176841591603 15816974780658265262387405)
          ·
            refine ⟨5931365542746849473395277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15816974780658265262387405 5931365542746849473395277)
            ·
              refine ⟨2224262078530068552523229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5931365542746849473395277 2224262078530068552523229)
              ·
                refine ⟨834098279448775707196211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2224262078530068552523229 834098279448775707196211)
                ·
                  refine ⟨1251147419173163560794317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834098279448775707196211 1251147419173163560794317)
                  ·
                    refine ⟨469180282189936335297869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1251147419173163560794317 469180282189936335297869)
                    ·
                      refine ⟨175942605821226125736701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 469180282189936335297869 175942605821226125736701)
                      ·
                        rfl

theorem cell23_342647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_342647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342647 prefixEnd_342647 := by exact prefixLift 342647
  have htrace : WordTrace (prefixWord ++ tailWord_342647) baseStart_342647 baseEnd_342647 := by
    simpa [prefixWord, tailWord_342647, baseEnd_342647] using wordTrace_append hprefix tailTrace_342647
  have hstable : (prefixWord ++ tailWord_342647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342647).length < 2 ^ (prefixWord ++ tailWord_342647).sum := by decide
  have hdescent : baseEnd_342647 < baseStart_342647 := by decide
  rcases family_descends (prefixWord ++ tailWord_342647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342700 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_342700 : Nat := 118140960795 + 342700 * 2 ^ 59
def prefixEnd_342700 : Nat := 4983230072969 + 3 ^ 40 * 342700 * 2
def baseEnd_342700 : Nat := 175969820295914418373957

theorem tailTrace_342700 : CollatzResearch.WordTrace tailWord_342700 prefixEnd_342700 175969820295914418373957 := by
  unfold tailWord_342700
  simp only [CollatzResearch.WordTrace]
  refine ⟨6249647929231951672708777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8332863905642602230278369 6249647929231951672708777)
  ·
    refine ⟨4687235946923963754531583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6249647929231951672708777 4687235946923963754531583)
    ·
      refine ⟨7030853920385945631797375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4687235946923963754531583 7030853920385945631797375)
      ·
        refine ⟨10546280880578918447696063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7030853920385945631797375 10546280880578918447696063)
        ·
          refine ⟨15819421320868377671544095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10546280880578918447696063 15819421320868377671544095)
          ·
            refine ⟨23729131981302566507316143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15819421320868377671544095 23729131981302566507316143)
            ·
              refine ⟨35593697971953849760974215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23729131981302566507316143 35593697971953849760974215)
              ·
                refine ⟨53390546957930774641461323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35593697971953849760974215 53390546957930774641461323)
                ·
                  refine ⟨80085820436896161962191985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53390546957930774641461323 80085820436896161962191985)
                  ·
                    refine ⟨60064365327672121471643989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80085820436896161962191985 60064365327672121471643989)
                    ·
                      refine ⟨175969820295914418373957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 60064365327672121471643989 175969820295914418373957)
                      ·
                        rfl

theorem cell23_342700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_342700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342700 prefixEnd_342700 := by exact prefixLift 342700
  have htrace : WordTrace (prefixWord ++ tailWord_342700) baseStart_342700 baseEnd_342700 := by
    simpa [prefixWord, tailWord_342700, baseEnd_342700] using wordTrace_append hprefix tailTrace_342700
  have hstable : (prefixWord ++ tailWord_342700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342700).length < 2 ^ (prefixWord ++ tailWord_342700).sum := by decide
  have hdescent : baseEnd_342700 < baseStart_342700 := by decide
  rcases family_descends (prefixWord ++ tailWord_342700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342724 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_342724 : Nat := 118140960795 + 342724 * 2 ^ 59
def prefixEnd_342724 : Nat := 4983230072969 + 3 ^ 40 * 342724 * 2
def baseEnd_342724 : Nat := 175982143831622324473847

theorem tailTrace_342724 : CollatzResearch.WordTrace tailWord_342724 prefixEnd_342724 175982143831622324473847 := by
  unfold tailWord_342724
  simp only [CollatzResearch.WordTrace]
  refine ⟨6250085605188477722145613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8333447473584636962860817 6250085605188477722145613)
  ·
    refine ⟨2343782101945679145804605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6250085605188477722145613 2343782101945679145804605)
    ·
      refine ⟨878918288229629679676727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2343782101945679145804605 878918288229629679676727)
      ·
        refine ⟨1318377432344444519515091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 878918288229629679676727 1318377432344444519515091)
        ·
          refine ⟨1977566148516666779272637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1318377432344444519515091 1977566148516666779272637)
          ·
            refine ⟨741587305693750042227239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1977566148516666779272637 741587305693750042227239)
            ·
              refine ⟨1112380958540625063340859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741587305693750042227239 1112380958540625063340859)
              ·
                refine ⟨1668571437810937595011289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112380958540625063340859 1668571437810937595011289)
                ·
                  refine ⟨1251428578358203196258467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1668571437810937595011289 1251428578358203196258467)
                  ·
                    refine ⟨1877142867537304794387701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1251428578358203196258467 1877142867537304794387701)
                    ·
                      refine ⟨175982143831622324473847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1877142867537304794387701 175982143831622324473847)
                      ·
                        rfl

theorem cell23_342724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_342724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342724 prefixEnd_342724 := by exact prefixLift 342724
  have htrace : WordTrace (prefixWord ++ tailWord_342724) baseStart_342724 baseEnd_342724 := by
    simpa [prefixWord, tailWord_342724, baseEnd_342724] using wordTrace_append hprefix tailTrace_342724
  have hstable : (prefixWord ++ tailWord_342724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342724).length < 2 ^ (prefixWord ++ tailWord_342724).sum := by decide
  have hdescent : baseEnd_342724 < baseStart_342724 := by decide
  rcases family_descends (prefixWord ++ tailWord_342724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342744 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 7]
def baseStart_342744 : Nat := 118140960795 + 342744 * 2 ^ 59
def prefixEnd_342744 : Nat := 4983230072969 + 3 ^ 40 * 342744 * 2
def baseEnd_342744 : Nat := 19554712604968027358195

theorem tailTrace_342744 : CollatzResearch.WordTrace tailWord_342744 prefixEnd_342744 19554712604968027358195 := by
  unfold tailWord_342744
  simp only [CollatzResearch.WordTrace]
  refine ⟨6250450335152249430009643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8333933780202999240012857 6250450335152249430009643)
  ·
    refine ⟨9375675502728374145014465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6250450335152249430009643 9375675502728374145014465)
    ·
      refine ⟨7031756627046280608760849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9375675502728374145014465 7031756627046280608760849)
      ·
        refine ⟨5273817470284710456570637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7031756627046280608760849 5273817470284710456570637)
        ·
          refine ⟨1977681551356766421213989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5273817470284710456570637 1977681551356766421213989)
          ·
            refine ⟨370815290879393703977623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1977681551356766421213989 370815290879393703977623)
            ·
              refine ⟨556222936319090555966435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370815290879393703977623 556222936319090555966435)
              ·
                refine ⟨834334404478635833949653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556222936319090555966435 834334404478635833949653)
                ·
                  refine ⟨19554712604968027358195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 834334404478635833949653 19554712604968027358195)
                  ·
                    rfl

theorem cell23_342744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 7].length) (baseStart_342744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342744 prefixEnd_342744 := by exact prefixLift 342744
  have htrace : WordTrace (prefixWord ++ tailWord_342744) baseStart_342744 baseEnd_342744 := by
    simpa [prefixWord, tailWord_342744, baseEnd_342744] using wordTrace_append hprefix tailTrace_342744
  have hstable : (prefixWord ++ tailWord_342744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342744).length < 2 ^ (prefixWord ++ tailWord_342744).sum := by decide
  have hdescent : baseEnd_342744 < baseStart_342744 := by decide
  rcases family_descends (prefixWord ++ tailWord_342744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342755 : List Nat := [1, 1, 1, 7, 1, 1, 4, 1, 2, 2, 2]
def baseStart_342755 : Nat := 118140960795 + 342755 * 2 ^ 59
def prefixEnd_342755 : Nat := 4983230072969 + 3 ^ 40 * 342755 * 2
def baseEnd_342755 : Nat := 175998061731911703186205

theorem tailTrace_342755 : CollatzResearch.WordTrace tailWord_342755 prefixEnd_342755 175998061731911703186205 := by
  unfold tailWord_342755
  simp only [CollatzResearch.WordTrace]
  refine ⟨12501301873264647738669719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8334201248843098492446479 12501301873264647738669719)
  ·
    refine ⟨18751952809896971608004579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12501301873264647738669719 18751952809896971608004579)
    ·
      refine ⟨28127929214845457412006869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18751952809896971608004579 28127929214845457412006869)
      ·
        refine ⟨659248340972940408093911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 28127929214845457412006869 659248340972940408093911)
        ·
          refine ⟨988872511459410612140867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659248340972940408093911 988872511459410612140867)
          ·
            refine ⟨1483308767189115918211301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 988872511459410612140867 1483308767189115918211301)
            ·
              refine ⟨278120393847959234664619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1483308767189115918211301 278120393847959234664619)
              ·
                refine ⟨417180590771938851996929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278120393847959234664619 417180590771938851996929)
                ·
                  refine ⟨312885443078954138997697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417180590771938851996929 312885443078954138997697)
                  ·
                    refine ⟨234664082309215604248273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 312885443078954138997697 234664082309215604248273)
                    ·
                      refine ⟨175998061731911703186205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 234664082309215604248273 175998061731911703186205)
                      ·
                        rfl

theorem cell23_342755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_342755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342755 prefixEnd_342755 := by exact prefixLift 342755
  have htrace : WordTrace (prefixWord ++ tailWord_342755) baseStart_342755 baseEnd_342755 := by
    simpa [prefixWord, tailWord_342755, baseEnd_342755] using wordTrace_append hprefix tailTrace_342755
  have hstable : (prefixWord ++ tailWord_342755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342755).length < 2 ^ (prefixWord ++ tailWord_342755).sum := by decide
  have hdescent : baseEnd_342755 < baseStart_342755 := by decide
  rcases family_descends (prefixWord ++ tailWord_342755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342777 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 1, 3, 4]
def baseStart_342777 : Nat := 118140960795 + 342777 * 2 ^ 59
def prefixEnd_342777 : Nat := 4983230072969 + 3 ^ 40 * 342777 * 2
def baseEnd_342777 : Nat := 176009358306310617111103

theorem tailTrace_342777 : CollatzResearch.WordTrace tailWord_342777 prefixEnd_342777 176009358306310617111103 := by
  unfold tailWord_342777
  simp only [CollatzResearch.WordTrace]
  refine ⟨12502104279184945495970585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8334736186123296997313723 12502104279184945495970585)
  ·
    refine ⟨9376578209388709121977939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12502104279184945495970585 9376578209388709121977939)
    ·
      refine ⟨14064867314083063682966909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9376578209388709121977939 14064867314083063682966909)
      ·
        refine ⟨5274325242781148881112591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14064867314083063682966909 5274325242781148881112591)
        ·
          refine ⟨7911487864171723321668887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5274325242781148881112591 7911487864171723321668887)
          ·
            refine ⟨11867231796257584982503331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7911487864171723321668887 11867231796257584982503331)
            ·
              refine ⟨17800847694386377473754997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11867231796257584982503331 17800847694386377473754997)
              ·
                refine ⟨1668829471348722888164531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17800847694386377473754997 1668829471348722888164531)
                ·
                  refine ⟨2503244207023084332246797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1668829471348722888164531 2503244207023084332246797)
                  ·
                    refine ⟨938716577633656624592549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2503244207023084332246797 938716577633656624592549)
                    ·
                      refine ⟨176009358306310617111103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 938716577633656624592549 176009358306310617111103)
                      ·
                        rfl

theorem cell23_342777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_342777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342777 prefixEnd_342777 := by exact prefixLift 342777
  have htrace : WordTrace (prefixWord ++ tailWord_342777) baseStart_342777 baseEnd_342777 := by
    simpa [prefixWord, tailWord_342777, baseEnd_342777] using wordTrace_append hprefix tailTrace_342777
  have hstable : (prefixWord ++ tailWord_342777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342777).length < 2 ^ (prefixWord ++ tailWord_342777).sum := by decide
  have hdescent : baseEnd_342777 < baseStart_342777 := by decide
  rcases family_descends (prefixWord ++ tailWord_342777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342794 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_342794 : Nat := 118140960795 + 342794 * 2 ^ 59
def prefixEnd_342794 : Nat := 4983230072969 + 3 ^ 40 * 342794 * 2
def baseEnd_342794 : Nat := 176018087477437050598525

theorem tailTrace_342794 : CollatzResearch.WordTrace tailWord_342794 prefixEnd_342794 176018087477437050598525 := by
  unfold tailWord_342794
  simp only [CollatzResearch.WordTrace]
  refine ⟨3125681080030839349834859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8335149546748904932892957 3125681080030839349834859)
  ·
    refine ⟨4688521620046259024752289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3125681080030839349834859 4688521620046259024752289)
    ·
      refine ⟨3516391215034694268564217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4688521620046259024752289 3516391215034694268564217)
      ·
        refine ⟨2637293411276020701423163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3516391215034694268564217 2637293411276020701423163)
        ·
          refine ⟨3955940116914031052134745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2637293411276020701423163 3955940116914031052134745)
          ·
            refine ⟨2966955087685523289101059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3955940116914031052134745 2966955087685523289101059)
            ·
              refine ⟨4450432631528284933651589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2966955087685523289101059 4450432631528284933651589)
              ·
                refine ⟨834456118411553425059673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4450432631528284933651589 834456118411553425059673)
                ·
                  refine ⟨625842088808665068794755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 834456118411553425059673 625842088808665068794755)
                  ·
                    refine ⟨938763133212997603192133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 625842088808665068794755 938763133212997603192133)
                    ·
                      refine ⟨176018087477437050598525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 938763133212997603192133 176018087477437050598525)
                      ·
                        rfl

theorem cell23_342794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_342794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342794 prefixEnd_342794 := by exact prefixLift 342794
  have htrace : WordTrace (prefixWord ++ tailWord_342794) baseStart_342794 baseEnd_342794 := by
    simpa [prefixWord, tailWord_342794, baseEnd_342794] using wordTrace_append hprefix tailTrace_342794
  have hstable : (prefixWord ++ tailWord_342794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342794).length < 2 ^ (prefixWord ++ tailWord_342794).sum := by decide
  have hdescent : baseEnd_342794 < baseStart_342794 := by decide
  rcases family_descends (prefixWord ++ tailWord_342794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
