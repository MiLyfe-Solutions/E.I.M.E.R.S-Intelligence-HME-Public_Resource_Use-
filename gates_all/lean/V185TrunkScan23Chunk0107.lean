import V185TrunkScan23Chunk0106

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_632634 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_632634 : Nat := 118140960795 + 632634 * 2 ^ 59
def prefixEnd_632634 : Nat := 4983230072969 + 3 ^ 40 * 632634 * 2
def baseEnd_632634 : Nat := 324845320376583050265575

theorem tailTrace_632634 : CollatzResearch.WordTrace tailWord_632634 prefixEnd_632634 324845320376583050265575 := by
  unfold tailWord_632634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5768514397520634532596239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15382705060055025420256637 5768514397520634532596239)
  ·
    refine ⟨8652771596280951798894359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5768514397520634532596239 8652771596280951798894359)
    ·
      refine ⟨12979157394421427698341539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8652771596280951798894359 12979157394421427698341539)
      ·
        refine ⟨19468736091632141547512309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12979157394421427698341539 19468736091632141547512309)
        ·
          refine ⟨1825194008590513270079279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19468736091632141547512309 1825194008590513270079279)
          ·
            refine ⟨2737791012885769905118919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825194008590513270079279 2737791012885769905118919)
            ·
              refine ⟨4106686519328654857678379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2737791012885769905118919 4106686519328654857678379)
              ·
                refine ⟨6160029778992982286517569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4106686519328654857678379 6160029778992982286517569)
                ·
                  refine ⟨4620022334244736714888177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6160029778992982286517569 4620022334244736714888177)
                  ·
                    refine ⟨3465016750683552536166133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4620022334244736714888177 3465016750683552536166133)
                    ·
                      refine ⟨324845320376583050265575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3465016750683552536166133 324845320376583050265575)
                      ·
                        rfl

theorem cell23_632634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_632634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632634 prefixEnd_632634 := by exact prefixLift 632634
  have htrace : WordTrace (prefixWord ++ tailWord_632634) baseStart_632634 baseEnd_632634 := by
    simpa [prefixWord, tailWord_632634, baseEnd_632634] using wordTrace_append hprefix tailTrace_632634
  have hstable : (prefixWord ++ tailWord_632634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632634).length < 2 ^ (prefixWord ++ tailWord_632634).sum := by decide
  have hdescent : baseEnd_632634 < baseStart_632634 := by decide
  rcases family_descends (prefixWord ++ tailWord_632634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632638 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_632638 : Nat := 118140960795 + 632638 * 2 ^ 59
def prefixEnd_632638 : Nat := 4983230072969 + 3 ^ 40 * 632638 * 2
def baseEnd_632638 : Nat := 324847374299201034615557

theorem tailTrace_632638 : CollatzResearch.WordTrace tailWord_632638 prefixEnd_632638 324847374299201034615557 := by
  unfold tailWord_632638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2884275435258505851691321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15382802321378697875687045 2884275435258505851691321)
  ·
    refine ⟨2163206576443879388768491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2884275435258505851691321 2163206576443879388768491)
    ·
      refine ⟨3244809864665819083152737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2163206576443879388768491 3244809864665819083152737)
      ·
        refine ⟨2433607398499364312364553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3244809864665819083152737 2433607398499364312364553)
        ·
          refine ⟨1825205548874523234273415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2433607398499364312364553 1825205548874523234273415)
          ·
            refine ⟨2737808323311784851410123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825205548874523234273415 2737808323311784851410123)
            ·
              refine ⟨4106712484967677277115185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2737808323311784851410123 4106712484967677277115185)
              ·
                refine ⟨3080034363725757957836389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4106712484967677277115185 3080034363725757957836389)
                ·
                  refine ⟨577506443198579617094323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3080034363725757957836389 577506443198579617094323)
                  ·
                    refine ⟨866259664797869425641485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 577506443198579617094323 866259664797869425641485)
                    ·
                      refine ⟨324847374299201034615557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 866259664797869425641485 324847374299201034615557)
                      ·
                        rfl

theorem cell23_632638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_632638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632638 prefixEnd_632638 := by exact prefixLift 632638
  have htrace : WordTrace (prefixWord ++ tailWord_632638) baseStart_632638 baseEnd_632638 := by
    simpa [prefixWord, tailWord_632638, baseEnd_632638] using wordTrace_append hprefix tailTrace_632638
  have hstable : (prefixWord ++ tailWord_632638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632638).length < 2 ^ (prefixWord ++ tailWord_632638).sum := by decide
  have hdescent : baseEnd_632638 < baseStart_632638 := by decide
  rcases family_descends (prefixWord ++ tailWord_632638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632639 : List Nat := [1, 1, 2, 2, 7, 1, 1, 3, 1, 2, 2]
def baseStart_632639 : Nat := 118140960795 + 632639 * 2 ^ 59
def prefixEnd_632639 : Nat := 4983230072969 + 3 ^ 40 * 632639 * 2
def baseEnd_632639 : Nat := 324847887779855530703053

theorem tailTrace_632639 : CollatzResearch.WordTrace tailWord_632639 prefixEnd_632639 324847887779855530703053 := by
  unfold tailWord_632639
  simp only [CollatzResearch.WordTrace]
  refine ⟨23074239955064423984316971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15382826636709615989544647 23074239955064423984316971)
  ·
    refine ⟨34611359932596635976475457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23074239955064423984316971 34611359932596635976475457)
    ·
      refine ⟨25958519949447476982356593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34611359932596635976475457 25958519949447476982356593)
      ·
        refine ⟨19468889962085607736767445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25958519949447476982356593 19468889962085607736767445)
        ·
          refine ⟨456302108486381431330487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 19468889962085607736767445 456302108486381431330487)
          ·
            refine ⟨684453162729572146995731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456302108486381431330487 684453162729572146995731)
            ·
              refine ⟨1026679744094358220493597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684453162729572146995731 1026679744094358220493597)
              ·
                refine ⟨385004904035384332685099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1026679744094358220493597 385004904035384332685099)
                ·
                  refine ⟨577507356053076499027649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385004904035384332685099 577507356053076499027649)
                  ·
                    refine ⟨433130517039807374270737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 577507356053076499027649 433130517039807374270737)
                    ·
                      refine ⟨324847887779855530703053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 433130517039807374270737 324847887779855530703053)
                      ·
                        rfl

theorem cell23_632639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 1, 2, 2].length) (baseStart_632639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632639 prefixEnd_632639 := by exact prefixLift 632639
  have htrace : WordTrace (prefixWord ++ tailWord_632639) baseStart_632639 baseEnd_632639 := by
    simpa [prefixWord, tailWord_632639, baseEnd_632639] using wordTrace_append hprefix tailTrace_632639
  have hstable : (prefixWord ++ tailWord_632639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632639).length < 2 ^ (prefixWord ++ tailWord_632639).sum := by decide
  have hdescent : baseEnd_632639 < baseStart_632639 := by decide
  rcases family_descends (prefixWord ++ tailWord_632639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632648 : List Nat := [2, 1, 3, 1, 1, 4, 2, 3, 1, 3, 2]
def baseStart_632648 : Nat := 118140960795 + 632648 * 2 ^ 59
def prefixEnd_632648 : Nat := 4983230072969 + 3 ^ 40 * 632648 * 2
def baseEnd_632648 : Nat := 324852509105745995490511

theorem tailTrace_632648 : CollatzResearch.WordTrace tailWord_632648 prefixEnd_632648 324852509105745995490511 := by
  unfold tailWord_632648
  simp only [CollatzResearch.WordTrace]
  refine ⟨11537284106015909260697299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15383045474687879014263065 11537284106015909260697299)
  ·
    refine ⟨17305926159023863891045949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11537284106015909260697299 17305926159023863891045949)
    ·
      refine ⟨6489722309633948959142231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17305926159023863891045949 6489722309633948959142231)
      ·
        refine ⟨9734583464450923438713347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6489722309633948959142231 9734583464450923438713347)
        ·
          refine ⟨14601875196676385158070021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9734583464450923438713347 14601875196676385158070021)
          ·
            refine ⟨2737851599376822217138129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14601875196676385158070021 2737851599376822217138129)
            ·
              refine ⟨2053388699532616662853597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2737851599376822217138129 2053388699532616662853597)
              ·
                refine ⟨770020762324731248570099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2053388699532616662853597 770020762324731248570099)
                ·
                  refine ⟨1155031143487096872855149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770020762324731248570099 1155031143487096872855149)
                  ·
                    refine ⟨433136678807661327320681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1155031143487096872855149 433136678807661327320681)
                    ·
                      refine ⟨324852509105745995490511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 433136678807661327320681 324852509105745995490511)
                      ·
                        rfl

theorem cell23_632648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_632648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632648 prefixEnd_632648 := by exact prefixLift 632648
  have htrace : WordTrace (prefixWord ++ tailWord_632648) baseStart_632648 baseEnd_632648 := by
    simpa [prefixWord, tailWord_632648, baseEnd_632648] using wordTrace_append hprefix tailTrace_632648
  have hstable : (prefixWord ++ tailWord_632648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632648).length < 2 ^ (prefixWord ++ tailWord_632648).sum := by decide
  have hdescent : baseEnd_632648 < baseStart_632648 := by decide
  rcases family_descends (prefixWord ++ tailWord_632648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632701 : List Nat := [1, 4, 1, 1, 2, 1, 1, 7, 5]
def baseStart_632701 : Nat := 118140960795 + 632701 * 2 ^ 59
def prefixEnd_632701 : Nat := 4983230072969 + 3 ^ 40 * 632701 * 2
def baseEnd_632701 : Nat := 36097747064492698680863

theorem tailTrace_632701 : CollatzResearch.WordTrace tailWord_632701 prefixEnd_632701 36097747064492698680863 := by
  unfold tailWord_632701
  simp only [CollatzResearch.WordTrace]
  refine ⟨23076501280839808573073957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15384334187226539048715971 23076501280839808573073957)
  ·
    refine ⟨4326843990157464107451367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23076501280839808573073957 4326843990157464107451367)
    ·
      refine ⟨6490265985236196161177051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4326843990157464107451367 6490265985236196161177051)
      ·
        refine ⟨9735398977854294241765577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6490265985236196161177051 9735398977854294241765577)
        ·
          refine ⟨7301549233390720681324183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9735398977854294241765577 7301549233390720681324183)
          ·
            refine ⟨10952323850086081021986275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7301549233390720681324183 10952323850086081021986275)
            ·
              refine ⟨16428485775129121532979413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10952323850086081021986275 16428485775129121532979413)
              ·
                refine ⟨385042635354588785929205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16428485775129121532979413 385042635354588785929205)
                ·
                  refine ⟨36097747064492698680863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 385042635354588785929205 36097747064492698680863)
                  ·
                    rfl

theorem cell23_632701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_632701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632701 prefixEnd_632701 := by exact prefixLift 632701
  have htrace : WordTrace (prefixWord ++ tailWord_632701) baseStart_632701 baseEnd_632701 := by
    simpa [prefixWord, tailWord_632701, baseEnd_632701] using wordTrace_append hprefix tailTrace_632701
  have hstable : (prefixWord ++ tailWord_632701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632701).length < 2 ^ (prefixWord ++ tailWord_632701).sum := by decide
  have hdescent : baseEnd_632701 < baseStart_632701 := by decide
  rcases family_descends (prefixWord ++ tailWord_632701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632712 : List Nat := [2, 1, 3, 3, 3, 1, 2, 2, 2, 2, 2]
def baseStart_632712 : Nat := 118140960795 + 632712 * 2 ^ 59
def prefixEnd_632712 : Nat := 4983230072969 + 3 ^ 40 * 632712 * 2
def baseEnd_632712 : Nat := 324885371867633745090217

theorem tailTrace_632712 : CollatzResearch.WordTrace tailWord_632712 prefixEnd_632712 324885371867633745090217 := by
  unfold tailWord_632712
  simp only [CollatzResearch.WordTrace]
  refine ⟨11538451241899978725862195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15384601655866638301149593 11538451241899978725862195)
  ·
    refine ⟨17307676862849968088793293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11538451241899978725862195 17307676862849968088793293)
    ·
      refine ⟨6490378823568738033297485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17307676862849968088793293 6490378823568738033297485)
      ·
        refine ⟨2433892058838276762486557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6490378823568738033297485 2433892058838276762486557)
        ·
          refine ⟨912709522064353785932459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2433892058838276762486557 912709522064353785932459)
          ·
            refine ⟨1369064283096530678898689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912709522064353785932459 1369064283096530678898689)
            ·
              refine ⟨1026798212322398009174017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1369064283096530678898689 1026798212322398009174017)
              ·
                refine ⟨770098659241798506880513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1026798212322398009174017 770098659241798506880513)
                ·
                  refine ⟨577573994431348880160385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 770098659241798506880513 577573994431348880160385)
                  ·
                    refine ⟨433180495823511660120289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 577573994431348880160385 433180495823511660120289)
                    ·
                      refine ⟨324885371867633745090217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 433180495823511660120289 324885371867633745090217)
                      ·
                        rfl

theorem cell23_632712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_632712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632712 prefixEnd_632712 := by exact prefixLift 632712
  have htrace : WordTrace (prefixWord ++ tailWord_632712) baseStart_632712 baseEnd_632712 := by
    simpa [prefixWord, tailWord_632712, baseEnd_632712] using wordTrace_append hprefix tailTrace_632712
  have hstable : (prefixWord ++ tailWord_632712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632712).length < 2 ^ (prefixWord ++ tailWord_632712).sum := by decide
  have hdescent : baseEnd_632712 < baseStart_632712 := by decide
  rcases family_descends (prefixWord ++ tailWord_632712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632721 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 2, 5, 2]
def baseStart_632721 : Nat := 118140960795 + 632721 * 2 ^ 59
def prefixEnd_632721 : Nat := 4983230072969 + 3 ^ 40 * 632721 * 2
def baseEnd_632721 : Nat := 324889993193524209877675

theorem tailTrace_632721 : CollatzResearch.WordTrace tailWord_632721 prefixEnd_632721 324889993193524209877675 := by
  unfold tailWord_632721
  simp only [CollatzResearch.WordTrace]
  refine ⟨23077230740767351988802017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15384820493844901325868011 23077230740767351988802017)
  ·
    refine ⟨17307923055575513991601513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23077230740767351988802017 17307923055575513991601513)
    ·
      refine ⟨12980942291681635493701135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17307923055575513991601513 12980942291681635493701135)
      ·
        refine ⟨19471413437522453240551703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12980942291681635493701135 19471413437522453240551703)
        ·
          refine ⟨29207120156283679860827555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19471413437522453240551703 29207120156283679860827555)
          ·
            refine ⟨43810680234425519791241333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29207120156283679860827555 43810680234425519791241333)
            ·
              refine ⟨4107251271977392480428875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43810680234425519791241333 4107251271977392480428875)
              ·
                refine ⟨6160876907966088720643313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4107251271977392480428875 6160876907966088720643313)
                ·
                  refine ⟨4620657680974566540482485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6160876907966088720643313 4620657680974566540482485)
                  ·
                    refine ⟨433186657591365613170233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4620657680974566540482485 433186657591365613170233)
                    ·
                      refine ⟨324889993193524209877675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 433186657591365613170233 324889993193524209877675)
                      ·
                        rfl

theorem cell23_632721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 5, 2].length) (baseStart_632721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632721 prefixEnd_632721 := by exact prefixLift 632721
  have htrace : WordTrace (prefixWord ++ tailWord_632721) baseStart_632721 baseEnd_632721 := by
    simpa [prefixWord, tailWord_632721, baseEnd_632721] using wordTrace_append hprefix tailTrace_632721
  have hstable : (prefixWord ++ tailWord_632721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632721).length < 2 ^ (prefixWord ++ tailWord_632721).sum := by decide
  have hdescent : baseEnd_632721 < baseStart_632721 := by decide
  rcases family_descends (prefixWord ++ tailWord_632721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632751 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 1, 6, 2]
def baseStart_632751 : Nat := 118140960795 + 632751 * 2 ^ 59
def prefixEnd_632751 : Nat := 4983230072969 + 3 ^ 40 * 632751 * 2
def baseEnd_632751 : Nat := 324905397613159092502537

theorem tailTrace_632751 : CollatzResearch.WordTrace tailWord_632751 prefixEnd_632751 324905397613159092502537 := by
  unfold tailWord_632751
  simp only [CollatzResearch.WordTrace]
  refine ⟨23078324930658667112394107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15385549953772444741596071 23078324930658667112394107)
  ·
    refine ⟨34617487395988000668591161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23078324930658667112394107 34617487395988000668591161)
    ·
      refine ⟨25963115546991000501443371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34617487395988000668591161 25963115546991000501443371)
      ·
        refine ⟨38944673320486500752165057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25963115546991000501443371 38944673320486500752165057)
        ·
          refine ⟨29208504990364875564123793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38944673320486500752165057 29208504990364875564123793)
          ·
            refine ⟨21906378742773656673092845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29208504990364875564123793 21906378742773656673092845)
            ·
              refine ⟨8214892028540121252409817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21906378742773656673092845 8214892028540121252409817)
              ·
                refine ⟨6161169021405090939307363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8214892028540121252409817 6161169021405090939307363)
                ·
                  refine ⟨9241753532107636408961045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6161169021405090939307363 9241753532107636408961045)
                  ·
                    refine ⟨433207196817545456670049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9241753532107636408961045 433207196817545456670049)
                    ·
                      refine ⟨324905397613159092502537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 433207196817545456670049 324905397613159092502537)
                      ·
                        rfl

theorem cell23_632751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 6, 2].length) (baseStart_632751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632751 prefixEnd_632751 := by exact prefixLift 632751
  have htrace : WordTrace (prefixWord ++ tailWord_632751) baseStart_632751 baseEnd_632751 := by
    simpa [prefixWord, tailWord_632751, baseEnd_632751] using wordTrace_append hprefix tailTrace_632751
  have hstable : (prefixWord ++ tailWord_632751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632751).length < 2 ^ (prefixWord ++ tailWord_632751).sum := by decide
  have hdescent : baseEnd_632751 < baseStart_632751 := by decide
  rcases family_descends (prefixWord ++ tailWord_632751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632761 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 5, 4]
def baseStart_632761 : Nat := 118140960795 + 632761 * 2 ^ 59
def prefixEnd_632761 : Nat := 4983230072969 + 3 ^ 40 * 632761 * 2
def baseEnd_632761 : Nat := 108303510806568017792497

theorem tailTrace_632761 : CollatzResearch.WordTrace tailWord_632761 prefixEnd_632761 108303510806568017792497 := by
  unfold tailWord_632761
  simp only [CollatzResearch.WordTrace]
  refine ⟨23078689660622438820258137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15385793107081625880172091 23078689660622438820258137)
  ·
    refine ⟨17309017245466829115193603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23078689660622438820258137 17309017245466829115193603)
    ·
      refine ⟨25963525868200243672790405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17309017245466829115193603 25963525868200243672790405)
      ·
        refine ⟨4868161100287545688648201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25963525868200243672790405 4868161100287545688648201)
        ·
          refine ⟨3651120825215659266486151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4868161100287545688648201 3651120825215659266486151)
          ·
            refine ⟨5476681237823488899729227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3651120825215659266486151 5476681237823488899729227)
            ·
              refine ⟨8215021856735233349593841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5476681237823488899729227 8215021856735233349593841)
              ·
                refine ⟨6161266392551425012195381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8215021856735233349593841 6161266392551425012195381)
                ·
                  refine ⟨577618724301696094893317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6161266392551425012195381 577618724301696094893317)
                  ·
                    refine ⟨108303510806568017792497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 577618724301696094893317 108303510806568017792497)
                    ·
                      rfl

theorem cell23_632761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 4].length) (baseStart_632761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632761 prefixEnd_632761 := by exact prefixLift 632761
  have htrace : WordTrace (prefixWord ++ tailWord_632761) baseStart_632761 baseEnd_632761 := by
    simpa [prefixWord, tailWord_632761, baseEnd_632761] using wordTrace_append hprefix tailTrace_632761
  have hstable : (prefixWord ++ tailWord_632761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632761).length < 2 ^ (prefixWord ++ tailWord_632761).sum := by decide
  have hdescent : baseEnd_632761 < baseStart_632761 := by decide
  rcases family_descends (prefixWord ++ tailWord_632761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632835 : List Nat := [1, 1, 1, 3, 2, 1, 1, 8, 1, 1, 3]
def baseStart_632835 : Nat := 118140960795 + 632835 * 2 ^ 59
def prefixEnd_632835 : Nat := 4983230072969 + 3 ^ 40 * 632835 * 2
def baseEnd_632835 : Nat := 324948529988136763852151

theorem tailTrace_632835 : CollatzResearch.WordTrace tailWord_632835 prefixEnd_632835 324948529988136763852151 := by
  unfold tailWord_632835
  simp only [CollatzResearch.WordTrace]
  refine ⟨23081388662354349458451959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15387592441569566305634639 23081388662354349458451959)
  ·
    refine ⟨34622082993531524187677939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23081388662354349458451959 34622082993531524187677939)
    ·
      refine ⟨51933124490297286281516909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34622082993531524187677939 51933124490297286281516909)
      ·
        refine ⟨19474921683861482355568841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51933124490297286281516909 19474921683861482355568841)
        ·
          refine ⟨14606191262896111766676631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19474921683861482355568841 14606191262896111766676631)
          ·
            refine ⟨21909286894344167650014947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14606191262896111766676631 21909286894344167650014947)
            ·
              refine ⟨32863930341516251475022421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21909286894344167650014947 32863930341516251475022421)
              ·
                refine ⟨385124183689643571972919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 32863930341516251475022421 385124183689643571972919)
                ·
                  refine ⟨577686275534465357959379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385124183689643571972919 577686275534465357959379)
                  ·
                    refine ⟨866529413301698036939069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 577686275534465357959379 866529413301698036939069)
                    ·
                      refine ⟨324948529988136763852151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 866529413301698036939069 324948529988136763852151)
                      ·
                        rfl

theorem cell23_632835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 1, 1, 3].length) (baseStart_632835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632835 prefixEnd_632835 := by exact prefixLift 632835
  have htrace : WordTrace (prefixWord ++ tailWord_632835) baseStart_632835 baseEnd_632835 := by
    simpa [prefixWord, tailWord_632835, baseEnd_632835] using wordTrace_append hprefix tailTrace_632835
  have hstable : (prefixWord ++ tailWord_632835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632835).length < 2 ^ (prefixWord ++ tailWord_632835).sum := by decide
  have hdescent : baseEnd_632835 < baseStart_632835 := by decide
  rcases family_descends (prefixWord ++ tailWord_632835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632842 : List Nat := [3, 1, 2, 2, 5, 1, 2, 1, 6]
def baseStart_632842 : Nat := 118140960795 + 632842 * 2 ^ 59
def prefixEnd_632842 : Nat := 4983230072969 + 3 ^ 40 * 632842 * 2
def baseEnd_632842 : Nat := 36105791594746470718291

theorem tailTrace_632842 : CollatzResearch.WordTrace tailWord_632842 prefixEnd_632842 36105791594746470718291 := by
  unfold tailWord_632842
  simp only [CollatzResearch.WordTrace]
  refine ⟨5770410993332247413489195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15387762648885993102637853 5770410993332247413489195)
  ·
    refine ⟨8655616489998371120233793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5770410993332247413489195 8655616489998371120233793)
    ·
      refine ⟨6491712367498778340175345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8655616489998371120233793 6491712367498778340175345)
      ·
        refine ⟨4868784275624083755131509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6491712367498778340175345 4868784275624083755131509)
        ·
          refine ⟨456448525839757852043579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4868784275624083755131509 456448525839757852043579)
          ·
            refine ⟨684672788759636778065369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456448525839757852043579 684672788759636778065369)
            ·
              refine ⟨513504591569727583549027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684672788759636778065369 513504591569727583549027)
              ·
                refine ⟨770256887354591375323541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513504591569727583549027 770256887354591375323541)
                ·
                  refine ⟨36105791594746470718291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 770256887354591375323541 36105791594746470718291)
                  ·
                    rfl

theorem cell23_632842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 6].length) (baseStart_632842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632842 prefixEnd_632842 := by exact prefixLift 632842
  have htrace : WordTrace (prefixWord ++ tailWord_632842) baseStart_632842 baseEnd_632842 := by
    simpa [prefixWord, tailWord_632842, baseEnd_632842] using wordTrace_append hprefix tailTrace_632842
  have hstable : (prefixWord ++ tailWord_632842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632842).length < 2 ^ (prefixWord ++ tailWord_632842).sum := by decide
  have hdescent : baseEnd_632842 < baseStart_632842 := by decide
  rcases family_descends (prefixWord ++ tailWord_632842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632858 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4]
def baseStart_632858 : Nat := 118140960795 + 632858 * 2 ^ 59
def prefixEnd_632858 : Nat := 4983230072969 + 3 ^ 40 * 632858 * 2
def baseEnd_632858 : Nat := 324960340043190173864545

theorem tailTrace_632858 : CollatzResearch.WordTrace tailWord_632858 prefixEnd_632858 324960340043190173864545 := by
  unfold tailWord_632858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5770556885317756096634807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15388151694180682924359485 5770556885317756096634807)
  ·
    refine ⟨8655835327976634144952211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5770556885317756096634807 8655835327976634144952211)
    ·
      refine ⟨12983752991964951217428317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8655835327976634144952211 12983752991964951217428317)
      ·
        refine ⟨4868907371986856706535619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12983752991964951217428317 4868907371986856706535619)
        ·
          refine ⟨7303361057980285059803429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4868907371986856706535619 7303361057980285059803429)
          ·
            refine ⟨1369380198371303448713143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7303361057980285059803429 1369380198371303448713143)
            ·
              refine ⟨2054070297556955173069715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369380198371303448713143 2054070297556955173069715)
              ·
                refine ⟨3081105446335432759604573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054070297556955173069715 3081105446335432759604573)
                ·
                  refine ⟨1155414542375787284851715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3081105446335432759604573 1155414542375787284851715)
                  ·
                    refine ⟨1733121813563680927277573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1155414542375787284851715 1733121813563680927277573)
                    ·
                      refine ⟨324960340043190173864545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1733121813563680927277573 324960340043190173864545)
                      ·
                        rfl

theorem cell23_632858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_632858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632858 prefixEnd_632858 := by exact prefixLift 632858
  have htrace : WordTrace (prefixWord ++ tailWord_632858) baseStart_632858 baseEnd_632858 := by
    simpa [prefixWord, tailWord_632858, baseEnd_632858] using wordTrace_append hprefix tailTrace_632858
  have hstable : (prefixWord ++ tailWord_632858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632858).length < 2 ^ (prefixWord ++ tailWord_632858).sum := by decide
  have hdescent : baseEnd_632858 < baseStart_632858 := by decide
  rcases family_descends (prefixWord ++ tailWord_632858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632902 : List Nat := [6, 1, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_632902 : Nat := 118140960795 + 632902 * 2 ^ 59
def prefixEnd_632902 : Nat := 4983230072969 + 3 ^ 40 * 632902 * 2
def baseEnd_632902 : Nat := 108327644397329333904781

theorem tailTrace_632902 : CollatzResearch.WordTrace tailWord_632902 prefixEnd_632902 108327644397329333904781 := by
  unfold tailWord_632902
  simp only [CollatzResearch.WordTrace]
  refine ⟨721369761034738121910655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15389221568741079934093973 721369761034738121910655)
  ·
    refine ⟨1082054641552107182865983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 721369761034738121910655 1082054641552107182865983)
    ·
      refine ⟨1623081962328160774298975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1082054641552107182865983 1623081962328160774298975)
      ·
        refine ⟨2434622943492241161448463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1623081962328160774298975 2434622943492241161448463)
        ·
          refine ⟨3651934415238361742172695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2434622943492241161448463 3651934415238361742172695)
          ·
            refine ⟨5477901622857542613259043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3651934415238361742172695 5477901622857542613259043)
            ·
              refine ⟨8216852434286313919888565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5477901622857542613259043 8216852434286313919888565)
              ·
                refine ⟨770329915714341929989553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8216852434286313919888565 770329915714341929989553)
                ·
                  refine ⟨577747436785756447492165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 770329915714341929989553 577747436785756447492165)
                  ·
                    refine ⟨108327644397329333904781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 577747436785756447492165 108327644397329333904781)
                    ·
                      rfl

theorem cell23_632902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_632902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632902 prefixEnd_632902 := by exact prefixLift 632902
  have htrace : WordTrace (prefixWord ++ tailWord_632902) baseStart_632902 baseEnd_632902 := by
    simpa [prefixWord, tailWord_632902, baseEnd_632902] using wordTrace_append hprefix tailTrace_632902
  have hstable : (prefixWord ++ tailWord_632902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632902).length < 2 ^ (prefixWord ++ tailWord_632902).sum := by decide
  have hdescent : baseEnd_632902 < baseStart_632902 := by decide
  rcases family_descends (prefixWord ++ tailWord_632902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632908 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 1, 3, 3]
def baseStart_632908 : Nat := 118140960795 + 632908 * 2 ^ 59
def prefixEnd_632908 : Nat := 4983230072969 + 3 ^ 40 * 632908 * 2
def baseEnd_632908 : Nat := 324986014075914978239315

theorem tailTrace_632908 : CollatzResearch.WordTrace tailWord_632908 prefixEnd_632908 324986014075914978239315 := by
  unfold tailWord_632908
  simp only [CollatzResearch.WordTrace]
  refine ⟨11542025595544941462929689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15389367460726588617239585 11542025595544941462929689)
  ·
    refine ⟨8656519196658706097197267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11542025595544941462929689 8656519196658706097197267)
    ·
      refine ⟨12984778794988059145795901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8656519196658706097197267 12984778794988059145795901)
      ·
        refine ⟨4869292048120522179673463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12984778794988059145795901 4869292048120522179673463)
        ·
          refine ⟨7303938072180783269510195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4869292048120522179673463 7303938072180783269510195)
          ·
            refine ⟨10955907108271174904265293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7303938072180783269510195 10955907108271174904265293)
            ·
              refine ⟨4108465165601690589099485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10955907108271174904265293 4108465165601690589099485)
              ·
                refine ⟨1540674437100633970912307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4108465165601690589099485 1540674437100633970912307)
                ·
                  refine ⟨2311011655650950956368461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1540674437100633970912307 2311011655650950956368461)
                  ·
                    refine ⟨866629370869106608638173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2311011655650950956368461 866629370869106608638173)
                    ·
                      refine ⟨324986014075914978239315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 866629370869106608638173 324986014075914978239315)
                      ·
                        rfl

theorem cell23_632908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_632908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632908 prefixEnd_632908 := by exact prefixLift 632908
  have htrace : WordTrace (prefixWord ++ tailWord_632908) baseStart_632908 baseEnd_632908 := by
    simpa [prefixWord, tailWord_632908, baseEnd_632908] using wordTrace_append hprefix tailTrace_632908
  have hstable : (prefixWord ++ tailWord_632908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632908).length < 2 ^ (prefixWord ++ tailWord_632908).sum := by decide
  have hdescent : baseEnd_632908 < baseStart_632908 := by decide
  rcases family_descends (prefixWord ++ tailWord_632908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_632921 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 2, 2, 5]
def baseStart_632921 : Nat := 118140960795 + 632921 * 2 ^ 59
def prefixEnd_632921 : Nat := 4983230072969 + 3 ^ 40 * 632921 * 2
def baseEnd_632921 : Nat := 324992689324423427376755

theorem tailTrace_632921 : CollatzResearch.WordTrace tailWord_632921 prefixEnd_632921 324992689324423427376755 := by
  unfold tailWord_632921
  simp only [CollatzResearch.WordTrace]
  refine ⟨23084525340042786146082617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15389683560028524097388411 23084525340042786146082617)
  ·
    refine ⟨17313394005032089609561963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23084525340042786146082617 17313394005032089609561963)
    ·
      refine ⟨25970091007548134414342945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17313394005032089609561963 25970091007548134414342945)
      ·
        refine ⟨19477568255661100810757209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25970091007548134414342945 19477568255661100810757209)
        ·
          refine ⟨14608176191745825608067907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19477568255661100810757209 14608176191745825608067907)
          ·
            refine ⟨21912264287618738412101861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14608176191745825608067907 21912264287618738412101861)
            ·
              refine ⟨4108549553928513452269099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21912264287618738412101861 4108549553928513452269099)
              ·
                refine ⟨6162824330892770178403649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4108549553928513452269099 6162824330892770178403649)
                ·
                  refine ⟨4622118248169577633802737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6162824330892770178403649 4622118248169577633802737)
                  ·
                    refine ⟨3466588686127183225352053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4622118248169577633802737 3466588686127183225352053)
                    ·
                      refine ⟨324992689324423427376755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3466588686127183225352053 324992689324423427376755)
                      ·
                        rfl

theorem cell23_632921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_632921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_632921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_632921 prefixEnd_632921 := by exact prefixLift 632921
  have htrace : WordTrace (prefixWord ++ tailWord_632921) baseStart_632921 baseEnd_632921 := by
    simpa [prefixWord, tailWord_632921, baseEnd_632921] using wordTrace_append hprefix tailTrace_632921
  have hstable : (prefixWord ++ tailWord_632921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_632921).length < 2 ^ (prefixWord ++ tailWord_632921).sum := by decide
  have hdescent : baseEnd_632921 < baseStart_632921 := by decide
  rcases family_descends (prefixWord ++ tailWord_632921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633005 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 7]
def baseStart_633005 : Nat := 118140960795 + 633005 * 2 ^ 59
def prefixEnd_633005 : Nat := 4983230072969 + 3 ^ 40 * 633005 * 2
def baseEnd_633005 : Nat := 36115091299933455414041

theorem tailTrace_633005 : CollatzResearch.WordTrace tailWord_633005 prefixEnd_633005 36115091299933455414041 := by
  unfold tailWord_633005
  simp only [CollatzResearch.WordTrace]
  refine ⟨23087589071738468492140469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15391726047825645661426979 23087589071738468492140469)
  ·
    refine ⟨2164461475475481421138169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23087589071738468492140469 2164461475475481421138169)
    ·
      refine ⟨1623346106606611065853627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2164461475475481421138169 1623346106606611065853627)
      ·
        refine ⟨2435019159909916598780441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1623346106606611065853627 2435019159909916598780441)
        ·
          refine ⟨1826264369932437449085331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2435019159909916598780441 1826264369932437449085331)
          ·
            refine ⟨2739396554898656173627997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826264369932437449085331 2739396554898656173627997)
            ·
              refine ⟨1027273708086996065110499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2739396554898656173627997 1027273708086996065110499)
              ·
                refine ⟨1540910562130494097665749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027273708086996065110499 1540910562130494097665749)
                ·
                  refine ⟨36115091299933455414041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1540910562130494097665749 36115091299933455414041)
                  ·
                    rfl

theorem cell23_633005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_633005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633005 prefixEnd_633005 := by exact prefixLift 633005
  have htrace : WordTrace (prefixWord ++ tailWord_633005) baseStart_633005 baseEnd_633005 := by
    simpa [prefixWord, tailWord_633005, baseEnd_633005] using wordTrace_append hprefix tailTrace_633005
  have hstable : (prefixWord ++ tailWord_633005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633005).length < 2 ^ (prefixWord ++ tailWord_633005).sum := by decide
  have hdescent : baseEnd_633005 < baseStart_633005 := by decide
  rcases family_descends (prefixWord ++ tailWord_633005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633055 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 2, 4, 2]
def baseStart_633055 : Nat := 118140960795 + 633055 * 2 ^ 59
def prefixEnd_633055 : Nat := 4983230072969 + 3 ^ 40 * 633055 * 2
def baseEnd_633055 : Nat := 325061495732125903101139

theorem tailTrace_633055 : CollatzResearch.WordTrace tailWord_633055 prefixEnd_633055 325061495732125903101139 := by
  unfold tailWord_633055
  simp only [CollatzResearch.WordTrace]
  refine ⟨23089412721557327031460619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15392941814371551354307079 23089412721557327031460619)
  ·
    refine ⟨34634119082335990547190929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23089412721557327031460619 34634119082335990547190929)
    ·
      refine ⟨25975589311751992910393197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34634119082335990547190929 25975589311751992910393197)
      ·
        refine ⟨9740845991906997341397449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25975589311751992910393197 9740845991906997341397449)
        ·
          refine ⟨7305634493930248006048087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9740845991906997341397449 7305634493930248006048087)
          ·
            refine ⟨10958451740895372009072131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7305634493930248006048087 10958451740895372009072131)
            ·
              refine ⟨16437677611343058013608197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10958451740895372009072131 16437677611343058013608197)
              ·
                refine ⟨3082064552126823377551537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16437677611343058013608197 3082064552126823377551537)
                ·
                  refine ⟨2311548414095117533163653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3082064552126823377551537 2311548414095117533163653)
                  ·
                    refine ⟨433415327642834537468185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2311548414095117533163653 433415327642834537468185)
                    ·
                      refine ⟨325061495732125903101139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 433415327642834537468185 325061495732125903101139)
                      ·
                        rfl

theorem cell23_633055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_633055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633055 prefixEnd_633055 := by exact prefixLift 633055
  have htrace : WordTrace (prefixWord ++ tailWord_633055) baseStart_633055 baseEnd_633055 := by
    simpa [prefixWord, tailWord_633055, baseEnd_633055] using wordTrace_append hprefix tailTrace_633055
  have hstable : (prefixWord ++ tailWord_633055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633055).length < 2 ^ (prefixWord ++ tailWord_633055).sum := by decide
  have hdescent : baseEnd_633055 < baseStart_633055 := by decide
  rcases family_descends (prefixWord ++ tailWord_633055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633092 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_633092 : Nat := 118140960795 + 633092 * 2 ^ 59
def prefixEnd_633092 : Nat := 4983230072969 + 3 ^ 40 * 633092 * 2
def baseEnd_633092 : Nat := 325080494516342258338469

theorem tailTrace_633092 : CollatzResearch.WordTrace tailWord_633092 prefixEnd_633092 325080494516342258338469 := by
  unfold tailWord_633092
  simp only [CollatzResearch.WordTrace]
  refine ⟨11545381111211641175278765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15393841481615521567038353 11545381111211641175278765)
  ·
    refine ⟨4329517916704365440729537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11545381111211641175278765 4329517916704365440729537)
    ·
      refine ⟨3247138437528274080547153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4329517916704365440729537 3247138437528274080547153)
      ·
        refine ⟨2435353828146205560410365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3247138437528274080547153 2435353828146205560410365)
        ·
          refine ⟨913257685554827085153887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2435353828146205560410365 913257685554827085153887)
          ·
            refine ⟨1369886528332240627730831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913257685554827085153887 1369886528332240627730831)
            ·
              refine ⟨2054829792498360941596247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369886528332240627730831 2054829792498360941596247)
              ·
                refine ⟨3082244688747541412394371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2054829792498360941596247 3082244688747541412394371)
                ·
                  refine ⟨4623367033121312118591557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3082244688747541412394371 4623367033121312118591557)
                  ·
                    refine ⟨866881318710246022235917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4623367033121312118591557 866881318710246022235917)
                    ·
                      refine ⟨325080494516342258338469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 866881318710246022235917 325080494516342258338469)
                      ·
                        rfl

theorem cell23_633092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_633092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633092 prefixEnd_633092 := by exact prefixLift 633092
  have htrace : WordTrace (prefixWord ++ tailWord_633092) baseStart_633092 baseEnd_633092 := by
    simpa [prefixWord, tailWord_633092, baseEnd_633092] using wordTrace_append hprefix tailTrace_633092
  have hstable : (prefixWord ++ tailWord_633092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633092).length < 2 ^ (prefixWord ++ tailWord_633092).sum := by decide
  have hdescent : baseEnd_633092 < baseStart_633092 := by decide
  rcases family_descends (prefixWord ++ tailWord_633092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633155 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 4, 4]
def baseStart_633155 : Nat := 118140960795 + 633155 * 2 ^ 59
def prefixEnd_633155 : Nat := 4983230072969 + 3 ^ 40 * 633155 * 2
def baseEnd_633155 : Nat := 108370947932525170616893

theorem tailTrace_633155 : CollatzResearch.WordTrace tailWord_633155 prefixEnd_633155 108370947932525170616893 := by
  unfold tailWord_633155
  simp only [CollatzResearch.WordTrace]
  refine ⟨23093060021195044110100919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15395373347463362740067279 23093060021195044110100919)
  ·
    refine ⟨34639590031792566165151379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23093060021195044110100919 34639590031792566165151379)
    ·
      refine ⟨51959385047688849247727069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34639590031792566165151379 51959385047688849247727069)
      ·
        refine ⟨19484769392883318467897651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51959385047688849247727069 19484769392883318467897651)
        ·
          refine ⟨29227154089324977701846477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19484769392883318467897651 29227154089324977701846477)
          ·
            refine ⟨10960182783496866638192429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29227154089324977701846477 10960182783496866638192429)
            ·
              refine ⟨4110068543811324989322161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10960182783496866638192429 4110068543811324989322161)
              ·
                refine ⟨3082551407858493741991621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4110068543811324989322161 3082551407858493741991621)
                ·
                  refine ⟨577978388973467576623429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3082551407858493741991621 577978388973467576623429)
                  ·
                    refine ⟨108370947932525170616893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 577978388973467576623429 108370947932525170616893)
                    ·
                      rfl

theorem cell23_633155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 4].length) (baseStart_633155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633155 prefixEnd_633155 := by exact prefixLift 633155
  have htrace : WordTrace (prefixWord ++ tailWord_633155) baseStart_633155 baseEnd_633155 := by
    simpa [prefixWord, tailWord_633155, baseEnd_633155] using wordTrace_append hprefix tailTrace_633155
  have hstable : (prefixWord ++ tailWord_633155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633155).length < 2 ^ (prefixWord ++ tailWord_633155).sum := by decide
  have hdescent : baseEnd_633155 < baseStart_633155 := by decide
  rcases family_descends (prefixWord ++ tailWord_633155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633168 : List Nat := [2, 1, 1, 1, 1, 6, 11]
def baseStart_633168 : Nat := 118140960795 + 633168 * 2 ^ 59
def prefixEnd_633168 : Nat := 4983230072969 + 3 ^ 40 * 633168 * 2
def baseEnd_633168 : Nat := 4013821222791160012199

theorem tailTrace_633168 : CollatzResearch.WordTrace tailWord_633168 prefixEnd_633168 4013821222791160012199 := by
  unfold tailWord_633168
  simp only [CollatzResearch.WordTrace]
  refine ⟨11546767085073973665162079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15395689446765298220216105 11546767085073973665162079)
  ·
    refine ⟨17320150627610960497743119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11546767085073973665162079 17320150627610960497743119)
    ·
      refine ⟨25980225941416440746614679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17320150627610960497743119 25980225941416440746614679)
      ·
        refine ⟨38970338912124661119922019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25980225941416440746614679 38970338912124661119922019)
        ·
          refine ⟨58455508368186991679883029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38970338912124661119922019 58455508368186991679883029)
          ·
            refine ⟨2740101954758765234994517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58455508368186991679883029 2740101954758765234994517)
            ·
              refine ⟨4013821222791160012199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2740101954758765234994517 4013821222791160012199)
              ·
                rfl

theorem cell23_633168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 11].length) (baseStart_633168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633168 prefixEnd_633168 := by exact prefixLift 633168
  have htrace : WordTrace (prefixWord ++ tailWord_633168) baseStart_633168 baseEnd_633168 := by
    simpa [prefixWord, tailWord_633168, baseEnd_633168] using wordTrace_append hprefix tailTrace_633168
  have hstable : (prefixWord ++ tailWord_633168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633168).length < 2 ^ (prefixWord ++ tailWord_633168).sum := by decide
  have hdescent : baseEnd_633168 < baseStart_633168 := by decide
  rcases family_descends (prefixWord ++ tailWord_633168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633172 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_633172 : Nat := 118140960795 + 633172 * 2 ^ 59
def prefixEnd_633172 : Nat := 4983230072969 + 3 ^ 40 * 633172 * 2
def baseEnd_633172 : Nat := 108373857656233981779367

theorem tailTrace_633172 : CollatzResearch.WordTrace tailWord_633172 prefixEnd_633172 108373857656233981779367 := by
  unfold tailWord_633172
  simp only [CollatzResearch.WordTrace]
  refine ⟨11546840031066728006734885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15395786708088970675646513 11546840031066728006734885)
  ·
    refine ⟨2165032505825011501262791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11546840031066728006734885 2165032505825011501262791)
    ·
      refine ⟨3247548758737517251894187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2165032505825011501262791 3247548758737517251894187)
      ·
        refine ⟨4871323138106275877841281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3247548758737517251894187 4871323138106275877841281)
        ·
          refine ⟨3653492353579706908380961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4871323138106275877841281 3653492353579706908380961)
          ·
            refine ⟨2740119265184780181285721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3653492353579706908380961 2740119265184780181285721)
            ·
              refine ⟨2055089448888585135964291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2740119265184780181285721 2055089448888585135964291)
              ·
                refine ⟨3082634173332877703946437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055089448888585135964291 3082634173332877703946437)
                ·
                  refine ⟨577993907499914569489957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3082634173332877703946437 577993907499914569489957)
                  ·
                    refine ⟨108373857656233981779367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 577993907499914569489957 108373857656233981779367)
                    ·
                      rfl

theorem cell23_633172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_633172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633172 prefixEnd_633172 := by exact prefixLift 633172
  have htrace : WordTrace (prefixWord ++ tailWord_633172) baseStart_633172 baseEnd_633172 := by
    simpa [prefixWord, tailWord_633172, baseEnd_633172] using wordTrace_append hprefix tailTrace_633172
  have hstable : (prefixWord ++ tailWord_633172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633172).length < 2 ^ (prefixWord ++ tailWord_633172).sum := by decide
  have hdescent : baseEnd_633172 < baseStart_633172 := by decide
  rcases family_descends (prefixWord ++ tailWord_633172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633173 : List Nat := [1, 3, 2, 2, 4, 1, 3, 2, 1, 1, 3]
def baseStart_633173 : Nat := 118140960795 + 633173 * 2 ^ 59
def prefixEnd_633173 : Nat := 4983230072969 + 3 ^ 40 * 633173 * 2
def baseEnd_633173 : Nat := 325122086449356441425597

theorem tailTrace_633173 : CollatzResearch.WordTrace tailWord_633173 prefixEnd_633173 325122086449356441425597 := by
  unfold tailWord_633173
  simp only [CollatzResearch.WordTrace]
  refine ⟨23093716535129833184256173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15395811023419888789504115 23093716535129833184256173)
  ·
    refine ⟨8660143700673687444096065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23093716535129833184256173 8660143700673687444096065)
    ·
      refine ⟨6495107775505265583072049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8660143700673687444096065 6495107775505265583072049)
      ·
        refine ⟨4871330831628949187304037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6495107775505265583072049 4871330831628949187304037)
        ·
          refine ⟨913374530930427972619507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4871330831628949187304037 913374530930427972619507)
          ·
            refine ⟨1370061796395641958929261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913374530930427972619507 1370061796395641958929261)
            ·
              refine ⟨513773173648365734598473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1370061796395641958929261 513773173648365734598473)
              ·
                refine ⟨385329880236274300948855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513773173648365734598473 385329880236274300948855)
                ·
                  refine ⟨577994820354411451423283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385329880236274300948855 577994820354411451423283)
                  ·
                    refine ⟨866992230531617177134925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 577994820354411451423283 866992230531617177134925)
                    ·
                      refine ⟨325122086449356441425597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 866992230531617177134925 325122086449356441425597)
                      ·
                        rfl

theorem cell23_633173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_633173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633173 prefixEnd_633173 := by exact prefixLift 633173
  have htrace : WordTrace (prefixWord ++ tailWord_633173) baseStart_633173 baseEnd_633173 := by
    simpa [prefixWord, tailWord_633173, baseEnd_633173] using wordTrace_append hprefix tailTrace_633173
  have hstable : (prefixWord ++ tailWord_633173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633173).length < 2 ^ (prefixWord ++ tailWord_633173).sum := by decide
  have hdescent : baseEnd_633173 < baseStart_633173 := by decide
  rcases family_descends (prefixWord ++ tailWord_633173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633189 : List Nat := [1, 3, 1, 3, 1, 3, 4, 1, 2, 4]
def baseStart_633189 : Nat := 118140960795 + 633189 * 2 ^ 59
def prefixEnd_633189 : Nat := 4983230072969 + 3 ^ 40 * 633189 * 2
def baseEnd_633189 : Nat := 108376767379942792941841

theorem tailTrace_633189 : CollatzResearch.WordTrace tailWord_633189 prefixEnd_633189 108376767379942792941841 := by
  unfold tailWord_633189
  simp only [CollatzResearch.WordTrace]
  refine ⟨23094300103071867916838621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15396200068714578611225747 23094300103071867916838621)
  ·
    refine ⟨8660362538651950468814483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23094300103071867916838621 8660362538651950468814483)
    ·
      refine ⟨12990543807977925703221725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8660362538651950468814483 12990543807977925703221725)
      ·
        refine ⟨4871453927991722138708147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12990543807977925703221725 4871453927991722138708147)
        ·
          refine ⟨7307180891987583208062221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4871453927991722138708147 7307180891987583208062221)
          ·
            refine ⟨2740192834495343703023333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7307180891987583208062221 2740192834495343703023333)
            ·
              refine ⟨513786156467876944316875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2740192834495343703023333 513786156467876944316875)
              ·
                refine ⟨770679234701815416475313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513786156467876944316875 770679234701815416475313)
                ·
                  refine ⟨578009426026361562356485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 770679234701815416475313 578009426026361562356485)
                  ·
                    refine ⟨108376767379942792941841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 578009426026361562356485 108376767379942792941841)
                    ·
                      rfl

theorem cell23_633189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_633189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633189 prefixEnd_633189 := by exact prefixLift 633189
  have htrace : WordTrace (prefixWord ++ tailWord_633189) baseStart_633189 baseEnd_633189 := by
    simpa [prefixWord, tailWord_633189, baseEnd_633189] using wordTrace_append hprefix tailTrace_633189
  have hstable : (prefixWord ++ tailWord_633189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633189).length < 2 ^ (prefixWord ++ tailWord_633189).sum := by decide
  have hdescent : baseEnd_633189 < baseStart_633189 := by decide
  rcases family_descends (prefixWord ++ tailWord_633189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633196 : List Nat := [2, 2, 1, 1, 7, 1, 1, 2, 1, 1, 4]
def baseStart_633196 : Nat := 118140960795 + 633196 * 2 ^ 59
def prefixEnd_633196 : Nat := 4983230072969 + 3 ^ 40 * 633196 * 2
def baseEnd_633196 : Nat := 325133896504409851437991

theorem tailTrace_633196 : CollatzResearch.WordTrace tailWord_633196 prefixEnd_633196 325133896504409851437991 := by
  unfold tailWord_633196
  simp only [CollatzResearch.WordTrace]
  refine ⟨11547277707023254056171721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15396370276031005408228961 11547277707023254056171721)
  ·
    refine ⟨8660458280267440542128791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11547277707023254056171721 8660458280267440542128791)
    ·
      refine ⟨12990687420401160813193187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8660458280267440542128791 12990687420401160813193187)
      ·
        refine ⟨19486031130601741219789781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12990687420401160813193187 19486031130601741219789781)
        ·
          refine ⟨456703854623478309838823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 19486031130601741219789781 456703854623478309838823)
          ·
            refine ⟨685055781935217464758235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456703854623478309838823 685055781935217464758235)
            ·
              refine ⟨1027583672902826197137353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685055781935217464758235 1027583672902826197137353)
              ·
                refine ⟨770687754677119647853015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1027583672902826197137353 770687754677119647853015)
                ·
                  refine ⟨1156031632015679471779523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770687754677119647853015 1156031632015679471779523)
                  ·
                    refine ⟨1734047448023519207669285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1156031632015679471779523 1734047448023519207669285)
                    ·
                      refine ⟨325133896504409851437991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1734047448023519207669285 325133896504409851437991)
                      ·
                        rfl

theorem cell23_633196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 1, 1, 4].length) (baseStart_633196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633196 prefixEnd_633196 := by exact prefixLift 633196
  have htrace : WordTrace (prefixWord ++ tailWord_633196) baseStart_633196 baseEnd_633196 := by
    simpa [prefixWord, tailWord_633196, baseEnd_633196] using wordTrace_append hprefix tailTrace_633196
  have hstable : (prefixWord ++ tailWord_633196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633196).length < 2 ^ (prefixWord ++ tailWord_633196).sum := by decide
  have hdescent : baseEnd_633196 < baseStart_633196 := by decide
  rcases family_descends (prefixWord ++ tailWord_633196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633212 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 4, 1, 3]
def baseStart_633212 : Nat := 118140960795 + 633212 * 2 ^ 59
def prefixEnd_633212 : Nat := 4983230072969 + 3 ^ 40 * 633212 * 2
def baseEnd_633212 : Nat := 325142112194881788837917

theorem tailTrace_633212 : CollatzResearch.WordTrace tailWord_633212 prefixEnd_633212 325142112194881788837917 := by
  unfold tailWord_633212
  simp only [CollatzResearch.WordTrace]
  refine ⟨11547569490994271422462945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15396759321325695229950593 11547569490994271422462945)
  ·
    refine ⟨8660677118245703566847209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11547569490994271422462945 8660677118245703566847209)
    ·
      refine ⟨6495507838684277675135407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8660677118245703566847209 6495507838684277675135407)
      ·
        refine ⟨9743261758026416512703111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6495507838684277675135407 9743261758026416512703111)
        ·
          refine ⟨14614892637039624769054667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9743261758026416512703111 14614892637039624769054667)
          ·
            refine ⟨21922338955559437153582001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14614892637039624769054667 21922338955559437153582001)
            ·
              refine ⟨16441754216669577865186501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21922338955559437153582001 16441754216669577865186501)
              ·
                refine ⟨3082828915625545849722469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16441754216669577865186501 3082828915625545849722469)
                ·
                  refine ⟨578030421679789846822963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3082828915625545849722469 578030421679789846822963)
                  ·
                    refine ⟨867045632519684770234445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 578030421679789846822963 867045632519684770234445)
                    ·
                      refine ⟨325142112194881788837917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 867045632519684770234445 325142112194881788837917)
                      ·
                        rfl

theorem cell23_633212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_633212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633212 prefixEnd_633212 := by exact prefixLift 633212
  have htrace : WordTrace (prefixWord ++ tailWord_633212) baseStart_633212 baseEnd_633212 := by
    simpa [prefixWord, tailWord_633212, baseEnd_633212] using wordTrace_append hprefix tailTrace_633212
  have hstable : (prefixWord ++ tailWord_633212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633212).length < 2 ^ (prefixWord ++ tailWord_633212).sum := by decide
  have hdescent : baseEnd_633212 < baseStart_633212 := by decide
  rcases family_descends (prefixWord ++ tailWord_633212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633230 : List Nat := [4, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2]
def baseStart_633230 : Nat := 118140960795 + 633230 * 2 ^ 59
def prefixEnd_633230 : Nat := 4983230072969 + 3 ^ 40 * 633230 * 2
def baseEnd_633230 : Nat := 325151354846662718412835

theorem tailTrace_633230 : CollatzResearch.WordTrace tailWord_633230 prefixEnd_633230 325151354846662718412835 := by
  unfold tailWord_633230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2886974436990416489885143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15397196997282221279387429 2886974436990416489885143)
  ·
    refine ⟨4330461655485624734827715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2886974436990416489885143 4330461655485624734827715)
    ·
      refine ⟨6495692483228437102241573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4330461655485624734827715 6495692483228437102241573)
      ·
        refine ⟨1217942340605331956670295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6495692483228437102241573 1217942340605331956670295)
        ·
          refine ⟨1826913510907997935005443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217942340605331956670295 1826913510907997935005443)
          ·
            refine ⟨2740370266361996902508165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826913510907997935005443 2740370266361996902508165)
            ·
              refine ⟨513819424942874419220281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2740370266361996902508165 513819424942874419220281)
              ·
                refine ⟨385364568707155814415211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 513819424942874419220281 385364568707155814415211)
                ·
                  refine ⟨578046853060733721622817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385364568707155814415211 578046853060733721622817)
                  ·
                    refine ⟨433535139795550291217113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 578046853060733721622817 433535139795550291217113)
                    ·
                      refine ⟨325151354846662718412835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 433535139795550291217113 325151354846662718412835)
                      ·
                        rfl

theorem cell23_633230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_633230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633230 prefixEnd_633230 := by exact prefixLift 633230
  have htrace : WordTrace (prefixWord ++ tailWord_633230) baseStart_633230 baseEnd_633230 := by
    simpa [prefixWord, tailWord_633230, baseEnd_633230] using wordTrace_append hprefix tailTrace_633230
  have hstable : (prefixWord ++ tailWord_633230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633230).length < 2 ^ (prefixWord ++ tailWord_633230).sum := by decide
  have hdescent : baseEnd_633230 < baseStart_633230 := by decide
  rcases family_descends (prefixWord ++ tailWord_633230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633246 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_633246 : Nat := 118140960795 + 633246 * 2 ^ 59
def prefixEnd_633246 : Nat := 4983230072969 + 3 ^ 40 * 633246 * 2
def baseEnd_633246 : Nat := 325159570537134655812761

theorem tailTrace_633246 : CollatzResearch.WordTrace tailWord_633246 prefixEnd_633246 325159570537134655812761 := by
  unfold tailWord_633246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2887047382983170831457949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15397586042576911101109061 2887047382983170831457949)
  ·
    refine ⟨1082642768618689061796731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2887047382983170831457949 1082642768618689061796731)
    ·
      refine ⟨1623964152928033592695097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1082642768618689061796731 1623964152928033592695097)
      ·
        refine ⟨1217973114696025194521323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1623964152928033592695097 1217973114696025194521323)
        ·
          refine ⟨1826959672044037791781985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217973114696025194521323 1826959672044037791781985)
          ·
            refine ⟨1370219754033028343836489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1826959672044037791781985 1370219754033028343836489)
            ·
              refine ⟨1027664815524771257877367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1370219754033028343836489 1027664815524771257877367)
              ·
                refine ⟨1541497223287156886816051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027664815524771257877367 1541497223287156886816051)
                ·
                  refine ⟨2312245834930735330224077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1541497223287156886816051 2312245834930735330224077)
                  ·
                    refine ⟨867092188099025748834029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2312245834930735330224077 867092188099025748834029)
                    ·
                      refine ⟨325159570537134655812761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 867092188099025748834029 325159570537134655812761)
                      ·
                        rfl

theorem cell23_633246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_633246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633246 prefixEnd_633246 := by exact prefixLift 633246
  have htrace : WordTrace (prefixWord ++ tailWord_633246) baseStart_633246 baseEnd_633246 := by
    simpa [prefixWord, tailWord_633246, baseEnd_633246] using wordTrace_append hprefix tailTrace_633246
  have hstable : (prefixWord ++ tailWord_633246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633246).length < 2 ^ (prefixWord ++ tailWord_633246).sum := by decide
  have hdescent : baseEnd_633246 < baseStart_633246 := by decide
  rcases family_descends (prefixWord ++ tailWord_633246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633256 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_633256 : Nat := 118140960795 + 633256 * 2 ^ 59
def prefixEnd_633256 : Nat := 4983230072969 + 3 ^ 40 * 633256 * 2
def baseEnd_633256 : Nat := 325164705343679616687715

theorem tailTrace_633256 : CollatzResearch.WordTrace tailWord_633256 prefixEnd_633256 325164705343679616687715 := by
  unfold tailWord_633256
  simp only [CollatzResearch.WordTrace]
  refine ⟨11548371896914569179763811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15397829195886092239685081 11548371896914569179763811)
  ·
    refine ⟨17322557845371853769645717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11548371896914569179763811 17322557845371853769645717)
    ·
      refine ⟨811994899001805645452143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17322557845371853769645717 811994899001805645452143)
      ·
        refine ⟨1217992348502708468178215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811994899001805645452143 1217992348502708468178215)
        ·
          refine ⟨1826988522754062702267323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217992348502708468178215 1826988522754062702267323)
          ·
            refine ⟨2740482784131094053400985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1826988522754062702267323 2740482784131094053400985)
            ·
              refine ⟨2055362088098320540050739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2740482784131094053400985 2055362088098320540050739)
              ·
                refine ⟨3083043132147480810076109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055362088098320540050739 3083043132147480810076109)
                ·
                  refine ⟨1156141174555305303778541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3083043132147480810076109 1156141174555305303778541)
                  ·
                    refine ⟨433552940458239488916953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156141174555305303778541 433552940458239488916953)
                    ·
                      refine ⟨325164705343679616687715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 433552940458239488916953 325164705343679616687715)
                      ·
                        rfl

theorem cell23_633256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_633256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633256 prefixEnd_633256 := by exact prefixLift 633256
  have htrace : WordTrace (prefixWord ++ tailWord_633256) baseStart_633256 baseEnd_633256 := by
    simpa [prefixWord, tailWord_633256, baseEnd_633256] using wordTrace_append hprefix tailTrace_633256
  have hstable : (prefixWord ++ tailWord_633256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633256).length < 2 ^ (prefixWord ++ tailWord_633256).sum := by decide
  have hdescent : baseEnd_633256 < baseStart_633256 := by decide
  rcases family_descends (prefixWord ++ tailWord_633256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633273 : List Nat := [1, 2, 1, 4, 3, 3, 2, 1, 1, 3, 2]
def baseStart_633273 : Nat := 118140960795 + 633273 * 2 ^ 59
def prefixEnd_633273 : Nat := 4983230072969 + 3 ^ 40 * 633273 * 2
def baseEnd_633273 : Nat := 325173434514806050175137

theorem tailTrace_633273 : CollatzResearch.WordTrace tailWord_633273 prefixEnd_633273 325173434514806050175137 := by
  unfold tailWord_633273
  simp only [CollatzResearch.WordTrace]
  refine ⟨23097363834767550262896473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15398242556511700175264315 23097363834767550262896473)
  ·
    refine ⟨17323022876075662697172355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23097363834767550262896473 17323022876075662697172355)
    ·
      refine ⟨25984534314113494045758533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17323022876075662697172355 25984534314113494045758533)
      ·
        refine ⟨4872100183896280133579725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25984534314113494045758533 4872100183896280133579725)
        ·
          refine ⟨1827037568961105050092397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4872100183896280133579725 1827037568961105050092397)
          ·
            refine ⟨685139088360414393784649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1827037568961105050092397 685139088360414393784649)
            ·
              refine ⟨513854316270310795338487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 685139088360414393784649 513854316270310795338487)
              ·
                refine ⟨770781474405466193007731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 513854316270310795338487 770781474405466193007731)
                ·
                  refine ⟨1156172211608199289511597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 770781474405466193007731 1156172211608199289511597)
                  ·
                    refine ⟨433564579353074733566849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156172211608199289511597 433564579353074733566849)
                    ·
                      refine ⟨325173434514806050175137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 433564579353074733566849 325173434514806050175137)
                      ·
                        rfl

theorem cell23_633273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_633273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633273 prefixEnd_633273 := by exact prefixLift 633273
  have htrace : WordTrace (prefixWord ++ tailWord_633273) baseStart_633273 baseEnd_633273 := by
    simpa [prefixWord, tailWord_633273, baseEnd_633273] using wordTrace_append hprefix tailTrace_633273
  have hstable : (prefixWord ++ tailWord_633273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633273).length < 2 ^ (prefixWord ++ tailWord_633273).sum := by decide
  have hdescent : baseEnd_633273 < baseStart_633273 := by decide
  rcases family_descends (prefixWord ++ tailWord_633273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633305 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 3, 7]
def baseStart_633305 : Nat := 118140960795 + 633305 * 2 ^ 59
def prefixEnd_633305 : Nat := 4983230072969 + 3 ^ 40 * 633305 * 2
def baseEnd_633305 : Nat := 108396621965249974991663

theorem tailTrace_633305 : CollatzResearch.WordTrace tailWord_633305 prefixEnd_633305 108396621965249974991663 := by
  unfold tailWord_633305
  simp only [CollatzResearch.WordTrace]
  refine ⟨23098530970651619728061369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15399020647101079818707579 23098530970651619728061369)
  ·
    refine ⟨17323898227988714796046027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23098530970651619728061369 17323898227988714796046027)
    ·
      refine ⟨25985847341983072194069041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17323898227988714796046027 25985847341983072194069041)
      ·
        refine ⟨19489385506487304145551781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25985847341983072194069041 19489385506487304145551781)
        ·
          refine ⟨3654259782466369527290959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19489385506487304145551781 3654259782466369527290959)
          ·
            refine ⟨5481389673699554290936439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3654259782466369527290959 5481389673699554290936439)
            ·
              refine ⟨8222084510549331436404659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5481389673699554290936439 8222084510549331436404659)
              ·
                refine ⟨12333126765823997154606989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8222084510549331436404659 12333126765823997154606989)
                ·
                  refine ⟨4624922537183998932977621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12333126765823997154606989 4624922537183998932977621)
                  ·
                    refine ⟨108396621965249974991663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4624922537183998932977621 108396621965249974991663)
                    ·
                      rfl

theorem cell23_633305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_633305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633305 prefixEnd_633305 := by exact prefixLift 633305
  have htrace : WordTrace (prefixWord ++ tailWord_633305) baseStart_633305 baseEnd_633305 := by
    simpa [prefixWord, tailWord_633305, baseEnd_633305] using wordTrace_append hprefix tailTrace_633305
  have hstable : (prefixWord ++ tailWord_633305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633305).length < 2 ^ (prefixWord ++ tailWord_633305).sum := by decide
  have hdescent : baseEnd_633305 < baseStart_633305 := by decide
  rcases family_descends (prefixWord ++ tailWord_633305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633322 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 1, 7]
def baseStart_633322 : Nat := 118140960795 + 633322 * 2 ^ 59
def prefixEnd_633322 : Nat := 4983230072969 + 3 ^ 40 * 633322 * 2
def baseEnd_633322 : Nat := 108399531688958786154137

theorem tailTrace_633322 : CollatzResearch.WordTrace tailWord_633322 prefixEnd_633322 108399531688958786154137 := by
  unfold tailWord_633322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5774787752897507907857555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15399434007726687754286813 5774787752897507907857555)
  ·
    refine ⟨8662181629346261861786333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5774787752897507907857555 8662181629346261861786333)
    ·
      refine ⟨3248318111004848198169875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8662181629346261861786333 3248318111004848198169875)
      ·
        refine ⟨4872477166507272297254813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3248318111004848198169875 4872477166507272297254813)
        ·
          refine ⟨1827178937440227111470555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4872477166507272297254813 1827178937440227111470555)
          ·
            refine ⟨2740768406160340667205833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1827178937440227111470555 2740768406160340667205833)
            ·
              refine ⟨2055576304620255500404375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2740768406160340667205833 2055576304620255500404375)
              ·
                refine ⟨3083364456930383250606563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2055576304620255500404375 3083364456930383250606563)
                ·
                  refine ⟨4625046685395574875909845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3083364456930383250606563 4625046685395574875909845)
                  ·
                    refine ⟨108399531688958786154137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4625046685395574875909845 108399531688958786154137)
                    ·
                      rfl

theorem cell23_633322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_633322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633322 prefixEnd_633322 := by exact prefixLift 633322
  have htrace : WordTrace (prefixWord ++ tailWord_633322) baseStart_633322 baseEnd_633322 := by
    simpa [prefixWord, tailWord_633322, baseEnd_633322] using wordTrace_append hprefix tailTrace_633322
  have hstable : (prefixWord ++ tailWord_633322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633322).length < 2 ^ (prefixWord ++ tailWord_633322).sum := by decide
  have hdescent : baseEnd_633322 < baseStart_633322 := by decide
  rcases family_descends (prefixWord ++ tailWord_633322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633326 : List Nat := [4, 1, 2, 1, 2, 4, 1, 3, 5]
def baseStart_633326 : Nat := 118140960795 + 633326 * 2 ^ 59
def prefixEnd_633326 : Nat := 4983230072969 + 3 ^ 40 * 633326 * 2
def baseEnd_633326 : Nat := 36133405443277149201377

theorem tailTrace_633326 : CollatzResearch.WordTrace tailWord_633326 prefixEnd_633326 36133405443277149201377 := by
  unfold tailWord_633326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2887412112946942539321979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15399531269050360209717221 2887412112946942539321979)
  ·
    refine ⟨4331118169420413808982969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2887412112946942539321979 4331118169420413808982969)
    ·
      refine ⟨3248338627065310356737227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4331118169420413808982969 3248338627065310356737227)
      ·
        refine ⟨4872507940597965535105841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3248338627065310356737227 4872507940597965535105841)
        ·
          refine ⟨3654380955448474151329381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4872507940597965535105841 3654380955448474151329381)
          ·
            refine ⟨685196429146588903374259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3654380955448474151329381 685196429146588903374259)
            ·
              refine ⟨1027794643719883355061389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685196429146588903374259 1027794643719883355061389)
              ·
                refine ⟨385422991394956258148021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1027794643719883355061389 385422991394956258148021)
                ·
                  refine ⟨36133405443277149201377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 385422991394956258148021 36133405443277149201377)
                  ·
                    rfl

theorem cell23_633326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_633326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633326 prefixEnd_633326 := by exact prefixLift 633326
  have htrace : WordTrace (prefixWord ++ tailWord_633326) baseStart_633326 baseEnd_633326 := by
    simpa [prefixWord, tailWord_633326, baseEnd_633326] using wordTrace_append hprefix tailTrace_633326
  have hstable : (prefixWord ++ tailWord_633326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633326).length < 2 ^ (prefixWord ++ tailWord_633326).sum := by decide
  have hdescent : baseEnd_633326 < baseStart_633326 := by decide
  rcases family_descends (prefixWord ++ tailWord_633326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633376 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 4]
def baseStart_633376 : Nat := 118140960795 + 633376 * 2 ^ 59
def prefixEnd_633376 : Nat := 4983230072969 + 3 ^ 40 * 633376 * 2
def baseEnd_633376 : Nat := 325226323022219147187163

theorem tailTrace_633376 : CollatzResearch.WordTrace tailWord_633376 prefixEnd_633376 325226323022219147187163 := by
  unfold tailWord_633376
  simp only [CollatzResearch.WordTrace]
  refine ⟨11550560276697199426947991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15400747035596265902597321 11550560276697199426947991)
  ·
    refine ⟨17325840415045799140421987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11550560276697199426947991 17325840415045799140421987)
    ·
      refine ⟨25988760622568698710632981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17325840415045799140421987 25988760622568698710632981)
      ·
        refine ⟨1218223154182907752060921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25988760622568698710632981 1218223154182907752060921)
        ·
          refine ⟨913667365637180814045691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1218223154182907752060921 913667365637180814045691)
          ·
            refine ⟨1370501048455771221068537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913667365637180814045691 1370501048455771221068537)
            ·
              refine ⟨1027875786341828415801403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1370501048455771221068537 1027875786341828415801403)
              ·
                refine ⟨1541813679512742623702105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1027875786341828415801403 1541813679512742623702105)
                ·
                  refine ⟨1156360259634556967776579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1541813679512742623702105 1156360259634556967776579)
                  ·
                    refine ⟨1734540389451835451664869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1156360259634556967776579 1734540389451835451664869)
                    ·
                      refine ⟨325226323022219147187163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1734540389451835451664869 325226323022219147187163)
                      ·
                        rfl

theorem cell23_633376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_633376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633376 prefixEnd_633376 := by exact prefixLift 633376
  have htrace : WordTrace (prefixWord ++ tailWord_633376) baseStart_633376 baseEnd_633376 := by
    simpa [prefixWord, tailWord_633376, baseEnd_633376] using wordTrace_append hprefix tailTrace_633376
  have hstable : (prefixWord ++ tailWord_633376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633376).length < 2 ^ (prefixWord ++ tailWord_633376).sum := by decide
  have hdescent : baseEnd_633376 < baseStart_633376 := by decide
  rcases family_descends (prefixWord ++ tailWord_633376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633379 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 3]
def baseStart_633379 : Nat := 118140960795 + 633379 * 2 ^ 59
def prefixEnd_633379 : Nat := 4983230072969 + 3 ^ 40 * 633379 * 2
def baseEnd_633379 : Nat := 325227863464182635449649

theorem tailTrace_633379 : CollatzResearch.WordTrace tailWord_633379 prefixEnd_633379 325227863464182635449649 := by
  unfold tailWord_633379
  simp only [CollatzResearch.WordTrace]
  refine ⟨23101229972383530366255191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15400819981589020244170127 23101229972383530366255191)
  ·
    refine ⟨34651844958575295549382787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23101229972383530366255191 34651844958575295549382787)
    ·
      refine ⟨51977767437862943324074181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34651844958575295549382787 51977767437862943324074181)
      ·
        refine ⟨9745831394599301873263909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51977767437862943324074181 9745831394599301873263909)
        ·
          refine ⟨1827343386487369101236983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9745831394599301873263909 1827343386487369101236983)
          ·
            refine ⟨2741015079731053651855475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1827343386487369101236983 2741015079731053651855475)
            ·
              refine ⟨4111522619596580477783213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2741015079731053651855475 4111522619596580477783213)
              ·
                refine ⟨1541820982348717679168705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4111522619596580477783213 1541820982348717679168705)
                ·
                  refine ⟨1156365736761538259376529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1541820982348717679168705 1156365736761538259376529)
                  ·
                    refine ⟨867274302571153694532397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1156365736761538259376529 867274302571153694532397)
                    ·
                      refine ⟨325227863464182635449649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 867274302571153694532397 325227863464182635449649)
                      ·
                        rfl

theorem cell23_633379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_633379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633379 prefixEnd_633379 := by exact prefixLift 633379
  have htrace : WordTrace (prefixWord ++ tailWord_633379) baseStart_633379 baseEnd_633379 := by
    simpa [prefixWord, tailWord_633379, baseEnd_633379] using wordTrace_append hprefix tailTrace_633379
  have hstable : (prefixWord ++ tailWord_633379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633379).length < 2 ^ (prefixWord ++ tailWord_633379).sum := by decide
  have hdescent : baseEnd_633379 < baseStart_633379 := by decide
  rcases family_descends (prefixWord ++ tailWord_633379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633419 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 4, 3, 2]
def baseStart_633419 : Nat := 118140960795 + 633419 * 2 ^ 59
def prefixEnd_633419 : Nat := 4983230072969 + 3 ^ 40 * 633419 * 2
def baseEnd_633419 : Nat := 325248402690362478949465

theorem tailTrace_633419 : CollatzResearch.WordTrace tailWord_633419 prefixEnd_633419 325248402690362478949465 := by
  unfold tailWord_633419
  simp only [CollatzResearch.WordTrace]
  refine ⟨23102688892238617197711311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15401792594825744798474207 23102688892238617197711311)
  ·
    refine ⟨34654033338357925796566967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23102688892238617197711311 34654033338357925796566967)
    ·
      refine ⟨51981050007536888694850451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34654033338357925796566967 51981050007536888694850451)
      ·
        refine ⟨77971575011305333042275677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51981050007536888694850451 77971575011305333042275677)
        ·
          refine ⟨29239340629239499890853379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77971575011305333042275677 29239340629239499890853379)
          ·
            refine ⟨43859010943859249836280069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29239340629239499890853379 43859010943859249836280069)
            ·
              refine ⟨8223564551973609344302513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43859010943859249836280069 8223564551973609344302513)
              ·
                refine ⟨6167673413980207008226885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8223564551973609344302513 6167673413980207008226885)
                ·
                  refine ⟨1156438765121288814042541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6167673413980207008226885 1156438765121288814042541)
                  ·
                    refine ⟨433664536920483305265953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156438765121288814042541 433664536920483305265953)
                    ·
                      refine ⟨325248402690362478949465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 433664536920483305265953 325248402690362478949465)
                      ·
                        rfl

theorem cell23_633419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 3, 2].length) (baseStart_633419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633419 prefixEnd_633419 := by exact prefixLift 633419
  have htrace : WordTrace (prefixWord ++ tailWord_633419) baseStart_633419 baseEnd_633419 := by
    simpa [prefixWord, tailWord_633419, baseEnd_633419] using wordTrace_append hprefix tailTrace_633419
  have hstable : (prefixWord ++ tailWord_633419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633419).length < 2 ^ (prefixWord ++ tailWord_633419).sum := by decide
  have hdescent : baseEnd_633419 < baseStart_633419 := by decide
  rcases family_descends (prefixWord ++ tailWord_633419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633426 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_633426 : Nat := 118140960795 + 633426 * 2 ^ 59
def prefixEnd_633426 : Nat := 4983230072969 + 3 ^ 40 * 633426 * 2
def baseEnd_633426 : Nat := 325251997054943951561933

theorem tailTrace_633426 : CollatzResearch.WordTrace tailWord_633426 prefixEnd_633426 325251997054943951561933 := by
  unfold tailWord_633426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5775736050803314348304033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15401962802142171595477421 5775736050803314348304033)
  ·
    refine ⟨4331802038102485761228025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5775736050803314348304033 4331802038102485761228025)
    ·
      refine ⟨3248851528576864320921019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4331802038102485761228025 3248851528576864320921019)
      ·
        refine ⟨4873277292865296481381529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3248851528576864320921019 4873277292865296481381529)
        ·
          refine ⟨3654957969648972361036147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4873277292865296481381529 3654957969648972361036147)
          ·
            refine ⟨5482436954473458541554221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3654957969648972361036147 5482436954473458541554221)
            ·
              refine ⟨2055913857927546953082833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5482436954473458541554221 2055913857927546953082833)
              ·
                refine ⟨1541935393445660214812125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2055913857927546953082833 1541935393445660214812125)
                ·
                  refine ⟨578225772542122580554547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1541935393445660214812125 578225772542122580554547)
                  ·
                    refine ⟨867338658813183870831821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 578225772542122580554547 867338658813183870831821)
                    ·
                      refine ⟨325251997054943951561933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 867338658813183870831821 325251997054943951561933)
                      ·
                        rfl

theorem cell23_633426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_633426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633426 prefixEnd_633426 := by exact prefixLift 633426
  have htrace : WordTrace (prefixWord ++ tailWord_633426) baseStart_633426 baseEnd_633426 := by
    simpa [prefixWord, tailWord_633426, baseEnd_633426] using wordTrace_append hprefix tailTrace_633426
  have hstable : (prefixWord ++ tailWord_633426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633426).length < 2 ^ (prefixWord ++ tailWord_633426).sum := by decide
  have hdescent : baseEnd_633426 < baseStart_633426 := by decide
  rcases family_descends (prefixWord ++ tailWord_633426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633443 : List Nat := [1, 1, 1, 5, 1, 2, 4, 3, 1, 1, 3]
def baseStart_633443 : Nat := 118140960795 + 633443 * 2 ^ 59
def prefixEnd_633443 : Nat := 4983230072969 + 3 ^ 40 * 633443 * 2
def baseEnd_633443 : Nat := 325260726226070385049355

theorem tailTrace_633443 : CollatzResearch.WordTrace tailWord_633443 prefixEnd_633443 325260726226070385049355 := by
  unfold tailWord_633443
  simp only [CollatzResearch.WordTrace]
  refine ⟨23103564244151669296584983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15402376162767779531056655 23103564244151669296584983)
  ·
    refine ⟨34655346366227503944877475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23103564244151669296584983 34655346366227503944877475)
    ·
      refine ⟨51983019549341255917316213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34655346366227503944877475 51983019549341255917316213)
      ·
        refine ⟨4873408082750742742248395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51983019549341255917316213 4873408082750742742248395)
        ·
          refine ⟨7310112124126114113372593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4873408082750742742248395 7310112124126114113372593)
          ·
            refine ⟨5482584093094585585029445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7310112124126114113372593 5482584093094585585029445)
            ·
              refine ⟨1027984517455234797193021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5482584093094585585029445 1027984517455234797193021)
              ·
                refine ⟨385494194045713048947383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1027984517455234797193021 385494194045713048947383)
                ·
                  refine ⟨578241291068569573421075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385494194045713048947383 578241291068569573421075)
                  ·
                    refine ⟨867361936602854360131613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 578241291068569573421075 867361936602854360131613)
                    ·
                      refine ⟨325260726226070385049355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 867361936602854360131613 325260726226070385049355)
                      ·
                        rfl

theorem cell23_633443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_633443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633443 prefixEnd_633443 := by exact prefixLift 633443
  have htrace : WordTrace (prefixWord ++ tailWord_633443) baseStart_633443 baseEnd_633443 := by
    simpa [prefixWord, tailWord_633443, baseEnd_633443] using wordTrace_append hprefix tailTrace_633443
  have hstable : (prefixWord ++ tailWord_633443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633443).length < 2 ^ (prefixWord ++ tailWord_633443).sum := by decide
  have hdescent : baseEnd_633443 < baseStart_633443 := by decide
  rcases family_descends (prefixWord ++ tailWord_633443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633459 : List Nat := [1, 1, 1, 2, 2, 1, 1, 8, 2, 4]
def baseStart_633459 : Nat := 118140960795 + 633459 * 2 ^ 59
def prefixEnd_633459 : Nat := 4983230072969 + 3 ^ 40 * 633459 * 2
def baseEnd_633459 : Nat := 108422980638847440816427

theorem tailTrace_633459 : CollatzResearch.WordTrace tailWord_633459 prefixEnd_633459 108422980638847440816427 := by
  unfold tailWord_633459
  simp only [CollatzResearch.WordTrace]
  refine ⟨23104147812093704029167431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15402765208062469352778287 23104147812093704029167431)
  ·
    refine ⟨34656221718140556043751147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23104147812093704029167431 34656221718140556043751147)
    ·
      refine ⟨51984332577210834065626721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34656221718140556043751147 51984332577210834065626721)
      ·
        refine ⟨38988249432908125549220041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51984332577210834065626721 38988249432908125549220041)
        ·
          refine ⟨29241187074681094161915031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38988249432908125549220041 29241187074681094161915031)
          ·
            refine ⟨43861780612021641242872547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29241187074681094161915031 43861780612021641242872547)
            ·
              refine ⟨65792670918032461864308821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43861780612021641242872547 65792670918032461864308821)
              ·
                refine ⟨771007862320692912472369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 65792670918032461864308821 771007862320692912472369)
                ·
                  refine ⟨578255896740519684354277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 771007862320692912472369 578255896740519684354277)
                  ·
                    refine ⟨108422980638847440816427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 578255896740519684354277 108422980638847440816427)
                    ·
                      rfl

theorem cell23_633459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 4].length) (baseStart_633459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633459 prefixEnd_633459 := by exact prefixLift 633459
  have htrace : WordTrace (prefixWord ++ tailWord_633459) baseStart_633459 baseEnd_633459 := by
    simpa [prefixWord, tailWord_633459, baseEnd_633459] using wordTrace_append hprefix tailTrace_633459
  have hstable : (prefixWord ++ tailWord_633459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633459).length < 2 ^ (prefixWord ++ tailWord_633459).sum := by decide
  have hdescent : baseEnd_633459 < baseStart_633459 := by decide
  rcases family_descends (prefixWord ++ tailWord_633459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633476 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_633476 : Nat := 118140960795 + 633476 * 2 ^ 59
def prefixEnd_633476 : Nat := 4983230072969 + 3 ^ 40 * 633476 * 2
def baseEnd_633476 : Nat := 108425890362556251978901

theorem tailTrace_633476 : CollatzResearch.WordTrace tailWord_633476 prefixEnd_633476 108425890362556251978901 := by
  unfold tailWord_633476
  simp only [CollatzResearch.WordTrace]
  refine ⟨11552383926516057966268141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15403178568688077288357521 11552383926516057966268141)
  ·
    refine ⟨4332143972443521737350553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11552383926516057966268141 4332143972443521737350553)
    ·
      refine ⟨3249107979332641303012915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4332143972443521737350553 3249107979332641303012915)
      ·
        refine ⟨4873661968998961954519373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3249107979332641303012915 4873661968998961954519373)
        ·
          refine ⟨1827623238374610732944765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4873661968998961954519373 1827623238374610732944765)
          ·
            refine ⟨685358714390479024854287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1827623238374610732944765 685358714390479024854287)
            ·
              refine ⟨1028038071585718537281431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685358714390479024854287 1028038071585718537281431)
              ·
                refine ⟨1542057107378577805922147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028038071585718537281431 1542057107378577805922147)
                ·
                  refine ⟨2313085661067866708883221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542057107378577805922147 2313085661067866708883221)
                  ·
                    refine ⟨108425890362556251978901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2313085661067866708883221 108425890362556251978901)
                    ·
                      rfl

theorem cell23_633476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_633476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633476 prefixEnd_633476 := by exact prefixLift 633476
  have htrace : WordTrace (prefixWord ++ tailWord_633476) baseStart_633476 baseEnd_633476 := by
    simpa [prefixWord, tailWord_633476, baseEnd_633476] using wordTrace_append hprefix tailTrace_633476
  have hstable : (prefixWord ++ tailWord_633476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633476).length < 2 ^ (prefixWord ++ tailWord_633476).sum := by decide
  have hdescent : baseEnd_633476 < baseStart_633476 := by decide
  rcases family_descends (prefixWord ++ tailWord_633476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633533 : List Nat := [1, 4, 1, 2, 1, 4, 1, 3, 2, 1, 3]
def baseStart_633533 : Nat := 118140960795 + 633533 * 2 ^ 59
def prefixEnd_633533 : Nat := 4983230072969 + 3 ^ 40 * 633533 * 2
def baseEnd_633533 : Nat := 325306939484975032923941

theorem tailTrace_633533 : CollatzResearch.WordTrace tailWord_633533 prefixEnd_633533 325306939484975032923941 := by
  unfold tailWord_633533
  simp only [CollatzResearch.WordTrace]
  refine ⟨23106846813825614667361253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15404564542550409778240835 23106846813825614667361253)
  ·
    refine ⟨4332533777592302750130235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23106846813825614667361253 4332533777592302750130235)
    ·
      refine ⟨6498800666388454125195353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4332533777592302750130235 6498800666388454125195353)
      ·
        refine ⟨4874100499791340593896515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6498800666388454125195353 4874100499791340593896515)
        ·
          refine ⟨7311150749687010890844773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4874100499791340593896515 7311150749687010890844773)
          ·
            refine ⟨1370840765566314542033395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7311150749687010890844773 1370840765566314542033395)
            ·
              refine ⟨2056261148349471813050093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370840765566314542033395 2056261148349471813050093)
              ·
                refine ⟨771097930631051929893785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2056261148349471813050093 771097930631051929893785)
                ·
                  refine ⟨578323447973288947420339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 771097930631051929893785 578323447973288947420339)
                  ·
                    refine ⟨867485171959933421130509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 578323447973288947420339 867485171959933421130509)
                    ·
                      refine ⟨325306939484975032923941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 867485171959933421130509 325306939484975032923941)
                      ·
                        rfl

theorem cell23_633533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_633533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633533 prefixEnd_633533 := by exact prefixLift 633533
  have htrace : WordTrace (prefixWord ++ tailWord_633533) baseStart_633533 baseEnd_633533 := by
    simpa [prefixWord, tailWord_633533, baseEnd_633533] using wordTrace_append hprefix tailTrace_633533
  have hstable : (prefixWord ++ tailWord_633533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633533).length < 2 ^ (prefixWord ++ tailWord_633533).sum := by decide
  have hdescent : baseEnd_633533 < baseStart_633533 := by decide
  rcases family_descends (prefixWord ++ tailWord_633533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633537 : List Nat := [1, 2, 6, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_633537 : Nat := 118140960795 + 633537 * 2 ^ 59
def prefixEnd_633537 : Nat := 4983230072969 + 3 ^ 40 * 633537 * 2
def baseEnd_633537 : Nat := 325308993407593017273923

theorem tailTrace_633537 : CollatzResearch.WordTrace tailWord_633537 prefixEnd_633537 325308993407593017273923 := by
  unfold tailWord_633537
  simp only [CollatzResearch.WordTrace]
  refine ⟨23106992705811123350506865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15404661803874082233671243 23106992705811123350506865)
  ·
    refine ⟨17330244529358342512880149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23106992705811123350506865 17330244529358342512880149)
    ·
      refine ⟨812355212313672305291257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17330244529358342512880149 812355212313672305291257)
      ·
        refine ⟨609266409235254228968443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 812355212313672305291257 609266409235254228968443)
        ·
          refine ⟨913899613852881343452665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609266409235254228968443 913899613852881343452665)
          ·
            refine ⟨685424710389661007589499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 913899613852881343452665 685424710389661007589499)
            ·
              refine ⟨1028137065584491511384249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685424710389661007589499 1028137065584491511384249)
              ·
                refine ⟨771102799188368633538187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1028137065584491511384249 771102799188368633538187)
                ·
                  refine ⟨1156654198782552950307281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771102799188368633538187 1156654198782552950307281)
                  ·
                    refine ⟨867490649086914712730461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1156654198782552950307281 867490649086914712730461)
                    ·
                      refine ⟨325308993407593017273923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 867490649086914712730461 325308993407593017273923)
                      ·
                        rfl

theorem cell23_633537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_633537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633537 prefixEnd_633537 := by exact prefixLift 633537
  have htrace : WordTrace (prefixWord ++ tailWord_633537) baseStart_633537 baseEnd_633537 := by
    simpa [prefixWord, tailWord_633537, baseEnd_633537] using wordTrace_append hprefix tailTrace_633537
  have hstable : (prefixWord ++ tailWord_633537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633537).length < 2 ^ (prefixWord ++ tailWord_633537).sum := by decide
  have hdescent : baseEnd_633537 < baseStart_633537 := by decide
  rcases family_descends (prefixWord ++ tailWord_633537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633552 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 6]
def baseStart_633552 : Nat := 118140960795 + 633552 * 2 ^ 59
def prefixEnd_633552 : Nat := 4983230072969 + 3 ^ 40 * 633552 * 2
def baseEnd_633552 : Nat := 325316695617410458586353

theorem tailTrace_633552 : CollatzResearch.WordTrace tailWord_633552 prefixEnd_633552 325316695617410458586353 := by
  unfold tailWord_633552
  simp only [CollatzResearch.WordTrace]
  refine ⟨11553769900378390456151455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15405026533837853941535273 11553769900378390456151455)
  ·
    refine ⟨17330654850567585684227183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11553769900378390456151455 17330654850567585684227183)
    ·
      refine ⟨25995982275851378526340775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17330654850567585684227183 25995982275851378526340775)
      ·
        refine ⟨38993973413777067789511163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25995982275851378526340775 38993973413777067789511163)
        ·
          refine ⟨58490960120665601684266745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38993973413777067789511163 58490960120665601684266745)
          ·
            refine ⟨43868220090499201263200059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58490960120665601684266745 43868220090499201263200059)
            ·
              refine ⟨65802330135748801894800089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43868220090499201263200059 65802330135748801894800089)
              ·
                refine ⟨49351747601811601421100067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65802330135748801894800089 49351747601811601421100067)
                ·
                  refine ⟨74027621402717402131650101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49351747601811601421100067 74027621402717402131650101)
                  ·
                    refine ⟨6940089506504756449842197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74027621402717402131650101 6940089506504756449842197)
                    ·
                      refine ⟨325316695617410458586353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6940089506504756449842197 325316695617410458586353)
                      ·
                        rfl

theorem cell23_633552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_633552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633552 prefixEnd_633552 := by exact prefixLift 633552
  have htrace : WordTrace (prefixWord ++ tailWord_633552) baseStart_633552 baseEnd_633552 := by
    simpa [prefixWord, tailWord_633552, baseEnd_633552] using wordTrace_append hprefix tailTrace_633552
  have hstable : (prefixWord ++ tailWord_633552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633552).length < 2 ^ (prefixWord ++ tailWord_633552).sum := by decide
  have hdescent : baseEnd_633552 < baseStart_633552 := by decide
  rcases family_descends (prefixWord ++ tailWord_633552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633559 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_633559 : Nat := 118140960795 + 633559 * 2 ^ 59
def prefixEnd_633559 : Nat := 4983230072969 + 3 ^ 40 * 633559 * 2
def baseEnd_633559 : Nat := 325320289981991931198821

theorem tailTrace_633559 : CollatzResearch.WordTrace tailWord_633559 prefixEnd_633559 325320289981991931198821 := by
  unfold tailWord_633559
  simp only [CollatzResearch.WordTrace]
  refine ⟨23107795111731421107807731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15405196741154280738538487 23107795111731421107807731)
  ·
    refine ⟨34661692667597131661711597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23107795111731421107807731 34661692667597131661711597)
    ·
      refine ⟨12998134750348924373141849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34661692667597131661711597 12998134750348924373141849)
      ·
        refine ⟨9748601062761693279856387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12998134750348924373141849 9748601062761693279856387)
        ·
          refine ⟨14622901594142539919784581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9748601062761693279856387 14622901594142539919784581)
          ·
            refine ⟨2741794048901726234959609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14622901594142539919784581 2741794048901726234959609)
            ·
              refine ⟨2056345536676294676219707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2741794048901726234959609 2056345536676294676219707)
              ·
                refine ⟨3084518305014442014329561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2056345536676294676219707 3084518305014442014329561)
                ·
                  refine ⟨2313388728760831510747171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3084518305014442014329561 2313388728760831510747171)
                  ·
                    refine ⟨3470083093141247266120757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2313388728760831510747171 3470083093141247266120757)
                    ·
                      refine ⟨325320289981991931198821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3470083093141247266120757 325320289981991931198821)
                      ·
                        rfl

theorem cell23_633559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_633559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633559 prefixEnd_633559 := by exact prefixLift 633559
  have htrace : WordTrace (prefixWord ++ tailWord_633559) baseStart_633559 baseEnd_633559 := by
    simpa [prefixWord, tailWord_633559, baseEnd_633559] using wordTrace_append hprefix tailTrace_633559
  have hstable : (prefixWord ++ tailWord_633559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633559).length < 2 ^ (prefixWord ++ tailWord_633559).sum := by decide
  have hdescent : baseEnd_633559 < baseStart_633559 := by decide
  rcases family_descends (prefixWord ++ tailWord_633559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633560 : List Nat := [2, 1, 2, 2, 3, 3, 3, 1, 1, 3, 2]
def baseStart_633560 : Nat := 118140960795 + 633560 * 2 ^ 59
def prefixEnd_633560 : Nat := 4983230072969 + 3 ^ 40 * 633560 * 2
def baseEnd_633560 : Nat := 325320803462646427286317

theorem tailTrace_633560 : CollatzResearch.WordTrace tailWord_633560 prefixEnd_633560 325320803462646427286317 := by
  unfold tailWord_633560
  simp only [CollatzResearch.WordTrace]
  refine ⟨11553915792363899139297067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15405221056485198852396089 11553915792363899139297067)
  ·
    refine ⟨17330873688545848708945601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11553915792363899139297067 17330873688545848708945601)
    ·
      refine ⟨12998155266409386531709201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17330873688545848708945601 12998155266409386531709201)
      ·
        refine ⟨9748616449807039898781901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12998155266409386531709201 9748616449807039898781901)
        ·
          refine ⟨3655731168677639962043213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9748616449807039898781901 3655731168677639962043213)
          ·
            refine ⟨1370899188254114985766205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3655731168677639962043213 1370899188254114985766205)
            ·
              refine ⟨514087195595293119662327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1370899188254114985766205 514087195595293119662327)
              ·
                refine ⟨771130793392939679493491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514087195595293119662327 771130793392939679493491)
                ·
                  refine ⟨1156696190089409519240237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771130793392939679493491 1156696190089409519240237)
                  ·
                    refine ⟨433761071283528569715089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156696190089409519240237 433761071283528569715089)
                    ·
                      refine ⟨325320803462646427286317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 433761071283528569715089 325320803462646427286317)
                      ·
                        rfl

theorem cell23_633560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_633560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633560 prefixEnd_633560 := by exact prefixLift 633560
  have htrace : WordTrace (prefixWord ++ tailWord_633560) baseStart_633560 baseEnd_633560 := by
    simpa [prefixWord, tailWord_633560, baseEnd_633560] using wordTrace_append hprefix tailTrace_633560
  have hstable : (prefixWord ++ tailWord_633560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633560).length < 2 ^ (prefixWord ++ tailWord_633560).sum := by decide
  have hdescent : baseEnd_633560 < baseStart_633560 := by decide
  rcases family_descends (prefixWord ++ tailWord_633560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633586 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_633586 : Nat := 118140960795 + 633586 * 2 ^ 59
def prefixEnd_633586 : Nat := 4983230072969 + 3 ^ 40 * 633586 * 2
def baseEnd_633586 : Nat := 325334153959663325561197

theorem tailTrace_633586 : CollatzResearch.WordTrace tailWord_633586 prefixEnd_633586 325334153959663325561197 := by
  unfold tailWord_633586
  simp only [CollatzResearch.WordTrace]
  refine ⟨5777194970658401179760153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15405853255089069812693741 5777194970658401179760153)
  ·
    refine ⟨4332896227993800884820115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5777194970658401179760153 4332896227993800884820115)
    ·
      refine ⟨6499344341990701327230173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4332896227993800884820115 6499344341990701327230173)
      ·
        refine ⟨2437254128246512997711315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6499344341990701327230173 2437254128246512997711315)
        ·
          refine ⟨3655881192369769496566973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2437254128246512997711315 3655881192369769496566973)
          ·
            refine ⟨1370955447138663561212615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3655881192369769496566973 1370955447138663561212615)
            ·
              refine ⟨2056433170707995341818923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370955447138663561212615 2056433170707995341818923)
              ·
                refine ⟨3084649756061993012728385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2056433170707995341818923 3084649756061993012728385)
                ·
                  refine ⟨2313487317046494759546289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3084649756061993012728385 2313487317046494759546289)
                  ·
                    refine ⟨1735115487784871069659717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2313487317046494759546289 1735115487784871069659717)
                    ·
                      refine ⟨325334153959663325561197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1735115487784871069659717 325334153959663325561197)
                      ·
                        rfl

theorem cell23_633586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_633586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633586 prefixEnd_633586 := by exact prefixLift 633586
  have htrace : WordTrace (prefixWord ++ tailWord_633586) baseStart_633586 baseEnd_633586 := by
    simpa [prefixWord, tailWord_633586, baseEnd_633586] using wordTrace_append hprefix tailTrace_633586
  have hstable : (prefixWord ++ tailWord_633586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633586).length < 2 ^ (prefixWord ++ tailWord_633586).sum := by decide
  have hdescent : baseEnd_633586 < baseStart_633586 := by decide
  rcases family_descends (prefixWord ++ tailWord_633586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633590 : List Nat := [5, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_633590 : Nat := 118140960795 + 633590 * 2 ^ 59
def prefixEnd_633590 : Nat := 4983230072969 + 3 ^ 40 * 633590 * 2
def baseEnd_633590 : Nat := 325336207882281309911179

theorem tailTrace_633590 : CollatzResearch.WordTrace tailWord_633590 prefixEnd_633590 325336207882281309911179 := by
  unfold tailWord_633590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1444307860913694587636639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15405950516412742268124149 1444307860913694587636639)
  ·
    refine ⟨2166461791370541881454959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1444307860913694587636639 2166461791370541881454959)
    ·
      refine ⟨3249692687055812822182439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2166461791370541881454959 3249692687055812822182439)
      ·
        refine ⟨4874539030583719233273659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3249692687055812822182439 4874539030583719233273659)
        ·
          refine ⟨7311808545875578849910489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4874539030583719233273659 7311808545875578849910489)
          ·
            refine ⟨5483856409406684137432867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7311808545875578849910489 5483856409406684137432867)
            ·
              refine ⟨8225784614110026206149301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5483856409406684137432867 8225784614110026206149301)
              ·
                refine ⟨771167307572814956826497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8225784614110026206149301 771167307572814956826497)
                ·
                  refine ⟨578375480679611217619873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 771167307572814956826497 578375480679611217619873)
                  ·
                    refine ⟨433781610509708413214905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 578375480679611217619873 433781610509708413214905)
                    ·
                      refine ⟨325336207882281309911179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 433781610509708413214905 325336207882281309911179)
                      ·
                        rfl

theorem cell23_633590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_633590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633590 prefixEnd_633590 := by exact prefixLift 633590
  have htrace : WordTrace (prefixWord ++ tailWord_633590) baseStart_633590 baseEnd_633590 := by
    simpa [prefixWord, tailWord_633590, baseEnd_633590] using wordTrace_append hprefix tailTrace_633590
  have hstable : (prefixWord ++ tailWord_633590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633590).length < 2 ^ (prefixWord ++ tailWord_633590).sum := by decide
  have hdescent : baseEnd_633590 < baseStart_633590 := by decide
  rcases family_descends (prefixWord ++ tailWord_633590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633656 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 3, 4]
def baseStart_633656 : Nat := 118140960795 + 633656 * 2 ^ 59
def prefixEnd_633656 : Nat := 4983230072969 + 3 ^ 40 * 633656 * 2
def baseEnd_633656 : Nat := 108456699201826017228625

theorem tailTrace_633656 : CollatzResearch.WordTrace tailWord_633656 prefixEnd_633656 108456699201826017228625 := by
  unfold tailWord_633656
  simp only [CollatzResearch.WordTrace]
  refine ⟨11555666496190003337044411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15407555328253337782725881 11555666496190003337044411)
  ·
    refine ⟨17333499744285005005566617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11555666496190003337044411 17333499744285005005566617)
    ·
      refine ⟨13000124808213753754174963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17333499744285005005566617 13000124808213753754174963)
      ·
        refine ⟨19500187212320630631262445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13000124808213753754174963 19500187212320630631262445)
        ·
          refine ⟨7312570204620236486723417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19500187212320630631262445 7312570204620236486723417)
          ·
            refine ⟨5484427653465177365042563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7312570204620236486723417 5484427653465177365042563)
            ·
              refine ⟨8226641480197766047563845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5484427653465177365042563 8226641480197766047563845)
              ·
                refine ⟨1542495277537081133918221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8226641480197766047563845 1542495277537081133918221)
                ·
                  refine ⟨578435729076405425219333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1542495277537081133918221 578435729076405425219333)
                  ·
                    refine ⟨108456699201826017228625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 578435729076405425219333 108456699201826017228625)
                    ·
                      rfl

theorem cell23_633656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_633656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633656 prefixEnd_633656 := by exact prefixLift 633656
  have htrace : WordTrace (prefixWord ++ tailWord_633656) baseStart_633656 baseEnd_633656 := by
    simpa [prefixWord, tailWord_633656, baseEnd_633656] using wordTrace_append hprefix tailTrace_633656
  have hstable : (prefixWord ++ tailWord_633656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633656).length < 2 ^ (prefixWord ++ tailWord_633656).sum := by decide
  have hdescent : baseEnd_633656 < baseStart_633656 := by decide
  rcases family_descends (prefixWord ++ tailWord_633656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633703 : List Nat := [1, 1, 5, 1, 2, 2, 4, 1, 6]
def baseStart_633703 : Nat := 118140960795 + 633703 * 2 ^ 59
def prefixEnd_633703 : Nat := 4983230072969 + 3 ^ 40 * 633703 * 2
def baseEnd_633703 : Nat := 36154914577359929755351

theorem tailTrace_633703 : CollatzResearch.WordTrace tailWord_633703 prefixEnd_633703 36154914577359929755351 := by
  unfold tailWord_633703
  simp only [CollatzResearch.WordTrace]
  refine ⟨23113047223209733701049763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15408698148806489134033175 23113047223209733701049763)
  ·
    refine ⟨34669570834814600551574645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23113047223209733701049763 34669570834814600551574645)
    ·
      refine ⟨3250272265763868801710123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34669570834814600551574645 3250272265763868801710123)
      ·
        refine ⟨4875408398645803202565185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3250272265763868801710123 4875408398645803202565185)
        ·
          refine ⟨3656556298984352401923889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4875408398645803202565185 3656556298984352401923889)
          ·
            refine ⟨2742417224238264301442917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3656556298984352401923889 2742417224238264301442917)
            ·
              refine ⟨514203229544674556520547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2742417224238264301442917 514203229544674556520547)
              ·
                refine ⟨771304844317011834780821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514203229544674556520547 771304844317011834780821)
                ·
                  refine ⟨36154914577359929755351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 771304844317011834780821 36154914577359929755351)
                  ·
                    rfl

theorem cell23_633703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 6].length) (baseStart_633703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633703 prefixEnd_633703 := by exact prefixLift 633703
  have htrace : WordTrace (prefixWord ++ tailWord_633703) baseStart_633703 baseEnd_633703 := by
    simpa [prefixWord, tailWord_633703, baseEnd_633703] using wordTrace_append hprefix tailTrace_633703
  have hstable : (prefixWord ++ tailWord_633703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633703).length < 2 ^ (prefixWord ++ tailWord_633703).sum := by decide
  have hdescent : baseEnd_633703 < baseStart_633703 := by decide
  rcases family_descends (prefixWord ++ tailWord_633703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633723 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 2, 3, 2]
def baseStart_633723 : Nat := 118140960795 + 633723 * 2 ^ 59
def prefixEnd_633723 : Nat := 4983230072969 + 3 ^ 40 * 633723 * 2
def baseEnd_633723 : Nat := 325404500809329289548067

theorem tailTrace_633723 : CollatzResearch.WordTrace tailWord_633723 prefixEnd_633723 325404500809329289548067 := by
  unfold tailWord_633723
  simp only [CollatzResearch.WordTrace]
  refine ⟨23113776683137277116777823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15409184455424851411185215 23113776683137277116777823)
  ·
    refine ⟨34670665024705915675166735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23113776683137277116777823 34670665024705915675166735)
    ·
      refine ⟨52005997537058873512750103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34670665024705915675166735 52005997537058873512750103)
      ·
        refine ⟨78008996305588310269125155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52005997537058873512750103 78008996305588310269125155)
        ·
          refine ⟨117013494458382465403687733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78008996305588310269125155 117013494458382465403687733)
          ·
            refine ⟨10970015105473356131595725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117013494458382465403687733 10970015105473356131595725)
            ·
              refine ⟨4113755664552508549348397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10970015105473356131595725 4113755664552508549348397)
              ·
                refine ⟨1542658374207190706005649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4113755664552508549348397 1542658374207190706005649)
                ·
                  refine ⟨1156993780655393029504237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1542658374207190706005649 1156993780655393029504237)
                  ·
                    refine ⟨433872667745772386064089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1156993780655393029504237 433872667745772386064089)
                    ·
                      refine ⟨325404500809329289548067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 433872667745772386064089 325404500809329289548067)
                      ·
                        rfl

theorem cell23_633723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 2, 3, 2].length) (baseStart_633723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633723 prefixEnd_633723 := by exact prefixLift 633723
  have htrace : WordTrace (prefixWord ++ tailWord_633723) baseStart_633723 baseEnd_633723 := by
    simpa [prefixWord, tailWord_633723, baseEnd_633723] using wordTrace_append hprefix tailTrace_633723
  have hstable : (prefixWord ++ tailWord_633723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633723).length < 2 ^ (prefixWord ++ tailWord_633723).sum := by decide
  have hdescent : baseEnd_633723 < baseStart_633723 := by decide
  rcases family_descends (prefixWord ++ tailWord_633723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633763 : List Nat := [1, 1, 1, 4, 1, 2, 4, 3, 2, 4]
def baseStart_633763 : Nat := 118140960795 + 633763 * 2 ^ 59
def prefixEnd_633763 : Nat := 4983230072969 + 3 ^ 40 * 633763 * 2
def baseEnd_633763 : Nat := 108475013345169711015961

theorem tailTrace_633763 : CollatzResearch.WordTrace tailWord_633763 prefixEnd_633763 108475013345169711015961 := by
  unfold tailWord_633763
  simp only [CollatzResearch.WordTrace]
  refine ⟨23115235602992363948233943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15410157068661575965489295 23115235602992363948233943)
  ·
    refine ⟨34672853404488545922350915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23115235602992363948233943 34672853404488545922350915)
    ·
      refine ⟨52009280106732818883526373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34672853404488545922350915 52009280106732818883526373)
      ·
        refine ⟨9751740020012403540661195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52009280106732818883526373 9751740020012403540661195)
        ·
          refine ⟨14627610030018605310991793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9751740020012403540661195 14627610030018605310991793)
          ·
            refine ⟨10970707522513953983243845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14627610030018605310991793 10970707522513953983243845)
            ·
              refine ⟨2057007660471366371858221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10970707522513953983243845 2057007660471366371858221)
              ·
                refine ⟨771377872676762389446833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2057007660471366371858221 771377872676762389446833)
                ·
                  refine ⟨578533404507571792085125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 771377872676762389446833 578533404507571792085125)
                  ·
                    refine ⟨108475013345169711015961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 578533404507571792085125 108475013345169711015961)
                    ·
                      rfl

theorem cell23_633763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2, 4].length) (baseStart_633763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633763 prefixEnd_633763 := by exact prefixLift 633763
  have htrace : WordTrace (prefixWord ++ tailWord_633763) baseStart_633763 baseEnd_633763 := by
    simpa [prefixWord, tailWord_633763, baseEnd_633763] using wordTrace_append hprefix tailTrace_633763
  have hstable : (prefixWord ++ tailWord_633763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633763).length < 2 ^ (prefixWord ++ tailWord_633763).sum := by decide
  have hdescent : baseEnd_633763 < baseStart_633763 := by decide
  rcases family_descends (prefixWord ++ tailWord_633763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633780 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_633780 : Nat := 118140960795 + 633780 * 2 ^ 59
def prefixEnd_633780 : Nat := 4983230072969 + 3 ^ 40 * 633780 * 2
def baseEnd_633780 : Nat := 108477923068878522178435

theorem tailTrace_633780 : CollatzResearch.WordTrace tailWord_633780 prefixEnd_633780 108477923068878522178435 := by
  unfold tailWord_633780
  simp only [CollatzResearch.WordTrace]
  refine ⟨11557927821965387925801397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15410570429287183901068529 11557927821965387925801397)
  ·
    refine ⟨1083555733309255118043881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11557927821965387925801397 1083555733309255118043881)
    ·
      refine ⟨812666799981941338532911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1083555733309255118043881 812666799981941338532911)
      ·
        refine ⟨1219000199972912007799367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 812666799981941338532911 1219000199972912007799367)
        ·
          refine ⟨1828500299959368011699051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219000199972912007799367 1828500299959368011699051)
          ·
            refine ⟨2742750449939052017548577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1828500299959368011699051 2742750449939052017548577)
            ·
              refine ⟨2057062837454289013161433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2742750449939052017548577 2057062837454289013161433)
              ·
                refine ⟨1542797128090716759871075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2057062837454289013161433 1542797128090716759871075)
                ·
                  refine ⟨2314195692136075139806613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1542797128090716759871075 2314195692136075139806613)
                  ·
                    refine ⟨108477923068878522178435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2314195692136075139806613 108477923068878522178435)
                    ·
                      rfl

theorem cell23_633780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_633780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633780 prefixEnd_633780 := by exact prefixLift 633780
  have htrace : WordTrace (prefixWord ++ tailWord_633780) baseStart_633780 baseEnd_633780 := by
    simpa [prefixWord, tailWord_633780, baseEnd_633780] using wordTrace_append hprefix tailTrace_633780
  have hstable : (prefixWord ++ tailWord_633780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633780).length < 2 ^ (prefixWord ++ tailWord_633780).sum := by decide
  have hdescent : baseEnd_633780 < baseStart_633780 := by decide
  rcases family_descends (prefixWord ++ tailWord_633780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633790 : List Nat := [4, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_633790 : Nat := 118140960795 + 633790 * 2 ^ 59
def prefixEnd_633790 : Nat := 4983230072969 + 3 ^ 40 * 633790 * 2
def baseEnd_633790 : Nat := 325438904013180527410259

theorem tailTrace_633790 : CollatzResearch.WordTrace tailWord_633790 prefixEnd_633790 325438904013180527410259 := by
  unfold tailWord_633790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2889527546736818444933353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15410813582596365039644549 2889527546736818444933353)
  ·
    refine ⟨2167145660052613833700015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2889527546736818444933353 2167145660052613833700015)
    ·
      refine ⟨3250718490078920750550023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2167145660052613833700015 3250718490078920750550023)
      ·
        refine ⟨4876077735118381125825035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3250718490078920750550023 4876077735118381125825035)
        ·
          refine ⟨7314116602677571688737553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4876077735118381125825035 7314116602677571688737553)
          ·
            refine ⟨5485587452008178766553165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7314116602677571688737553 5485587452008178766553165)
            ·
              refine ⟨2057095294503067037457437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5485587452008178766553165 2057095294503067037457437)
              ·
                refine ⟨771410735438650139046539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2057095294503067037457437 771410735438650139046539)
                ·
                  refine ⟨1157116103157975208569809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 771410735438650139046539 1157116103157975208569809)
                  ·
                    refine ⟨867837077368481406427357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1157116103157975208569809 867837077368481406427357)
                    ·
                      refine ⟨325438904013180527410259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 867837077368481406427357 325438904013180527410259)
                      ·
                        rfl

theorem cell23_633790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_633790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633790 prefixEnd_633790 := by exact prefixLift 633790
  have htrace : WordTrace (prefixWord ++ tailWord_633790) baseStart_633790 baseEnd_633790 := by
    simpa [prefixWord, tailWord_633790, baseEnd_633790] using wordTrace_append hprefix tailTrace_633790
  have hstable : (prefixWord ++ tailWord_633790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633790).length < 2 ^ (prefixWord ++ tailWord_633790).sum := by decide
  have hdescent : baseEnd_633790 < baseStart_633790 := by decide
  rcases family_descends (prefixWord ++ tailWord_633790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633798 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_633798 : Nat := 118140960795 + 633798 * 2 ^ 59
def prefixEnd_633798 : Nat := 4983230072969 + 3 ^ 40 * 633798 * 2
def baseEnd_633798 : Nat := 325443011858416496110223

theorem tailTrace_633798 : CollatzResearch.WordTrace tailWord_633798 prefixEnd_633798 325443011858416496110223 := by
  unfold tailWord_633798
  simp only [CollatzResearch.WordTrace]
  refine ⟨722391004933298903929939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15411008105243709950505365 722391004933298903929939)
  ·
    refine ⟨1083586507399948355894909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 722391004933298903929939 1083586507399948355894909)
    ·
      refine ⟨406344940274980633460591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1083586507399948355894909 406344940274980633460591)
      ·
        refine ⟨609517410412470950190887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406344940274980633460591 609517410412470950190887)
        ·
          refine ⟨914276115618706425286331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609517410412470950190887 914276115618706425286331)
          ·
            refine ⟨1371414173428059637929497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914276115618706425286331 1371414173428059637929497)
            ·
              refine ⟨1028560630071044728447123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1371414173428059637929497 1028560630071044728447123)
              ·
                refine ⟨1542840945106567092670685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028560630071044728447123 1542840945106567092670685)
                ·
                  refine ⟨578565354414962659751507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1542840945106567092670685 578565354414962659751507)
                  ·
                    refine ⟨867848031622443989627261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 578565354414962659751507 867848031622443989627261)
                    ·
                      refine ⟨325443011858416496110223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 867848031622443989627261 325443011858416496110223)
                      ·
                        rfl

theorem cell23_633798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_633798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633798 prefixEnd_633798 := by exact prefixLift 633798
  have htrace : WordTrace (prefixWord ++ tailWord_633798) baseStart_633798 baseEnd_633798 := by
    simpa [prefixWord, tailWord_633798, baseEnd_633798] using wordTrace_append hprefix tailTrace_633798
  have hstable : (prefixWord ++ tailWord_633798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633798).length < 2 ^ (prefixWord ++ tailWord_633798).sum := by decide
  have hdescent : baseEnd_633798 < baseStart_633798 := by decide
  rcases family_descends (prefixWord ++ tailWord_633798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633814 : List Nat := [5, 2, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_633814 : Nat := 118140960795 + 633814 * 2 ^ 59
def prefixEnd_633814 : Nat := 4983230072969 + 3 ^ 40 * 633814 * 2
def baseEnd_633814 : Nat := 108483742516296144503383

theorem tailTrace_633814 : CollatzResearch.WordTrace tailWord_633814 prefixEnd_633814 108483742516296144503383 := by
  unfold tailWord_633814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1444818482862974978646281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15411397150538399772226997 1444818482862974978646281)
  ·
    refine ⟨1083613862147231233984711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1444818482862974978646281 1083613862147231233984711)
    ·
      refine ⟨1625420793220846850977067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1083613862147231233984711 1625420793220846850977067)
      ·
        refine ⟨2438131189831270276465601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1625420793220846850977067 2438131189831270276465601)
        ·
          refine ⟨1828598392373452707349201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2438131189831270276465601 1828598392373452707349201)
          ·
            refine ⟨1371448794280089530511901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1828598392373452707349201 1371448794280089530511901)
            ·
              refine ⟨514293297855033573941963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1371448794280089530511901 514293297855033573941963)
              ·
                refine ⟨771439946782550360912945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514293297855033573941963 771439946782550360912945)
                ·
                  refine ⟨578579960086912770684709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 771439946782550360912945 578579960086912770684709)
                  ·
                    refine ⟨108483742516296144503383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 578579960086912770684709 108483742516296144503383)
                    ·
                      rfl

theorem cell23_633814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_633814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633814 prefixEnd_633814 := by exact prefixLift 633814
  have htrace : WordTrace (prefixWord ++ tailWord_633814) baseStart_633814 baseEnd_633814 := by
    simpa [prefixWord, tailWord_633814, baseEnd_633814] using wordTrace_append hprefix tailTrace_633814
  have hstable : (prefixWord ++ tailWord_633814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633814).length < 2 ^ (prefixWord ++ tailWord_633814).sum := by decide
  have hdescent : baseEnd_633814 < baseStart_633814 := by decide
  rcases family_descends (prefixWord ++ tailWord_633814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633838 : List Nat := [4, 1, 2, 1, 5, 1, 1, 3, 1, 2, 2]
def baseStart_633838 : Nat := 118140960795 + 633838 * 2 ^ 59
def prefixEnd_633838 : Nat := 4983230072969 + 3 ^ 40 * 633838 * 2
def baseEnd_633838 : Nat := 325463551084596339610039

theorem tailTrace_633838 : CollatzResearch.WordTrace tailWord_633838 prefixEnd_633838 325463551084596339610039 := by
  unfold tailWord_633838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2889746384715081469651771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15411980718480434504809445 2889746384715081469651771)
  ·
    refine ⟨4334619577072622204477657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2889746384715081469651771 4334619577072622204477657)
    ·
      refine ⟨3250964682804466653358243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4334619577072622204477657 3250964682804466653358243)
      ·
        refine ⟨4876447024206699980037365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3250964682804466653358243 4876447024206699980037365)
        ·
          refine ⟨457166908519378123128503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4876447024206699980037365 457166908519378123128503)
          ·
            refine ⟨685750362779067184692755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457166908519378123128503 685750362779067184692755)
            ·
              refine ⟨1028625544168600777039133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685750362779067184692755 1028625544168600777039133)
              ·
                refine ⟨385734579063225291389675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1028625544168600777039133 385734579063225291389675)
                ·
                  refine ⟨578601868594837937084513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385734579063225291389675 578601868594837937084513)
                  ·
                    refine ⟨433951401446128452813385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 578601868594837937084513 433951401446128452813385)
                    ·
                      refine ⟨325463551084596339610039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 433951401446128452813385 325463551084596339610039)
                      ·
                        rfl

theorem cell23_633838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_633838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633838 prefixEnd_633838 := by exact prefixLift 633838
  have htrace : WordTrace (prefixWord ++ tailWord_633838) baseStart_633838 baseEnd_633838 := by
    simpa [prefixWord, tailWord_633838, baseEnd_633838] using wordTrace_append hprefix tailTrace_633838
  have hstable : (prefixWord ++ tailWord_633838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633838).length < 2 ^ (prefixWord ++ tailWord_633838).sum := by decide
  have hdescent : baseEnd_633838 < baseStart_633838 := by decide
  rcases family_descends (prefixWord ++ tailWord_633838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633844 : List Nat := [2, 6, 2, 1, 1, 2, 9]
def baseStart_633844 : Nat := 118140960795 + 633844 * 2 ^ 59
def prefixEnd_633844 : Nat := 4983230072969 + 3 ^ 40 * 633844 * 2
def baseEnd_633844 : Nat := 4018106567512633532531

theorem tailTrace_633844 : CollatzResearch.WordTrace tailWord_633844 prefixEnd_633844 4018106567512633532531 := by
  unfold tailWord_633844
  simp only [CollatzResearch.WordTrace]
  refine ⟨11559094957849457390966293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15412126610465943187955057 11559094957849457390966293)
  ·
    refine ⟨541832576149193315201545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11559094957849457390966293 541832576149193315201545)
    ·
      refine ⟨406374432111894986401159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 541832576149193315201545 406374432111894986401159)
      ·
        refine ⟨609561648167842479601739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406374432111894986401159 609561648167842479601739)
        ·
          refine ⟨914342472251763719402609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609561648167842479601739 914342472251763719402609)
          ·
            refine ⟨685756854188822789551957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 914342472251763719402609 685756854188822789551957)
            ·
              refine ⟨4018106567512633532531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 685756854188822789551957 4018106567512633532531)
              ·
                rfl

theorem cell23_633844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 9].length) (baseStart_633844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633844 prefixEnd_633844 := by exact prefixLift 633844
  have htrace : WordTrace (prefixWord ++ tailWord_633844) baseStart_633844 baseEnd_633844 := by
    simpa [prefixWord, tailWord_633844, baseEnd_633844] using wordTrace_append hprefix tailTrace_633844
  have hstable : (prefixWord ++ tailWord_633844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633844).length < 2 ^ (prefixWord ++ tailWord_633844).sum := by decide
  have hdescent : baseEnd_633844 < baseStart_633844 := by decide
  rcases family_descends (prefixWord ++ tailWord_633844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633863 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_633863 : Nat := 118140960795 + 633863 * 2 ^ 59
def prefixEnd_633863 : Nat := 4983230072969 + 3 ^ 40 * 633863 * 2
def baseEnd_633863 : Nat := 325476388100958741797423

theorem tailTrace_633863 : CollatzResearch.WordTrace tailWord_633863 prefixEnd_633863 325476388100958741797423 := by
  unfold tailWord_633863
  simp only [CollatzResearch.WordTrace]
  refine ⟨23118882902630081026874243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15412588601753387351249495 23118882902630081026874243)
  ·
    refine ⟨34678324353945121540311365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23118882902630081026874243 34678324353945121540311365)
    ·
      refine ⟨6502185816364710288808381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34678324353945121540311365 6502185816364710288808381)
      ·
        refine ⟨2438319681136766358303143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6502185816364710288808381 2438319681136766358303143)
        ·
          refine ⟨3657479521705149537454715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2438319681136766358303143 3657479521705149537454715)
          ·
            refine ⟨5486219282557724306182073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3657479521705149537454715 5486219282557724306182073)
            ·
              refine ⟨4114664461918293229636555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5486219282557724306182073 4114664461918293229636555)
              ·
                refine ⟨6171996692877439844454833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4114664461918293229636555 6171996692877439844454833)
                ·
                  refine ⟨4628997519658079883341125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6171996692877439844454833 4628997519658079883341125)
                  ·
                    refine ⟨867937034935889978126461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4628997519658079883341125 867937034935889978126461)
                    ·
                      refine ⟨325476388100958741797423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 867937034935889978126461 325476388100958741797423)
                      ·
                        rfl

theorem cell23_633863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_633863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633863 prefixEnd_633863 := by exact prefixLift 633863
  have htrace : WordTrace (prefixWord ++ tailWord_633863) baseStart_633863 baseEnd_633863 := by
    simpa [prefixWord, tailWord_633863, baseEnd_633863] using wordTrace_append hprefix tailTrace_633863
  have hstable : (prefixWord ++ tailWord_633863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633863).length < 2 ^ (prefixWord ++ tailWord_633863).sum := by decide
  have hdescent : baseEnd_633863 < baseStart_633863 := by decide
  rcases family_descends (prefixWord ++ tailWord_633863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633917 : List Nat := [1, 4, 1, 3, 1, 2, 4, 2, 5]
def baseStart_633917 : Nat := 118140960795 + 633917 * 2 ^ 59
def prefixEnd_633917 : Nat := 4983230072969 + 3 ^ 40 * 633917 * 2
def baseEnd_633917 : Nat := 36167124006255725613575

theorem tailTrace_633917 : CollatzResearch.WordTrace tailWord_633917 prefixEnd_633917 36167124006255725613575 := by
  unfold tailWord_633917
  simp only [CollatzResearch.WordTrace]
  refine ⟨23120852444434448249340005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15413901629622965499560003 23120852444434448249340005)
  ·
    refine ⟨4335159833331459046751251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23120852444434448249340005 4335159833331459046751251)
    ·
      refine ⟨6502739749997188570126877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4335159833331459046751251 6502739749997188570126877)
      ·
        refine ⟨2438527406248945713797579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6502739749997188570126877 2438527406248945713797579)
        ·
          refine ⟨3657791109373418570696369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2438527406248945713797579 3657791109373418570696369)
          ·
            refine ⟨2743343332030063928022277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3657791109373418570696369 2743343332030063928022277)
            ·
              refine ⟨514376874755636986504177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2743343332030063928022277 514376874755636986504177)
              ·
                refine ⟨385782656066727739878133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514376874755636986504177 385782656066727739878133)
                ·
                  refine ⟨36167124006255725613575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 385782656066727739878133 36167124006255725613575)
                  ·
                    rfl

theorem cell23_633917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_633917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633917 prefixEnd_633917 := by exact prefixLift 633917
  have htrace : WordTrace (prefixWord ++ tailWord_633917) baseStart_633917 baseEnd_633917 := by
    simpa [prefixWord, tailWord_633917, baseEnd_633917] using wordTrace_append hprefix tailTrace_633917
  have hstable : (prefixWord ++ tailWord_633917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633917).length < 2 ^ (prefixWord ++ tailWord_633917).sum := by decide
  have hdescent : baseEnd_633917 < baseStart_633917 := by decide
  rcases family_descends (prefixWord ++ tailWord_633917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633970 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_633970 : Nat := 118140960795 + 633970 * 2 ^ 59
def prefixEnd_633970 : Nat := 4983230072969 + 3 ^ 40 * 633970 * 2
def baseEnd_633970 : Nat := 325531330530989823159431

theorem tailTrace_633970 : CollatzResearch.WordTrace tailWord_633970 prefixEnd_633970 325531330530989823159431 := by
  unfold tailWord_633970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5780696378310609575254841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15415190342161625534012909 5780696378310609575254841)
  ·
    refine ⟨4335522283732957181441131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5780696378310609575254841 4335522283732957181441131)
    ·
      refine ⟨6503283425599435772161697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4335522283732957181441131 6503283425599435772161697)
      ·
        refine ⟨4877462569199576829121273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6503283425599435772161697 4877462569199576829121273)
        ·
          refine ⟨3658096926899682621840955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4877462569199576829121273 3658096926899682621840955)
          ·
            refine ⟨5487145390349523932761433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3658096926899682621840955 5487145390349523932761433)
            ·
              refine ⟨4115359042762142949571075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5487145390349523932761433 4115359042762142949571075)
              ·
                refine ⟨6173038564143214424356613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4115359042762142949571075 6173038564143214424356613)
                ·
                  refine ⟨1157444730776852704566865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6173038564143214424356613 1157444730776852704566865)
                  ·
                    refine ⟨868083548082639528425149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1157444730776852704566865 868083548082639528425149)
                    ·
                      refine ⟨325531330530989823159431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 868083548082639528425149 325531330530989823159431)
                      ·
                        rfl

theorem cell23_633970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_633970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633970 prefixEnd_633970 := by exact prefixLift 633970
  have htrace : WordTrace (prefixWord ++ tailWord_633970) baseStart_633970 baseEnd_633970 := by
    simpa [prefixWord, tailWord_633970, baseEnd_633970] using wordTrace_append hprefix tailTrace_633970
  have hstable : (prefixWord ++ tailWord_633970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633970).length < 2 ^ (prefixWord ++ tailWord_633970).sum := by decide
  have hdescent : baseEnd_633970 < baseStart_633970 := by decide
  rcases family_descends (prefixWord ++ tailWord_633970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_633977 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 3, 4]
def baseStart_633977 : Nat := 118140960795 + 633977 * 2 ^ 59
def prefixEnd_633977 : Nat := 4983230072969 + 3 ^ 40 * 633977 * 2
def baseEnd_633977 : Nat := 108511641631857098590633

theorem tailTrace_633977 : CollatzResearch.WordTrace tailWord_633977 prefixEnd_633977 108511641631857098590633 := by
  unfold tailWord_633977
  simp only [CollatzResearch.WordTrace]
  refine ⟨23123040824217078496524185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15415360549478052331016123 23123040824217078496524185)
  ·
    refine ⟨17342280618162808872393139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23123040824217078496524185 17342280618162808872393139)
    ·
      refine ⟨26013420927244213308589709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17342280618162808872393139 26013420927244213308589709)
      ·
        refine ⟨9755032847716579990721141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26013420927244213308589709 9755032847716579990721141)
        ·
          refine ⟨914534329473429374130107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9755032847716579990721141 914534329473429374130107)
          ·
            refine ⟨1371801494210144061195161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914534329473429374130107 1371801494210144061195161)
            ·
              refine ⟨1028851120657608045896371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1371801494210144061195161 1028851120657608045896371)
              ·
                refine ⟨1543276680986412068844557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028851120657608045896371 1543276680986412068844557)
                ·
                  refine ⟨578728755369904525816709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1543276680986412068844557 578728755369904525816709)
                  ·
                    refine ⟨108511641631857098590633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 578728755369904525816709 108511641631857098590633)
                    ·
                      rfl

theorem cell23_633977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3, 4].length) (baseStart_633977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_633977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_633977 prefixEnd_633977 := by exact prefixLift 633977
  have htrace : WordTrace (prefixWord ++ tailWord_633977) baseStart_633977 baseEnd_633977 := by
    simpa [prefixWord, tailWord_633977, baseEnd_633977] using wordTrace_append hprefix tailTrace_633977
  have hstable : (prefixWord ++ tailWord_633977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_633977).length < 2 ^ (prefixWord ++ tailWord_633977).sum := by decide
  have hdescent : baseEnd_633977 < baseStart_633977 := by decide
  rcases family_descends (prefixWord ++ tailWord_633977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634000 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 5, 1, 3]
def baseStart_634000 : Nat := 118140960795 + 634000 * 2 ^ 59
def prefixEnd_634000 : Nat := 4983230072969 + 3 ^ 40 * 634000 * 2
def baseEnd_634000 : Nat := 325546734950624705784293

theorem tailTrace_634000 : CollatzResearch.WordTrace tailWord_634000 prefixEnd_634000 325546734950624705784293 := by
  unfold tailWord_634000
  simp only [CollatzResearch.WordTrace]
  refine ⟨11561939851566876712305727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15415919802089168949740969 11561939851566876712305727)
  ·
    refine ⟨17342909777350315068458591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11561939851566876712305727 17342909777350315068458591)
    ·
      refine ⟨26014364666025472602687887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17342909777350315068458591 26014364666025472602687887)
      ·
        refine ⟨39021546999038208904031831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26014364666025472602687887 39021546999038208904031831)
        ·
          refine ⟨58532320498557313356047747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39021546999038208904031831 58532320498557313356047747)
          ·
            refine ⟨87798480747835970034071621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58532320498557313356047747 87798480747835970034071621)
            ·
              refine ⟨16462215140219244381388429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87798480747835970034071621 16462215140219244381388429)
              ·
                refine ⟨6173330677582216643020661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16462215140219244381388429 6173330677582216643020661)
                ·
                  refine ⟨578749751023332810283187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6173330677582216643020661 578749751023332810283187)
                  ·
                    refine ⟨868124626534999215424781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 578749751023332810283187 868124626534999215424781)
                    ·
                      refine ⟨325546734950624705784293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 868124626534999215424781 325546734950624705784293)
                      ·
                        rfl

theorem cell23_634000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 5, 1, 3].length) (baseStart_634000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634000 prefixEnd_634000 := by exact prefixLift 634000
  have htrace : WordTrace (prefixWord ++ tailWord_634000) baseStart_634000 baseEnd_634000 := by
    simpa [prefixWord, tailWord_634000, baseEnd_634000] using wordTrace_append hprefix tailTrace_634000
  have hstable : (prefixWord ++ tailWord_634000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634000).length < 2 ^ (prefixWord ++ tailWord_634000).sum := by decide
  have hdescent : baseEnd_634000 < baseStart_634000 := by decide
  rcases family_descends (prefixWord ++ tailWord_634000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634003 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 3, 5]
def baseStart_634003 : Nat := 118140960795 + 634003 * 2 ^ 59
def prefixEnd_634003 : Nat := 4983230072969 + 3 ^ 40 * 634003 * 2
def baseEnd_634003 : Nat := 108516091797529398015593

theorem tailTrace_634003 : CollatzResearch.WordTrace tailWord_634003 prefixEnd_634003 108516091797529398015593 := by
  unfold tailWord_634003
  simp only [CollatzResearch.WordTrace]
  refine ⟨23123989122122884936970663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15415992748081923291313775 23123989122122884936970663)
  ·
    refine ⟨34685983683184327405455995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23123989122122884936970663 34685983683184327405455995)
    ·
      refine ⟨52028975524776491108183993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34685983683184327405455995 52028975524776491108183993)
      ·
        refine ⟨39021731643582368331137995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52028975524776491108183993 39021731643582368331137995)
        ·
          refine ⟨58532597465373552496706993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39021731643582368331137995 58532597465373552496706993)
          ·
            refine ⟨43899448099030164372530245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58532597465373552496706993 43899448099030164372530245)
            ·
              refine ⟨8231146518568155819849421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43899448099030164372530245 8231146518568155819849421)
              ·
                refine ⟨3086679944463058432443533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8231146518568155819849421 3086679944463058432443533)
                ·
                  refine ⟨1157504979173646912166325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3086679944463058432443533 1157504979173646912166325)
                  ·
                    refine ⟨108516091797529398015593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1157504979173646912166325 108516091797529398015593)
                    ·
                      rfl

theorem cell23_634003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 3, 5].length) (baseStart_634003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634003 prefixEnd_634003 := by exact prefixLift 634003
  have htrace : WordTrace (prefixWord ++ tailWord_634003) baseStart_634003 baseEnd_634003 := by
    simpa [prefixWord, tailWord_634003, baseEnd_634003] using wordTrace_append hprefix tailTrace_634003
  have hstable : (prefixWord ++ tailWord_634003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634003).length < 2 ^ (prefixWord ++ tailWord_634003).sum := by decide
  have hdescent : baseEnd_634003 < baseStart_634003 := by decide
  rcases family_descends (prefixWord ++ tailWord_634003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634034 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3]
def baseStart_634034 : Nat := 118140960795 + 634034 * 2 ^ 59
def prefixEnd_634034 : Nat := 4983230072969 + 3 ^ 40 * 634034 * 2
def baseEnd_634034 : Nat := 325564193292877572759137

theorem tailTrace_634034 : CollatzResearch.WordTrace tailWord_634034 prefixEnd_634034 325564193292877572759137 := by
  unfold tailWord_634034
  simp only [CollatzResearch.WordTrace]
  refine ⟨5781279946252644307837289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15416746523340384820899437 5781279946252644307837289)
  ·
    refine ⟨4335959959689483230877967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5781279946252644307837289 4335959959689483230877967)
    ·
      refine ⟨6503939939534224846316951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4335959959689483230877967 6503939939534224846316951)
      ·
        refine ⟨9755909909301337269475427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6503939939534224846316951 9755909909301337269475427)
        ·
          refine ⟨14633864863952005904213141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9755909909301337269475427 14633864863952005904213141)
          ·
            refine ⟨685962415497750276759991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14633864863952005904213141 685962415497750276759991)
            ·
              refine ⟨1028943623246625415139987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685962415497750276759991 1028943623246625415139987)
              ·
                refine ⟨1543415434869938122709981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028943623246625415139987 1543415434869938122709981)
                ·
                  refine ⟨578780788076226796016243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1543415434869938122709981 578780788076226796016243)
                  ·
                    refine ⟨868171182114340194024365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 578780788076226796016243 868171182114340194024365)
                    ·
                      refine ⟨325564193292877572759137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 868171182114340194024365 325564193292877572759137)
                      ·
                        rfl

theorem cell23_634034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_634034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634034 prefixEnd_634034 := by exact prefixLift 634034
  have htrace : WordTrace (prefixWord ++ tailWord_634034) baseStart_634034 baseEnd_634034 := by
    simpa [prefixWord, tailWord_634034, baseEnd_634034] using wordTrace_append hprefix tailTrace_634034
  have hstable : (prefixWord ++ tailWord_634034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634034).length < 2 ^ (prefixWord ++ tailWord_634034).sum := by decide
  have hdescent : baseEnd_634034 < baseStart_634034 := by decide
  rcases family_descends (prefixWord ++ tailWord_634034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634040 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 2, 6, 2]
def baseStart_634040 : Nat := 118140960795 + 634040 * 2 ^ 59
def prefixEnd_634040 : Nat := 4983230072969 + 3 ^ 40 * 634040 * 2
def baseEnd_634040 : Nat := 325567274176804549284109

theorem tailTrace_634040 : CollatzResearch.WordTrace tailWord_634040 prefixEnd_634040 325567274176804549284109 := by
  unfold tailWord_634040
  simp only [CollatzResearch.WordTrace]
  refine ⟨11562669311494420128033787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15416892415325893504045049 11562669311494420128033787)
  ·
    refine ⟨17344003967241630192050681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11562669311494420128033787 17344003967241630192050681)
    ·
      refine ⟨13008002975431222644038011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17344003967241630192050681 13008002975431222644038011)
      ·
        refine ⟨19512004463146833966057017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13008002975431222644038011 19512004463146833966057017)
        ·
          refine ⟨14634003347360125474542763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19512004463146833966057017 14634003347360125474542763)
          ·
            refine ⟨21951005021040188211814145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14634003347360125474542763 21951005021040188211814145)
            ·
              refine ⟨16463253765780141158860609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21951005021040188211814145 16463253765780141158860609)
              ·
                refine ⟨12347440324335105869145457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16463253765780141158860609 12347440324335105869145457)
                ·
                  refine ⟨9260580243251329401859093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12347440324335105869145457 9260580243251329401859093)
                  ·
                    refine ⟨434089698902406065712145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9260580243251329401859093 434089698902406065712145)
                    ·
                      refine ⟨325567274176804549284109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434089698902406065712145 325567274176804549284109)
                      ·
                        rfl

theorem cell23_634040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 6, 2].length) (baseStart_634040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634040 prefixEnd_634040 := by exact prefixLift 634040
  have htrace : WordTrace (prefixWord ++ tailWord_634040) baseStart_634040 baseEnd_634040 := by
    simpa [prefixWord, tailWord_634040, baseEnd_634040] using wordTrace_append hprefix tailTrace_634040
  have hstable : (prefixWord ++ tailWord_634040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634040).length < 2 ^ (prefixWord ++ tailWord_634040).sum := by decide
  have hdescent : baseEnd_634040 < baseStart_634040 := by decide
  rcases family_descends (prefixWord ++ tailWord_634040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634043 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 5]
def baseStart_634043 : Nat := 118140960795 + 634043 * 2 ^ 59
def prefixEnd_634043 : Nat := 4983230072969 + 3 ^ 40 * 634043 * 2
def baseEnd_634043 : Nat := 325568814618768037546595

theorem tailTrace_634043 : CollatzResearch.WordTrace tailWord_634043 prefixEnd_634043 325568814618768037546595 := by
  unfold tailWord_634043
  simp only [CollatzResearch.WordTrace]
  refine ⟨23125448041977971768426783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15416965361318647845617855 23125448041977971768426783)
  ·
    refine ⟨34688172062966957652640175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23125448041977971768426783 34688172062966957652640175)
    ·
      refine ⟨52032258094450436478960263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34688172062966957652640175 52032258094450436478960263)
      ·
        refine ⟨78048387141675654718440395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52032258094450436478960263 78048387141675654718440395)
        ·
          refine ⟨117072580712513482077660593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78048387141675654718440395 117072580712513482077660593)
          ·
            refine ⟨87804435534385111558245445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117072580712513482077660593 87804435534385111558245445)
            ·
              refine ⟨16463331662697208417171021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87804435534385111558245445 16463331662697208417171021)
              ·
                refine ⟨6173749373511453156439133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16463331662697208417171021 6173749373511453156439133)
                ·
                  refine ⟨2315156015066794933664675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6173749373511453156439133 2315156015066794933664675)
                  ·
                    refine ⟨3472734022600192400497013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2315156015066794933664675 3472734022600192400497013)
                    ·
                      refine ⟨325568814618768037546595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3472734022600192400497013 325568814618768037546595)
                      ·
                        rfl

theorem cell23_634043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 5].length) (baseStart_634043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634043 prefixEnd_634043 := by exact prefixLift 634043
  have htrace : WordTrace (prefixWord ++ tailWord_634043) baseStart_634043 baseEnd_634043 := by
    simpa [prefixWord, tailWord_634043, baseEnd_634043] using wordTrace_append hprefix tailTrace_634043
  have hstable : (prefixWord ++ tailWord_634043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634043).length < 2 ^ (prefixWord ++ tailWord_634043).sum := by decide
  have hdescent : baseEnd_634043 < baseStart_634043 := by decide
  rcases family_descends (prefixWord ++ tailWord_634043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634085 : List Nat := [1, 3, 1, 4, 4, 1, 2, 2, 1, 1, 3]
def baseStart_634085 : Nat := 118140960795 + 634085 * 2 ^ 59
def prefixEnd_634085 : Nat := 4983230072969 + 3 ^ 40 * 634085 * 2
def baseEnd_634085 : Nat := 325590380806256873221403

theorem tailTrace_634085 : CollatzResearch.WordTrace tailWord_634085 prefixEnd_634085 325590380806256873221403 := by
  unfold tailWord_634085
  simp only [CollatzResearch.WordTrace]
  refine ⟨23126979907825812941455709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15417986605217208627637139 23126979907825812941455709)
  ·
    refine ⟨8672617465434679853045891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23126979907825812941455709 8672617465434679853045891)
    ·
      refine ⟨13008926198152019779568837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8672617465434679853045891 13008926198152019779568837)
      ·
        refine ⟨2439173662153503708669157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13008926198152019779568837 2439173662153503708669157)
        ·
          refine ⟨457345061653781945375467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2439173662153503708669157 457345061653781945375467)
          ·
            refine ⟨686017592480672918063201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457345061653781945375467 686017592480672918063201)
            ·
              refine ⟨514513194360504688547401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686017592480672918063201 514513194360504688547401)
              ·
                refine ⟨385884895770378516410551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514513194360504688547401 385884895770378516410551)
                ·
                  refine ⟨578827343655567774615827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385884895770378516410551 578827343655567774615827)
                  ·
                    refine ⟨868241015483351661923741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 578827343655567774615827 868241015483351661923741)
                    ·
                      refine ⟨325590380806256873221403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 868241015483351661923741 325590380806256873221403)
                      ·
                        rfl

theorem cell23_634085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_634085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634085 prefixEnd_634085 := by exact prefixLift 634085
  have htrace : WordTrace (prefixWord ++ tailWord_634085) baseStart_634085 baseEnd_634085 := by
    simpa [prefixWord, tailWord_634085, baseEnd_634085] using wordTrace_append hprefix tailTrace_634085
  have hstable : (prefixWord ++ tailWord_634085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634085).length < 2 ^ (prefixWord ++ tailWord_634085).sum := by decide
  have hdescent : baseEnd_634085 < baseStart_634085 := by decide
  rcases family_descends (prefixWord ++ tailWord_634085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634091 : List Nat := [1, 1, 1, 1, 2, 7, 1, 4, 1, 2, 2]
def baseStart_634091 : Nat := 118140960795 + 634091 * 2 ^ 59
def prefixEnd_634091 : Nat := 4983230072969 + 3 ^ 40 * 634091 * 2
def baseEnd_634091 : Nat := 325593461690183849746375

theorem tailTrace_634091 : CollatzResearch.WordTrace tailWord_634091 prefixEnd_634091 325593461690183849746375 := by
  unfold tailWord_634091
  simp only [CollatzResearch.WordTrace]
  refine ⟨23127198745804075966174127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15418132497202717310782751 23127198745804075966174127)
  ·
    refine ⟨34690798118706113949261191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23127198745804075966174127 34690798118706113949261191)
    ·
      refine ⟨52036197178059170923891787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34690798118706113949261191 52036197178059170923891787)
      ·
        refine ⟨78054295767088756385837681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52036197178059170923891787 78054295767088756385837681)
        ·
          refine ⟨58540721825316567289378261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78054295767088756385837681 58540721825316567289378261)
          ·
            refine ⟨1372048167780857045844803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 58540721825316567289378261 1372048167780857045844803)
            ·
              refine ⟨2058072251671285568767205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372048167780857045844803 2058072251671285568767205)
              ·
                refine ⟨385888547188366044143851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2058072251671285568767205 385888547188366044143851)
                ·
                  refine ⟨578832820782549066215777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 385888547188366044143851 578832820782549066215777)
                  ·
                    refine ⟨434124615586911799661833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 578832820782549066215777 434124615586911799661833)
                    ·
                      refine ⟨325593461690183849746375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434124615586911799661833 325593461690183849746375)
                      ·
                        rfl

theorem cell23_634091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 1, 2, 2].length) (baseStart_634091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634091 prefixEnd_634091 := by exact prefixLift 634091
  have htrace : WordTrace (prefixWord ++ tailWord_634091) baseStart_634091 baseEnd_634091 := by
    simpa [prefixWord, tailWord_634091, baseEnd_634091] using wordTrace_append hprefix tailTrace_634091
  have hstable : (prefixWord ++ tailWord_634091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634091).length < 2 ^ (prefixWord ++ tailWord_634091).sum := by decide
  have hdescent : baseEnd_634091 < baseStart_634091 := by decide
  rcases family_descends (prefixWord ++ tailWord_634091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634114 : List Nat := [3, 4, 1, 1, 3, 1, 3, 7]
def baseStart_634114 : Nat := 118140960795 + 634114 * 2 ^ 59
def prefixEnd_634114 : Nat := 4983230072969 + 3 ^ 40 * 634114 * 2
def baseEnd_634114 : Nat := 12059454509082861472547

theorem tailTrace_634114 : CollatzResearch.WordTrace tailWord_634114 prefixEnd_634114 12059454509082861472547 := by
  unfold tailWord_634114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5782009406180187723565349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15418691749813833929507597 5782009406180187723565349)
  ·
    refine ⟨1084126763658785198168503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5782009406180187723565349 1084126763658785198168503)
    ·
      refine ⟨1626190145488177797252755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1084126763658785198168503 1626190145488177797252755)
      ·
        refine ⟨2439285218232266695879133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1626190145488177797252755 2439285218232266695879133)
        ·
          refine ⟨914731956837100010954675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2439285218232266695879133 914731956837100010954675)
          ·
            refine ⟨1372097935255650016432013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 914731956837100010954675 1372097935255650016432013)
            ·
              refine ⟨514536725720868756162005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1372097935255650016432013 514536725720868756162005)
              ·
                refine ⟨12059454509082861472547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 514536725720868756162005 12059454509082861472547)
                ·
                  rfl

theorem cell23_634114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 7].length) (baseStart_634114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634114 prefixEnd_634114 := by exact prefixLift 634114
  have htrace : WordTrace (prefixWord ++ tailWord_634114) baseStart_634114 baseEnd_634114 := by
    simpa [prefixWord, tailWord_634114, baseEnd_634114] using wordTrace_append hprefix tailTrace_634114
  have hstable : (prefixWord ++ tailWord_634114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634114).length < 2 ^ (prefixWord ++ tailWord_634114).sum := by decide
  have hdescent : baseEnd_634114 < baseStart_634114 := by decide
  rcases family_descends (prefixWord ++ tailWord_634114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634117 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 3, 3, 2]
def baseStart_634117 : Nat := 118140960795 + 634117 * 2 ^ 59
def prefixEnd_634117 : Nat := 4983230072969 + 3 ^ 40 * 634117 * 2
def baseEnd_634117 : Nat := 325606812187200748021255

theorem tailTrace_634117 : CollatzResearch.WordTrace tailWord_634117 prefixEnd_634117 325606812187200748021255 := by
  unfold tailWord_634117
  simp only [CollatzResearch.WordTrace]
  refine ⟨23128147043709882406620605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15418764695806588271080403 23128147043709882406620605)
  ·
    refine ⟨8673055141391205902482727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23128147043709882406620605 8673055141391205902482727)
    ·
      refine ⟨13009582712086808853724091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8673055141391205902482727 13009582712086808853724091)
      ·
        refine ⟨19514374068130213280586137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13009582712086808853724091 19514374068130213280586137)
        ·
          refine ⟨14635780551097659960439603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19514374068130213280586137 14635780551097659960439603)
          ·
            refine ⟨21953670826646489940659405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14635780551097659960439603 21953670826646489940659405)
            ·
              refine ⟨8232626559992433727747277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21953670826646489940659405 8232626559992433727747277)
              ·
                refine ⟨3087234959997162647905229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8232626559992433727747277 3087234959997162647905229)
                ·
                  refine ⟨1157713109998935992964461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3087234959997162647905229 1157713109998935992964461)
                  ·
                    refine ⟨434142416249600997361673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1157713109998935992964461 434142416249600997361673)
                    ·
                      refine ⟨325606812187200748021255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434142416249600997361673 325606812187200748021255)
                      ·
                        rfl

theorem cell23_634117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 3, 2].length) (baseStart_634117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634117 prefixEnd_634117 := by exact prefixLift 634117
  have htrace : WordTrace (prefixWord ++ tailWord_634117) baseStart_634117 baseEnd_634117 := by
    simpa [prefixWord, tailWord_634117, baseEnd_634117] using wordTrace_append hprefix tailTrace_634117
  have hstable : (prefixWord ++ tailWord_634117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634117).length < 2 ^ (prefixWord ++ tailWord_634117).sum := by decide
  have hdescent : baseEnd_634117 < baseStart_634117 := by decide
  rcases family_descends (prefixWord ++ tailWord_634117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634140 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 2, 6]
def baseStart_634140 : Nat := 118140960795 + 634140 * 2 ^ 59
def prefixEnd_634140 : Nat := 4983230072969 + 3 ^ 40 * 634140 * 2
def baseEnd_634140 : Nat := 108539540747418052677883

theorem tailTrace_634140 : CollatzResearch.WordTrace tailWord_634140 prefixEnd_634140 108539540747418052677883 := by
  unfold tailWord_634140
  simp only [CollatzResearch.WordTrace]
  refine ⟨11564492961313278667353937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15419323948417704889805249 11564492961313278667353937)
  ·
    refine ⟨8673369720984959000515453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11564492961313278667353937 8673369720984959000515453)
    ·
      refine ⟨3252513645369359625193295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8673369720984959000515453 3252513645369359625193295)
      ·
        refine ⟨4878770468054039437789943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3252513645369359625193295 4878770468054039437789943)
        ·
          refine ⟨7318155702081059156684915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4878770468054039437789943 7318155702081059156684915)
          ·
            refine ⟨10977233553121588735027373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7318155702081059156684915 10977233553121588735027373)
            ·
              refine ⟨4116462582420595775635265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10977233553121588735027373 4116462582420595775635265)
              ·
                refine ⟨3087346936815446831726449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4116462582420595775635265 3087346936815446831726449)
                ·
                  refine ⟨2315510202611585123794837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3087346936815446831726449 2315510202611585123794837)
                  ·
                    refine ⟨108539540747418052677883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2315510202611585123794837 108539540747418052677883)
                    ·
                      rfl

theorem cell23_634140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_634140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634140 prefixEnd_634140 := by exact prefixLift 634140
  have htrace : WordTrace (prefixWord ++ tailWord_634140) baseStart_634140 baseEnd_634140 := by
    simpa [prefixWord, tailWord_634140, baseEnd_634140] using wordTrace_append hprefix tailTrace_634140
  have hstable : (prefixWord ++ tailWord_634140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634140).length < 2 ^ (prefixWord ++ tailWord_634140).sum := by decide
  have hdescent : baseEnd_634140 < baseStart_634140 := by decide
  rcases family_descends (prefixWord ++ tailWord_634140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634141 : List Nat := [1, 4, 2, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_634141 : Nat := 118140960795 + 634141 * 2 ^ 59
def prefixEnd_634141 : Nat := 4983230072969 + 3 ^ 40 * 634141 * 2
def baseEnd_634141 : Nat := 325619135722908654121145

theorem tailTrace_634141 : CollatzResearch.WordTrace tailWord_634141 prefixEnd_634141 325619135722908654121145 := by
  unfold tailWord_634141
  simp only [CollatzResearch.WordTrace]
  refine ⟨23129022395622934505494277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15419348263748623003662851 23129022395622934505494277)
  ·
    refine ⟨4336691699179300219780177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23129022395622934505494277 4336691699179300219780177)
    ·
      refine ⟨3252518774384475164835133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4336691699179300219780177 3252518774384475164835133)
      ·
        refine ⟨1219694540394178186813175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3252518774384475164835133 1219694540394178186813175)
        ·
          refine ⟨1829541810591267280219763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219694540394178186813175 1829541810591267280219763)
          ·
            refine ⟨2744312715886900920329645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1829541810591267280219763 2744312715886900920329645)
            ·
              refine ⟨1029117268457587845123617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2744312715886900920329645 1029117268457587845123617)
              ·
                refine ⟨771837951343190883842713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1029117268457587845123617 771837951343190883842713)
                ·
                  refine ⟨578878463507393162882035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 771837951343190883842713 578878463507393162882035)
                  ·
                    refine ⟨868317695261089744323053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 578878463507393162882035 868317695261089744323053)
                    ·
                      refine ⟨325619135722908654121145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 868317695261089744323053 325619135722908654121145)
                      ·
                        rfl

theorem cell23_634141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_634141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634141 prefixEnd_634141 := by exact prefixLift 634141
  have htrace : WordTrace (prefixWord ++ tailWord_634141) baseStart_634141 baseEnd_634141 := by
    simpa [prefixWord, tailWord_634141, baseEnd_634141] using wordTrace_append hprefix tailTrace_634141
  have hstable : (prefixWord ++ tailWord_634141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634141).length < 2 ^ (prefixWord ++ tailWord_634141).sum := by decide
  have hdescent : baseEnd_634141 < baseStart_634141 := by decide
  rcases family_descends (prefixWord ++ tailWord_634141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634160 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 4]
def baseStart_634160 : Nat := 118140960795 + 634160 * 2 ^ 59
def prefixEnd_634160 : Nat := 4983230072969 + 3 ^ 40 * 634160 * 2
def baseEnd_634160 : Nat := 325628891855344079783557

theorem tailTrace_634160 : CollatzResearch.WordTrace tailWord_634160 prefixEnd_634160 325628891855344079783557 := by
  unfold tailWord_634160
  simp only [CollatzResearch.WordTrace]
  refine ⟨11564857691277050375217967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15419810255036067166957289 11564857691277050375217967)
  ·
    refine ⟨17347286536915575562826951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11564857691277050375217967 17347286536915575562826951)
    ·
      refine ⟨26020929805373363344240427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17347286536915575562826951 26020929805373363344240427)
      ·
        refine ⟨39031394708060045016360641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26020929805373363344240427 39031394708060045016360641)
        ·
          refine ⟨29273546031045033762270481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39031394708060045016360641 29273546031045033762270481)
          ·
            refine ⟨21955159523283775321702861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29273546031045033762270481 21955159523283775321702861)
            ·
              refine ⟨8233184821231415745638573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21955159523283775321702861 8233184821231415745638573)
              ·
                refine ⟨3087444307961780904614465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8233184821231415745638573 3087444307961780904614465)
                ·
                  refine ⟨2315583230971335678460849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3087444307961780904614465 2315583230971335678460849)
                  ·
                    refine ⟨1736687423228501758845637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2315583230971335678460849 1736687423228501758845637)
                    ·
                      refine ⟨325628891855344079783557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1736687423228501758845637 325628891855344079783557)
                      ·
                        rfl

theorem cell23_634160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_634160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634160 prefixEnd_634160 := by exact prefixLift 634160
  have htrace : WordTrace (prefixWord ++ tailWord_634160) baseStart_634160 baseEnd_634160 := by
    simpa [prefixWord, tailWord_634160, baseEnd_634160] using wordTrace_append hprefix tailTrace_634160
  have hstable : (prefixWord ++ tailWord_634160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634160).length < 2 ^ (prefixWord ++ tailWord_634160).sum := by decide
  have hdescent : baseEnd_634160 < baseStart_634160 := by decide
  rcases family_descends (prefixWord ++ tailWord_634160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634170 : List Nat := [3, 1, 1, 1, 4, 1, 1, 4, 7]
def baseStart_634170 : Nat := 118140960795 + 634170 * 2 ^ 59
def prefixEnd_634170 : Nat := 4983230072969 + 3 ^ 40 * 634170 * 2
def baseEnd_634170 : Nat := 36181558517987671184279

theorem tailTrace_634170 : CollatzResearch.WordTrace tailWord_634170 prefixEnd_634170 36181558517987671184279 := by
  unfold tailWord_634170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5782520028129468114574991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15420053408345248305533309 5782520028129468114574991)
  ·
    refine ⟨8673780042194202171862487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5782520028129468114574991 8673780042194202171862487)
    ·
      refine ⟨13010670063291303257793731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8673780042194202171862487 13010670063291303257793731)
      ·
        refine ⟨19516005094936954886690597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13010670063291303257793731 19516005094936954886690597)
        ·
          refine ⟨3659250955300679041254487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19516005094936954886690597 3659250955300679041254487)
          ·
            refine ⟨5488876432951018561881731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3659250955300679041254487 5488876432951018561881731)
            ·
              refine ⟨8233314649426527842822597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5488876432951018561881731 8233314649426527842822597)
              ·
                refine ⟨1543746496767473970529237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8233314649426527842822597 1543746496767473970529237)
                ·
                  refine ⟨36181558517987671184279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1543746496767473970529237 36181558517987671184279)
                  ·
                    rfl

theorem cell23_634170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_634170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634170 prefixEnd_634170 := by exact prefixLift 634170
  have htrace : WordTrace (prefixWord ++ tailWord_634170) baseStart_634170 baseEnd_634170 := by
    simpa [prefixWord, tailWord_634170, baseEnd_634170] using wordTrace_append hprefix tailTrace_634170
  have hstable : (prefixWord ++ tailWord_634170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634170).length < 2 ^ (prefixWord ++ tailWord_634170).sum := by decide
  have hdescent : baseEnd_634170 < baseStart_634170 := by decide
  rcases family_descends (prefixWord ++ tailWord_634170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634207 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 2, 5, 2]
def baseStart_634207 : Nat := 118140960795 + 634207 * 2 ^ 59
def prefixEnd_634207 : Nat := 4983230072969 + 3 ^ 40 * 634207 * 2
def baseEnd_634207 : Nat := 325653025446105395895841

theorem tailTrace_634207 : CollatzResearch.WordTrace tailWord_634207 prefixEnd_634207 325653025446105395895841 := by
  unfold tailWord_634207
  simp only [CollatzResearch.WordTrace]
  refine ⟨23131429613383827777396875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15420953075589218518264583 23131429613383827777396875)
  ·
    refine ⟨34697144420075741666095313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23131429613383827777396875 34697144420075741666095313)
    ·
      refine ⟨26022858315056806249571485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34697144420075741666095313 26022858315056806249571485)
      ·
        refine ⟨9758571868146302343589307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26022858315056806249571485 9758571868146302343589307)
        ·
          refine ⟨14637857802219453515383961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9758571868146302343589307 14637857802219453515383961)
          ·
            refine ⟨10978393351664590136537971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14637857802219453515383961 10978393351664590136537971)
            ·
              refine ⟨16467590027496885204806957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10978393351664590136537971 16467590027496885204806957)
              ·
                refine ⟨6175346260311331951802609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16467590027496885204806957 6175346260311331951802609)
                ·
                  refine ⟨4631509695233498963851957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6175346260311331951802609 4631509695233498963851957)
                  ·
                    refine ⟨434204033928140527861121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4631509695233498963851957 434204033928140527861121)
                    ·
                      refine ⟨325653025446105395895841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434204033928140527861121 325653025446105395895841)
                      ·
                        rfl

theorem cell23_634207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_634207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634207 prefixEnd_634207 := by exact prefixLift 634207
  have htrace : WordTrace (prefixWord ++ tailWord_634207) baseStart_634207 baseEnd_634207 := by
    simpa [prefixWord, tailWord_634207, baseEnd_634207] using wordTrace_append hprefix tailTrace_634207
  have hstable : (prefixWord ++ tailWord_634207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634207).length < 2 ^ (prefixWord ++ tailWord_634207).sum := by decide
  have hdescent : baseEnd_634207 < baseStart_634207 := by decide
  rcases family_descends (prefixWord ++ tailWord_634207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634215 : List Nat := [1, 1, 5, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_634215 : Nat := 118140960795 + 634215 * 2 ^ 59
def prefixEnd_634215 : Nat := 4983230072969 + 3 ^ 40 * 634215 * 2
def baseEnd_634215 : Nat := 325657133291341364595805

theorem tailTrace_634215 : CollatzResearch.WordTrace tailWord_634215 prefixEnd_634215 325657133291341364595805 := by
  unfold tailWord_634215
  simp only [CollatzResearch.WordTrace]
  refine ⟨23131721397354845143688099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15421147598236563429125399 23131721397354845143688099)
  ·
    refine ⟨34697582096032267715532149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23131721397354845143688099 34697582096032267715532149)
    ·
      refine ⟨3252898321503025098331139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34697582096032267715532149 3252898321503025098331139)
      ·
        refine ⟨4879347482254537647496709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3252898321503025098331139 4879347482254537647496709)
        ·
          refine ⟨914877652922725808905633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4879347482254537647496709 914877652922725808905633)
          ·
            refine ⟨686158239692044356679225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 914877652922725808905633 686158239692044356679225)
            ·
              refine ⟨514618679769033267509419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686158239692044356679225 514618679769033267509419)
              ·
                refine ⟨771928019653549901264129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514618679769033267509419 771928019653549901264129)
                ·
                  refine ⟨578946014740162425948097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 771928019653549901264129 578946014740162425948097)
                  ·
                    refine ⟨434209511055121819461073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 578946014740162425948097 434209511055121819461073)
                    ·
                      refine ⟨325657133291341364595805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434209511055121819461073 325657133291341364595805)
                      ·
                        rfl

theorem cell23_634215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_634215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634215 prefixEnd_634215 := by exact prefixLift 634215
  have htrace : WordTrace (prefixWord ++ tailWord_634215) baseStart_634215 baseEnd_634215 := by
    simpa [prefixWord, tailWord_634215, baseEnd_634215] using wordTrace_append hprefix tailTrace_634215
  have hstable : (prefixWord ++ tailWord_634215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634215).length < 2 ^ (prefixWord ++ tailWord_634215).sum := by decide
  have hdescent : baseEnd_634215 < baseStart_634215 := by decide
  rcases family_descends (prefixWord ++ tailWord_634215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634327 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 4]
def baseStart_634327 : Nat := 118140960795 + 634327 * 2 ^ 59
def prefixEnd_634327 : Nat := 4983230072969 + 3 ^ 40 * 634327 * 2
def baseEnd_634327 : Nat := 325714643124644926395289

theorem tailTrace_634327 : CollatzResearch.WordTrace tailWord_634327 prefixEnd_634327 325714643124644926395289 := by
  unfold tailWord_634327
  simp only [CollatzResearch.WordTrace]
  refine ⟨23135806372949088271765235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15423870915299392181176823 23135806372949088271765235)
  ·
    refine ⟨34703709559423632407647853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23135806372949088271765235 34703709559423632407647853)
    ·
      refine ⟨13013891084783862152867945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34703709559423632407647853 13013891084783862152867945)
      ·
        refine ⟨9760418313587896614650959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13013891084783862152867945 9760418313587896614650959)
        ·
          refine ⟨14640627470381844921976439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9760418313587896614650959 14640627470381844921976439)
          ·
            refine ⟨21960941205572767382964659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14640627470381844921976439 21960941205572767382964659)
            ·
              refine ⟨32941411808359151074446989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21960941205572767382964659 32941411808359151074446989)
              ·
                refine ⟨12353029428134681652917621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32941411808359151074446989 12353029428134681652917621)
                ·
                  refine ⟨1158096508887626404961027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12353029428134681652917621 1158096508887626404961027)
                  ·
                    refine ⟨1737144763331439607441541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1158096508887626404961027 1737144763331439607441541)
                    ·
                      refine ⟨325714643124644926395289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1737144763331439607441541 325714643124644926395289)
                      ·
                        rfl

theorem cell23_634327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_634327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634327 prefixEnd_634327 := by exact prefixLift 634327
  have htrace : WordTrace (prefixWord ++ tailWord_634327) baseStart_634327 baseEnd_634327 := by
    simpa [prefixWord, tailWord_634327, baseEnd_634327] using wordTrace_append hprefix tailTrace_634327
  have hstable : (prefixWord ++ tailWord_634327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634327).length < 2 ^ (prefixWord ++ tailWord_634327).sum := by decide
  have hdescent : baseEnd_634327 < baseStart_634327 := by decide
  rcases family_descends (prefixWord ++ tailWord_634327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634341 : List Nat := [1, 3, 1, 5, 1, 2, 2, 2, 1, 5]
def baseStart_634341 : Nat := 118140960795 + 634341 * 2 ^ 59
def prefixEnd_634341 : Nat := 4983230072969 + 3 ^ 40 * 634341 * 2
def baseEnd_634341 : Nat := 108573943951269290540075

theorem tailTrace_634341 : CollatzResearch.WordTrace tailWord_634341 prefixEnd_634341 108573943951269290540075 := by
  unfold tailWord_634341
  simp only [CollatzResearch.WordTrace]
  refine ⟨23136316994898368662774877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15424211329932245775183251 23136316994898368662774877)
  ·
    refine ⟨8676118873086888248540579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23136316994898368662774877 8676118873086888248540579)
    ·
      refine ⟨13014178309630332372810869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8676118873086888248540579 13014178309630332372810869)
      ·
        refine ⟨1220079216527843659951019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13014178309630332372810869 1220079216527843659951019)
        ·
          refine ⟨1830118824791765489926529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220079216527843659951019 1830118824791765489926529)
          ·
            refine ⟨1372589118593824117444897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1830118824791765489926529 1372589118593824117444897)
            ·
              refine ⟨1029441838945368088083673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1372589118593824117444897 1029441838945368088083673)
              ·
                refine ⟨772081379209026066062755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1029441838945368088083673 772081379209026066062755)
                ·
                  refine ⟨1158122068813539099094133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772081379209026066062755 1158122068813539099094133)
                  ·
                    refine ⟨108573943951269290540075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1158122068813539099094133 108573943951269290540075)
                    ·
                      rfl

theorem cell23_634341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_634341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634341 prefixEnd_634341 := by exact prefixLift 634341
  have htrace : WordTrace (prefixWord ++ tailWord_634341) baseStart_634341 baseEnd_634341 := by
    simpa [prefixWord, tailWord_634341, baseEnd_634341] using wordTrace_append hprefix tailTrace_634341
  have hstable : (prefixWord ++ tailWord_634341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634341).length < 2 ^ (prefixWord ++ tailWord_634341).sum := by decide
  have hdescent : baseEnd_634341 < baseStart_634341 := by decide
  rcases family_descends (prefixWord ++ tailWord_634341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634344 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_634344 : Nat := 118140960795 + 634344 * 2 ^ 59
def prefixEnd_634344 : Nat := 4983230072969 + 3 ^ 40 * 634344 * 2
def baseEnd_634344 : Nat := 325723372295771359882711

theorem tailTrace_634344 : CollatzResearch.WordTrace tailWord_634344 prefixEnd_634344 325723372295771359882711 := by
  unfold tailWord_634344
  simp only [CollatzResearch.WordTrace]
  refine ⟨11568213206943750087567043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15424284275925000116756057 11568213206943750087567043)
  ·
    refine ⟨17352319810415625131350565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11568213206943750087567043 17352319810415625131350565)
    ·
      refine ⟨3253559964452929712128231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17352319810415625131350565 3253559964452929712128231)
      ·
        refine ⟨4880339946679394568192347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3253559964452929712128231 4880339946679394568192347)
        ·
          refine ⟨7320509920019091852288521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4880339946679394568192347 7320509920019091852288521)
          ·
            refine ⟨5490382440014318889216391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7320509920019091852288521 5490382440014318889216391)
            ·
              refine ⟨8235573660021478333824587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5490382440014318889216391 8235573660021478333824587)
              ·
                refine ⟨12353360490032217500736881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8235573660021478333824587 12353360490032217500736881)
                ·
                  refine ⟨9265020367524163125552661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12353360490032217500736881 9265020367524163125552661)
                  ·
                    refine ⟨434297829727695146510281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9265020367524163125552661 434297829727695146510281)
                    ·
                      refine ⟨325723372295771359882711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434297829727695146510281 325723372295771359882711)
                      ·
                        rfl

theorem cell23_634344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_634344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634344 prefixEnd_634344 := by exact prefixLift 634344
  have htrace : WordTrace (prefixWord ++ tailWord_634344) baseStart_634344 baseEnd_634344 := by
    simpa [prefixWord, tailWord_634344, baseEnd_634344] using wordTrace_append hprefix tailTrace_634344
  have hstable : (prefixWord ++ tailWord_634344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634344).length < 2 ^ (prefixWord ++ tailWord_634344).sum := by decide
  have hdescent : baseEnd_634344 < baseStart_634344 := by decide
  rcases family_descends (prefixWord ++ tailWord_634344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634372 : List Nat := [2, 3, 2, 3, 2, 1, 3, 2, 1, 1, 3]
def baseStart_634372 : Nat := 118140960795 + 634372 * 2 ^ 59
def prefixEnd_634372 : Nat := 4983230072969 + 3 ^ 40 * 634372 * 2
def baseEnd_634372 : Nat := 325737749754097250332583

theorem tailTrace_634372 : CollatzResearch.WordTrace tailWord_634372 prefixEnd_634372 325737749754097250332583 := by
  unfold tailWord_634372
  simp only [CollatzResearch.WordTrace]
  refine ⟨11568723828893030478576685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15424965105190707304768913 11568723828893030478576685)
  ·
    refine ⟨4338271435834886429466257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11568723828893030478576685 4338271435834886429466257)
    ·
      refine ⟨3253703576876164822099693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4338271435834886429466257 3253703576876164822099693)
      ·
        refine ⟨1220138841328561808287385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3253703576876164822099693 1220138841328561808287385)
        ·
          refine ⟨915104130996421356215539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1220138841328561808287385 915104130996421356215539)
          ·
            refine ⟨1372656196494632034323309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915104130996421356215539 1372656196494632034323309)
            ·
              refine ⟨514746073685487012871241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1372656196494632034323309 514746073685487012871241)
              ·
                refine ⟨386059555264115259653431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514746073685487012871241 386059555264115259653431)
                ·
                  refine ⟨579089332896172889480147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386059555264115259653431 579089332896172889480147)
                  ·
                    refine ⟨868633999344259334220221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 579089332896172889480147 868633999344259334220221)
                    ·
                      refine ⟨325737749754097250332583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 868633999344259334220221 325737749754097250332583)
                      ·
                        rfl

theorem cell23_634372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_634372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634372 prefixEnd_634372 := by exact prefixLift 634372
  have htrace : WordTrace (prefixWord ++ tailWord_634372) baseStart_634372 baseEnd_634372 := by
    simpa [prefixWord, tailWord_634372, baseEnd_634372] using wordTrace_append hprefix tailTrace_634372
  have hstable : (prefixWord ++ tailWord_634372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634372).length < 2 ^ (prefixWord ++ tailWord_634372).sum := by decide
  have hdescent : baseEnd_634372 < baseStart_634372 := by decide
  rcases family_descends (prefixWord ++ tailWord_634372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634378 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 3, 2, 2]
def baseStart_634378 : Nat := 118140960795 + 634378 * 2 ^ 59
def prefixEnd_634378 : Nat := 4983230072969 + 3 ^ 40 * 634378 * 2
def baseEnd_634378 : Nat := 325740830638024226857555

theorem tailTrace_634378 : CollatzResearch.WordTrace tailWord_634378 prefixEnd_634378 325740830638024226857555 := by
  unfold tailWord_634378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784416623941080995467947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15425110997176215987914525 5784416623941080995467947)
  ·
    refine ⟨8676624935911621493201921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5784416623941080995467947 8676624935911621493201921)
    ·
      refine ⟨6507468701933716119901441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8676624935911621493201921 6507468701933716119901441)
      ·
        refine ⟨4880601526450287089926081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6507468701933716119901441 4880601526450287089926081)
        ·
          refine ⟨3660451144837715317444561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4880601526450287089926081 3660451144837715317444561)
          ·
            refine ⟨2745338358628286488083421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3660451144837715317444561 2745338358628286488083421)
            ·
              refine ⟨1029501884485607433031283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2745338358628286488083421 1029501884485607433031283)
              ·
                refine ⟨1544252826728411149546925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029501884485607433031283 1544252826728411149546925)
                ·
                  refine ⟨579094810023154181080097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1544252826728411149546925 579094810023154181080097)
                  ·
                    refine ⟨434321107517365635810073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 579094810023154181080097 434321107517365635810073)
                    ·
                      refine ⟨325740830638024226857555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434321107517365635810073 325740830638024226857555)
                      ·
                        rfl

theorem cell23_634378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_634378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634378 prefixEnd_634378 := by exact prefixLift 634378
  have htrace : WordTrace (prefixWord ++ tailWord_634378) baseStart_634378 baseEnd_634378 := by
    simpa [prefixWord, tailWord_634378, baseEnd_634378] using wordTrace_append hprefix tailTrace_634378
  have hstable : (prefixWord ++ tailWord_634378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634378).length < 2 ^ (prefixWord ++ tailWord_634378).sum := by decide
  have hdescent : baseEnd_634378 < baseStart_634378 := by decide
  rcases family_descends (prefixWord ++ tailWord_634378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634394 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3]
def baseStart_634394 : Nat := 118140960795 + 634394 * 2 ^ 59
def prefixEnd_634394 : Nat := 4983230072969 + 3 ^ 40 * 634394 * 2
def baseEnd_634394 : Nat := 325749046328496164257481

theorem tailTrace_634394 : CollatzResearch.WordTrace tailWord_634394 prefixEnd_634394 325749046328496164257481 := by
  unfold tailWord_634394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784562515926589678613559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15425500042470905809636157 5784562515926589678613559)
  ·
    refine ⟨8676843773889884517920339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5784562515926589678613559 8676843773889884517920339)
    ·
      refine ⟨13015265660834826776880509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8676843773889884517920339 13015265660834826776880509)
      ·
        refine ⟨4880724622813060041330191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13015265660834826776880509 4880724622813060041330191)
        ·
          refine ⟨7321086934219590061995287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4880724622813060041330191 7321086934219590061995287)
          ·
            refine ⟨10981630401329385092992931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7321086934219590061995287 10981630401329385092992931)
            ·
              refine ⟨16472445601994077639489397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10981630401329385092992931 16472445601994077639489397)
              ·
                refine ⟨1544291775186944778702131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16472445601994077639489397 1544291775186944778702131)
                ·
                  refine ⟨2316437662780417168053197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544291775186944778702131 2316437662780417168053197)
                  ·
                    refine ⟨868664123542656438019949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2316437662780417168053197 868664123542656438019949)
                    ·
                      refine ⟨325749046328496164257481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 868664123542656438019949 325749046328496164257481)
                      ·
                        rfl

theorem cell23_634394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_634394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634394 prefixEnd_634394 := by exact prefixLift 634394
  have htrace : WordTrace (prefixWord ++ tailWord_634394) baseStart_634394 baseEnd_634394 := by
    simpa [prefixWord, tailWord_634394, baseEnd_634394] using wordTrace_append hprefix tailTrace_634394
  have hstable : (prefixWord ++ tailWord_634394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634394).length < 2 ^ (prefixWord ++ tailWord_634394).sum := by decide
  have hdescent : baseEnd_634394 < baseStart_634394 := by decide
  rcases family_descends (prefixWord ++ tailWord_634394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634429 : List Nat := [1, 4, 1, 3, 3, 2, 2, 2, 1, 2, 2]
def baseStart_634429 : Nat := 118140960795 + 634429 * 2 ^ 59
def prefixEnd_634429 : Nat := 4983230072969 + 3 ^ 40 * 634429 * 2
def baseEnd_634429 : Nat := 325767018151403527319821

theorem tailTrace_634429 : CollatzResearch.WordTrace tailWord_634429 prefixEnd_634429 325767018151403527319821 := by
  unfold tailWord_634429
  simp only [CollatzResearch.WordTrace]
  refine ⟨23139526618579559691978341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15426351079053039794652227 23139526618579559691978341)
  ·
    refine ⟨4338661240983667442245939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23139526618579559691978341 4338661240983667442245939)
    ·
      refine ⟨6507991861475501163368909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4338661240983667442245939 6507991861475501163368909)
      ·
        refine ⟨2440496948053312936263341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6507991861475501163368909 2440496948053312936263341)
        ·
          refine ⟨915186355519992351098753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2440496948053312936263341 915186355519992351098753)
          ·
            refine ⟨686389766639994263324065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 915186355519992351098753 686389766639994263324065)
            ·
              refine ⟨514792324979995697493049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686389766639994263324065 514792324979995697493049)
              ·
                refine ⟨386094243734996773119787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514792324979995697493049 386094243734996773119787)
                ·
                  refine ⟨579141365602495159679681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386094243734996773119787 579141365602495159679681)
                  ·
                    refine ⟨434356024201871369759761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 579141365602495159679681 434356024201871369759761)
                    ·
                      refine ⟨325767018151403527319821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434356024201871369759761 325767018151403527319821)
                      ·
                        rfl

theorem cell23_634429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_634429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634429 prefixEnd_634429 := by exact prefixLift 634429
  have htrace : WordTrace (prefixWord ++ tailWord_634429) baseStart_634429 baseEnd_634429 := by
    simpa [prefixWord, tailWord_634429, baseEnd_634429] using wordTrace_append hprefix tailTrace_634429
  have hstable : (prefixWord ++ tailWord_634429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634429).length < 2 ^ (prefixWord ++ tailWord_634429).sum := by decide
  have hdescent : baseEnd_634429 < baseStart_634429 := by decide
  rcases family_descends (prefixWord ++ tailWord_634429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634444 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 2, 6]
def baseStart_634444 : Nat := 118140960795 + 634444 * 2 ^ 59
def prefixEnd_634444 : Nat := 4983230072969 + 3 ^ 40 * 634444 * 2
def baseEnd_634444 : Nat := 108591573453740322877417

theorem tailTrace_634444 : CollatzResearch.WordTrace tailWord_634444 prefixEnd_634444 108591573453740322877417 := by
  unfold tailWord_634444
  simp only [CollatzResearch.WordTrace]
  refine ⟨11570036856762608626887193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15426715809016811502516257 11570036856762608626887193)
  ·
    refine ⟨8677527642571956470165395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11570036856762608626887193 8677527642571956470165395)
    ·
      refine ⟨13016291463857934705248093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8677527642571956470165395 13016291463857934705248093)
      ·
        refine ⟨4881109298946725514468035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13016291463857934705248093 4881109298946725514468035)
        ·
          refine ⟨7321663948420088271702053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4881109298946725514468035 7321663948420088271702053)
          ·
            refine ⟨1372811990328766550944135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7321663948420088271702053 1372811990328766550944135)
            ·
              refine ⟨2059217985493149826416203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372811990328766550944135 2059217985493149826416203)
              ·
                refine ⟨3088826978239724739624305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059217985493149826416203 3088826978239724739624305)
                ·
                  refine ⟨2316620233679793554718229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3088826978239724739624305 2316620233679793554718229)
                  ·
                    refine ⟨108591573453740322877417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2316620233679793554718229 108591573453740322877417)
                    ·
                      rfl

theorem cell23_634444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_634444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634444 prefixEnd_634444 := by exact prefixLift 634444
  have htrace : WordTrace (prefixWord ++ tailWord_634444) baseStart_634444 baseEnd_634444 := by
    simpa [prefixWord, tailWord_634444, baseEnd_634444] using wordTrace_append hprefix tailTrace_634444
  have hstable : (prefixWord ++ tailWord_634444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634444).length < 2 ^ (prefixWord ++ tailWord_634444).sum := by decide
  have hdescent : baseEnd_634444 < baseStart_634444 := by decide
  rcases family_descends (prefixWord ++ tailWord_634444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634472 : List Nat := [2, 1, 4, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_634472 : Nat := 118140960795 + 634472 * 2 ^ 59
def prefixEnd_634472 : Nat := 4983230072969 + 3 ^ 40 * 634472 * 2
def baseEnd_634472 : Nat := 325789097819546859082123

theorem tailTrace_634472 : CollatzResearch.WordTrace tailWord_634472 prefixEnd_634472 325789097819546859082123 := by
  unfold tailWord_634472
  simp only [CollatzResearch.WordTrace]
  refine ⟨11570547478711889017896835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15427396638282518690529113 11570547478711889017896835)
  ·
    refine ⟨17355821218067833526845253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11570547478711889017896835 17355821218067833526845253)
    ·
      refine ⟨3254216478387718786283485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17355821218067833526845253 3254216478387718786283485)
      ·
        refine ⟨1220331179395394544856307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3254216478387718786283485 1220331179395394544856307)
        ·
          refine ⟨1830496769093091817284461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220331179395394544856307 1830496769093091817284461)
          ·
            refine ⟨686436288409909431481673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1830496769093091817284461 686436288409909431481673)
            ·
              refine ⟨514827216307432073611255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686436288409909431481673 514827216307432073611255)
              ·
                refine ⟨772240824461148110416883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514827216307432073611255 772240824461148110416883)
                ·
                  refine ⟨1158361236691722165625325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772240824461148110416883 1158361236691722165625325)
                  ·
                    refine ⟨434385463759395812109497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1158361236691722165625325 434385463759395812109497)
                    ·
                      refine ⟨325789097819546859082123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434385463759395812109497 325789097819546859082123)
                      ·
                        rfl

theorem cell23_634472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_634472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634472 prefixEnd_634472 := by exact prefixLift 634472
  have htrace : WordTrace (prefixWord ++ tailWord_634472) baseStart_634472 baseEnd_634472 := by
    simpa [prefixWord, tailWord_634472, baseEnd_634472] using wordTrace_append hprefix tailTrace_634472
  have hstable : (prefixWord ++ tailWord_634472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634472).length < 2 ^ (prefixWord ++ tailWord_634472).sum := by decide
  have hdescent : baseEnd_634472 < baseStart_634472 := by decide
  rcases family_descends (prefixWord ++ tailWord_634472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634485 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_634485 : Nat := 118140960795 + 634485 * 2 ^ 59
def prefixEnd_634485 : Nat := 4983230072969 + 3 ^ 40 * 634485 * 2
def baseEnd_634485 : Nat := 325795773068055308219563

theorem tailTrace_634485 : CollatzResearch.WordTrace tailWord_634485 prefixEnd_634485 325795773068055308219563 := by
  unfold tailWord_634485
  simp only [CollatzResearch.WordTrace]
  refine ⟨23141569106376681256016909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15427712737584454170677939 23141569106376681256016909)
  ·
    refine ⟨8678088414891255471006341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23141569106376681256016909 8678088414891255471006341)
    ·
      refine ⟨1627141577792110400813689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8678088414891255471006341 1627141577792110400813689)
      ·
        refine ⟨1220356183344082800610267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1627141577792110400813689 1220356183344082800610267)
        ·
          refine ⟨1830534275016124200915401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220356183344082800610267 1830534275016124200915401)
          ·
            refine ⟨1372900706262093150686551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1830534275016124200915401 1372900706262093150686551)
            ·
              refine ⟨2059351059393139726029827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372900706262093150686551 2059351059393139726029827)
              ·
                refine ⟨3089026589089709589044741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059351059393139726029827 3089026589089709589044741)
                ·
                  refine ⟨579192485454320547945889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3089026589089709589044741 579192485454320547945889)
                  ·
                    refine ⟨434394364090740410959417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 579192485454320547945889 434394364090740410959417)
                    ·
                      refine ⟨325795773068055308219563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434394364090740410959417 325795773068055308219563)
                      ·
                        rfl

theorem cell23_634485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_634485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634485 prefixEnd_634485 := by exact prefixLift 634485
  have htrace : WordTrace (prefixWord ++ tailWord_634485) baseStart_634485 baseEnd_634485 := by
    simpa [prefixWord, tailWord_634485, baseEnd_634485] using wordTrace_append hprefix tailTrace_634485
  have hstable : (prefixWord ++ tailWord_634485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634485).length < 2 ^ (prefixWord ++ tailWord_634485).sum := by decide
  have hdescent : baseEnd_634485 < baseStart_634485 := by decide
  rcases family_descends (prefixWord ++ tailWord_634485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634542 : List Nat := [4, 1, 4, 1, 2, 1, 3, 2, 5]
def baseStart_634542 : Nat := 118140960795 + 634542 * 2 ^ 59
def prefixEnd_634542 : Nat := 4983230072969 + 3 ^ 40 * 634542 * 2
def baseEnd_634542 : Nat := 36202782385040176134089

theorem tailTrace_634542 : CollatzResearch.WordTrace tailWord_634542 prefixEnd_634542 36202782385040176134089 := by
  unfold tailWord_634542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2892956008396272498855235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15429098711446786660561253 2892956008396272498855235)
  ·
    refine ⟨4339434012594408748282853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2892956008396272498855235 4339434012594408748282853)
    ·
      refine ⟨813643877361451640303035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4339434012594408748282853 813643877361451640303035)
      ·
        refine ⟨1220465816042177460454553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 813643877361451640303035 1220465816042177460454553)
        ·
          refine ⟨915349362031633095340915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1220465816042177460454553 915349362031633095340915)
          ·
            refine ⟨1373024043047449643011373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915349362031633095340915 1373024043047449643011373)
            ·
              refine ⟨514884016142793616129265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1373024043047449643011373 514884016142793616129265)
              ·
                refine ⟨386163012107095212096949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 514884016142793616129265 386163012107095212096949)
                ·
                  refine ⟨36202782385040176134089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 386163012107095212096949 36202782385040176134089)
                  ·
                    rfl

theorem cell23_634542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_634542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634542 prefixEnd_634542 := by exact prefixLift 634542
  have htrace : WordTrace (prefixWord ++ tailWord_634542) baseStart_634542 baseEnd_634542 := by
    simpa [prefixWord, tailWord_634542, baseEnd_634542] using wordTrace_append hprefix tailTrace_634542
  have hstable : (prefixWord ++ tailWord_634542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634542).length < 2 ^ (prefixWord ++ tailWord_634542).sum := by decide
  have hdescent : baseEnd_634542 < baseStart_634542 := by decide
  rcases family_descends (prefixWord ++ tailWord_634542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634578 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_634578 : Nat := 118140960795 + 634578 * 2 ^ 59
def prefixEnd_634578 : Nat := 4983230072969 + 3 ^ 40 * 634578 * 2
def baseEnd_634578 : Nat := 325843526768923444356635

theorem tailTrace_634578 : CollatzResearch.WordTrace tailWord_634578 prefixEnd_634578 325843526768923444356635 := by
  unfold tailWord_634578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5786240273759939534788097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15429974063359838759434925 5786240273759939534788097)
  ·
    refine ⟨4339680205319954651091073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5786240273759939534788097 4339680205319954651091073)
    ·
      refine ⟨3254760153989965988318305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4339680205319954651091073 3254760153989965988318305)
      ·
        refine ⟨2441070115492474491238729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3254760153989965988318305 2441070115492474491238729)
        ·
          refine ⟨1830802586619355868429047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2441070115492474491238729 1830802586619355868429047)
          ·
            refine ⟨2746203879929033802643571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1830802586619355868429047 2746203879929033802643571)
            ·
              refine ⟨4119305819893550703965357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746203879929033802643571 4119305819893550703965357)
              ·
                refine ⟨1544739682460081513987009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4119305819893550703965357 1544739682460081513987009)
                ·
                  refine ⟨1158554761845061135490257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1544739682460081513987009 1158554761845061135490257)
                  ·
                    refine ⟨868916071383795851617693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1158554761845061135490257 868916071383795851617693)
                    ·
                      refine ⟨325843526768923444356635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 868916071383795851617693 325843526768923444356635)
                      ·
                        rfl

theorem cell23_634578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_634578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634578 prefixEnd_634578 := by exact prefixLift 634578
  have htrace : WordTrace (prefixWord ++ tailWord_634578) baseStart_634578 baseEnd_634578 := by
    simpa [prefixWord, tailWord_634578, baseEnd_634578] using wordTrace_append hprefix tailTrace_634578
  have hstable : (prefixWord ++ tailWord_634578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634578).length < 2 ^ (prefixWord ++ tailWord_634578).sum := by decide
  have hdescent : baseEnd_634578 < baseStart_634578 := by decide
  rcases family_descends (prefixWord ++ tailWord_634578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634601 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 3, 5, 2]
def baseStart_634601 : Nat := 118140960795 + 634601 * 2 ^ 59
def prefixEnd_634601 : Nat := 4983230072969 + 3 ^ 40 * 634601 * 2
def baseEnd_634601 : Nat := 325855336823976854369029

theorem tailTrace_634601 : CollatzResearch.WordTrace tailWord_634601 prefixEnd_634601 325855336823976854369029 := by
  unfold tailWord_634601
  simp only [CollatzResearch.WordTrace]
  refine ⟨23145799973956433067239657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15430533315970955378159771 23145799973956433067239657)
  ·
    refine ⟨17359349980467324800429743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23145799973956433067239657 17359349980467324800429743)
    ·
      refine ⟨26039024970700987200644615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17359349980467324800429743 26039024970700987200644615)
      ·
        refine ⟨39058537456051480800966923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26039024970700987200644615 39058537456051480800966923)
        ·
          refine ⟨58587806184077221201450385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39058537456051480800966923 58587806184077221201450385)
          ·
            refine ⟨43940854638057915901087789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58587806184077221201450385 43940854638057915901087789)
            ·
              refine ⟨16477820489271718462907921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43940854638057915901087789 16477820489271718462907921)
              ·
                refine ⟨12358365366953788847180941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16477820489271718462907921 12358365366953788847180941)
                ·
                  refine ⟨4634387012607670817692853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12358365366953788847180941 4634387012607670817692853)
                  ·
                    refine ⟨434473782431969139158705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4634387012607670817692853 434473782431969139158705)
                    ·
                      refine ⟨325855336823976854369029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434473782431969139158705 325855336823976854369029)
                      ·
                        rfl

theorem cell23_634601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 5, 2].length) (baseStart_634601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634601 prefixEnd_634601 := by exact prefixLift 634601
  have htrace : WordTrace (prefixWord ++ tailWord_634601) baseStart_634601 baseEnd_634601 := by
    simpa [prefixWord, tailWord_634601, baseEnd_634601] using wordTrace_append hprefix tailTrace_634601
  have hstable : (prefixWord ++ tailWord_634601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634601).length < 2 ^ (prefixWord ++ tailWord_634601).sum := by decide
  have hdescent : baseEnd_634601 < baseStart_634601 := by decide
  rcases family_descends (prefixWord ++ tailWord_634601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634624 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 5, 6]
def baseStart_634624 : Nat := 118140960795 + 634624 * 2 ^ 59
def prefixEnd_634624 : Nat := 4983230072969 + 3 ^ 40 * 634624 * 2
def baseEnd_634624 : Nat := 108622382293010088127141

theorem tailTrace_634624 : CollatzResearch.WordTrace tailWord_634624 prefixEnd_634624 108622382293010088127141 := by
  unfold tailWord_634624
  simp only [CollatzResearch.WordTrace]
  refine ⟨11573319426436553997663463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15431092568582071996884617 11573319426436553997663463)
  ·
    refine ⟨17359979139654830996495195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11573319426436553997663463 17359979139654830996495195)
    ·
      refine ⟨26039968709482246494742793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17359979139654830996495195 26039968709482246494742793)
      ·
        refine ⟨19529976532111684871057095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26039968709482246494742793 19529976532111684871057095)
        ·
          refine ⟨29294964798167527306585643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19529976532111684871057095 29294964798167527306585643)
          ·
            refine ⟨43942447197251290959878465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29294964798167527306585643 43942447197251290959878465)
            ·
              refine ⟨32956835397938468219908849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43942447197251290959878465 32956835397938468219908849)
              ·
                refine ⟨24717626548453851164931637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32956835397938468219908849 24717626548453851164931637)
                ·
                  refine ⟨2317277488917548546712341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24717626548453851164931637 2317277488917548546712341)
                  ·
                    refine ⟨108622382293010088127141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2317277488917548546712341 108622382293010088127141)
                    ·
                      rfl

theorem cell23_634624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 5, 6].length) (baseStart_634624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634624 prefixEnd_634624 := by exact prefixLift 634624
  have htrace : WordTrace (prefixWord ++ tailWord_634624) baseStart_634624 baseEnd_634624 := by
    simpa [prefixWord, tailWord_634624, baseEnd_634624] using wordTrace_append hprefix tailTrace_634624
  have hstable : (prefixWord ++ tailWord_634624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634624).length < 2 ^ (prefixWord ++ tailWord_634624).sum := by decide
  have hdescent : baseEnd_634624 < baseStart_634624 := by decide
  rcases family_descends (prefixWord ++ tailWord_634624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634641 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 4, 4]
def baseStart_634641 : Nat := 118140960795 + 634641 * 2 ^ 59
def prefixEnd_634641 : Nat := 4983230072969 + 3 ^ 40 * 634641 * 2
def baseEnd_634641 : Nat := 108625292016718899289615

theorem tailTrace_634641 : CollatzResearch.WordTrace tailWord_634641 prefixEnd_634641 108625292016718899289615 := by
  unfold tailWord_634641
  simp only [CollatzResearch.WordTrace]
  refine ⟨23147258893811519898695777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15431505929207679932463851 23147258893811519898695777)
  ·
    refine ⟨17360444170358639924021833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23147258893811519898695777 17360444170358639924021833)
    ·
      refine ⟨13020333127768979943016375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17360444170358639924021833 13020333127768979943016375)
      ·
        refine ⟨19530499691653469914524563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13020333127768979943016375 19530499691653469914524563)
        ·
          refine ⟨29295749537480204871786845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19530499691653469914524563 29295749537480204871786845)
          ·
            refine ⟨10985906076555076826920067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29295749537480204871786845 10985906076555076826920067)
            ·
              refine ⟨16478859114832615240380101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10985906076555076826920067 16478859114832615240380101)
              ·
                refine ⟨3089786084031115357571269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16478859114832615240380101 3089786084031115357571269)
                ·
                  refine ⟨579334890755834129544613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3089786084031115357571269 579334890755834129544613)
                  ·
                    refine ⟨108625292016718899289615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 579334890755834129544613 108625292016718899289615)
                    ·
                      rfl

theorem cell23_634641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_634641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634641 prefixEnd_634641 := by exact prefixLift 634641
  have htrace : WordTrace (prefixWord ++ tailWord_634641) baseStart_634641 baseEnd_634641 := by
    simpa [prefixWord, tailWord_634641, baseEnd_634641] using wordTrace_append hprefix tailTrace_634641
  have hstable : (prefixWord ++ tailWord_634641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634641).length < 2 ^ (prefixWord ++ tailWord_634641).sum := by decide
  have hdescent : baseEnd_634641 < baseStart_634641 := by decide
  rcases family_descends (prefixWord ++ tailWord_634641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634645 : List Nat := [1, 3, 2, 1, 2, 5, 2, 1, 1, 5]
def baseStart_634645 : Nat := 118140960795 + 634645 * 2 ^ 59
def prefixEnd_634645 : Nat := 4983230072969 + 3 ^ 40 * 634645 * 2
def baseEnd_634645 : Nat := 108625976657591560739609

theorem tailTrace_634645 : CollatzResearch.WordTrace tailWord_634645 prefixEnd_634645 108625976657591560739609 := by
  unfold tailWord_634645
  simp only [CollatzResearch.WordTrace]
  refine ⟨23147404785797028581841389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15431603190531352387894259 23147404785797028581841389)
  ·
    refine ⟨8680276794673885718190521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23147404785797028581841389 8680276794673885718190521)
    ·
      refine ⟨6510207596005414288642891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8680276794673885718190521 6510207596005414288642891)
      ·
        refine ⟨9765311394008121432964337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6510207596005414288642891 9765311394008121432964337)
        ·
          refine ⟨7323983545506091074723253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9765311394008121432964337 7323983545506091074723253)
          ·
            refine ⟨686623457391196038255305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7323983545506091074723253 686623457391196038255305)
            ·
              refine ⟨514967593043397028691479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686623457391196038255305 514967593043397028691479)
              ·
                refine ⟨772451389565095543037219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 514967593043397028691479 772451389565095543037219)
                ·
                  refine ⟨1158677084347643314555829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772451389565095543037219 1158677084347643314555829)
                  ·
                    refine ⟨108625976657591560739609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1158677084347643314555829 108625976657591560739609)
                    ·
                      rfl

theorem cell23_634645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_634645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634645 prefixEnd_634645 := by exact prefixLift 634645
  have htrace : WordTrace (prefixWord ++ tailWord_634645) baseStart_634645 baseEnd_634645 := by
    simpa [prefixWord, tailWord_634645, baseEnd_634645] using wordTrace_append hprefix tailTrace_634645
  have hstable : (prefixWord ++ tailWord_634645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634645).length < 2 ^ (prefixWord ++ tailWord_634645).sum := by decide
  have hdescent : baseEnd_634645 < baseStart_634645 := by decide
  rcases family_descends (prefixWord ++ tailWord_634645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634658 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_634658 : Nat := 118140960795 + 634658 * 2 ^ 59
def prefixEnd_634658 : Nat := 4983230072969 + 3 ^ 40 * 634658 * 2
def baseEnd_634658 : Nat := 108628201740427710452089

theorem tailTrace_634658 : CollatzResearch.WordTrace tailWord_634658 prefixEnd_634658 108628201740427710452089 := by
  unfold tailWord_634658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5786969733687482950516157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15431919289833287868043085 5786969733687482950516157)
  ·
    refine ⟨2170113650132806106443559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5786969733687482950516157 2170113650132806106443559)
    ·
      refine ⟨3255170475199209159665339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2170113650132806106443559 3255170475199209159665339)
      ·
        refine ⟨4882755712798813739498009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3255170475199209159665339 4882755712798813739498009)
        ·
          refine ⟨3662066784599110304623507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4882755712798813739498009 3662066784599110304623507)
          ·
            refine ⟨5493100176898665456935261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3662066784599110304623507 5493100176898665456935261)
            ·
              refine ⟨2059912566336999546350723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5493100176898665456935261 2059912566336999546350723)
              ·
                refine ⟨3089868849505499319526085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2059912566336999546350723 3089868849505499319526085)
                ·
                  refine ⟨579350409282281122411141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3089868849505499319526085 579350409282281122411141)
                  ·
                    refine ⟨108628201740427710452089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 579350409282281122411141 108628201740427710452089)
                    ·
                      rfl

theorem cell23_634658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_634658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634658 prefixEnd_634658 := by exact prefixLift 634658
  have htrace : WordTrace (prefixWord ++ tailWord_634658) baseStart_634658 baseEnd_634658 := by
    simpa [prefixWord, tailWord_634658, baseEnd_634658] using wordTrace_append hprefix tailTrace_634658
  have hstable : (prefixWord ++ tailWord_634658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634658).length < 2 ^ (prefixWord ++ tailWord_634658).sum := by decide
  have hdescent : baseEnd_634658 < baseStart_634658 := by decide
  rcases family_descends (prefixWord ++ tailWord_634658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634675 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 1, 6]
def baseStart_634675 : Nat := 118140960795 + 634675 * 2 ^ 59
def prefixEnd_634675 : Nat := 4983230072969 + 3 ^ 40 * 634675 * 2
def baseEnd_634675 : Nat := 108631111464136521614563

theorem tailTrace_634675 : CollatzResearch.WordTrace tailWord_634675 prefixEnd_634675 108631111464136521614563 := by
  unfold tailWord_634675
  simp only [CollatzResearch.WordTrace]
  refine ⟨23148498975688343705433479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15432332650458895803622319 23148498975688343705433479)
  ·
    refine ⟨34722748463532515558150219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23148498975688343705433479 34722748463532515558150219)
    ·
      refine ⟨52084122695298773337225329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34722748463532515558150219 52084122695298773337225329)
      ·
        refine ⟨39063092021474080002918997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52084122695298773337225329 39063092021474080002918997)
        ·
          refine ⟨457770609626649375034207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 39063092021474080002918997 457770609626649375034207)
          ·
            refine ⟨686655914439974062551311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457770609626649375034207 686655914439974062551311)
            ·
              refine ⟨1029983871659961093826967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686655914439974062551311 1029983871659961093826967)
              ·
                refine ⟨1544975807489941640740451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1029983871659961093826967 1544975807489941640740451)
                ·
                  refine ⟨2317463711234912461110677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1544975807489941640740451 2317463711234912461110677)
                  ·
                    refine ⟨108631111464136521614563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2317463711234912461110677 108631111464136521614563)
                    ·
                      rfl

theorem cell23_634675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 1, 6].length) (baseStart_634675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634675 prefixEnd_634675 := by exact prefixLift 634675
  have htrace : WordTrace (prefixWord ++ tailWord_634675) baseStart_634675 baseEnd_634675 := by
    simpa [prefixWord, tailWord_634675, baseEnd_634675] using wordTrace_append hprefix tailTrace_634675
  have hstable : (prefixWord ++ tailWord_634675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634675).length < 2 ^ (prefixWord ++ tailWord_634675).sum := by decide
  have hdescent : baseEnd_634675 < baseStart_634675 := by decide
  rcases family_descends (prefixWord ++ tailWord_634675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634685 : List Nat := [1, 4, 1, 4, 1, 1, 1, 4, 1, 2, 3]
def baseStart_634685 : Nat := 118140960795 + 634685 * 2 ^ 59
def prefixEnd_634685 : Nat := 4983230072969 + 3 ^ 40 * 634685 * 2
def baseEnd_634685 : Nat := 325898469198954525718643

theorem tailTrace_634685 : CollatzResearch.WordTrace tailWord_634685 prefixEnd_634685 325898469198954525718643 := by
  unfold tailWord_634685
  simp only [CollatzResearch.WordTrace]
  refine ⟨23148863705652115413297509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15432575803768076942198339 23148863705652115413297509)
  ·
    refine ⟨4340411944809771639993283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23148863705652115413297509 4340411944809771639993283)
    ·
      refine ⟨6510617917214657459989925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4340411944809771639993283 6510617917214657459989925)
      ·
        refine ⟨1220740859477748273748111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6510617917214657459989925 1220740859477748273748111)
        ·
          refine ⟨1831111289216622410622167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220740859477748273748111 1831111289216622410622167)
          ·
            refine ⟨2746666933824933615933251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1831111289216622410622167 2746666933824933615933251)
            ·
              refine ⟨4120000400737400423899877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2746666933824933615933251 4120000400737400423899877)
              ·
                refine ⟨772500075138262579481227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4120000400737400423899877 772500075138262579481227)
                ·
                  refine ⟨1158750112707393869221841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772500075138262579481227 1158750112707393869221841)
                  ·
                    refine ⟨869062584530545401916381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1158750112707393869221841 869062584530545401916381)
                    ·
                      refine ⟨325898469198954525718643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 869062584530545401916381 325898469198954525718643)
                      ·
                        rfl

theorem cell23_634685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_634685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634685 prefixEnd_634685 := by exact prefixLift 634685
  have htrace : WordTrace (prefixWord ++ tailWord_634685) baseStart_634685 baseEnd_634685 := by
    simpa [prefixWord, tailWord_634685, baseEnd_634685] using wordTrace_append hprefix tailTrace_634685
  have hstable : (prefixWord ++ tailWord_634685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634685).length < 2 ^ (prefixWord ++ tailWord_634685).sum := by decide
  have hdescent : baseEnd_634685 < baseStart_634685 := by decide
  rcases family_descends (prefixWord ++ tailWord_634685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634698 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 6, 1, 3]
def baseStart_634698 : Nat := 118140960795 + 634698 * 2 ^ 59
def prefixEnd_634698 : Nat := 4983230072969 + 3 ^ 40 * 634698 * 2
def baseEnd_634698 : Nat := 325905144447462974856083

theorem tailTrace_634698 : CollatzResearch.WordTrace tailWord_634698 prefixEnd_634698 325905144447462974856083 := by
  unfold tailWord_634698
  simp only [CollatzResearch.WordTrace]
  refine ⟨5787334463651254658380187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15432891903070012422347165 5787334463651254658380187)
  ·
    refine ⟨8681001695476881987570281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5787334463651254658380187 8681001695476881987570281)
    ·
      refine ⟨6510751271607661490677711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8681001695476881987570281 6510751271607661490677711)
      ·
        refine ⟨9766126907411492236016567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6510751271607661490677711 9766126907411492236016567)
        ·
          refine ⟨14649190361117238354024851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9766126907411492236016567 14649190361117238354024851)
          ·
            refine ⟨21973785541675857531037277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14649190361117238354024851 21973785541675857531037277)
            ·
              refine ⟨8240169578128446574138979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21973785541675857531037277 8240169578128446574138979)
              ·
                refine ⟨12360254367192669861208469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8240169578128446574138979 12360254367192669861208469)
                ·
                  refine ⟨579386923462156399744147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12360254367192669861208469 579386923462156399744147)
                  ·
                    refine ⟨869080385193234599616221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 579386923462156399744147 869080385193234599616221)
                    ·
                      refine ⟨325905144447462974856083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 869080385193234599616221 325905144447462974856083)
                      ·
                        rfl

theorem cell23_634698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_634698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634698 prefixEnd_634698 := by exact prefixLift 634698
  have htrace : WordTrace (prefixWord ++ tailWord_634698) baseStart_634698 baseEnd_634698 := by
    simpa [prefixWord, tailWord_634698, baseEnd_634698] using wordTrace_append hprefix tailTrace_634698
  have hstable : (prefixWord ++ tailWord_634698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634698).length < 2 ^ (prefixWord ++ tailWord_634698).sum := by decide
  have hdescent : baseEnd_634698 < baseStart_634698 := by decide
  rcases family_descends (prefixWord ++ tailWord_634698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634716 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_634716 : Nat := 118140960795 + 634716 * 2 ^ 59
def prefixEnd_634716 : Nat := 4983230072969 + 3 ^ 40 * 634716 * 2
def baseEnd_634716 : Nat := 325914387099243904431001

theorem tailTrace_634716 : CollatzResearch.WordTrace tailWord_634716 prefixEnd_634716 325914387099243904431001 := by
  unfold tailWord_634716
  simp only [CollatzResearch.WordTrace]
  refine ⟨11574997184269903853838001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15433329579026538471784001 11574997184269903853838001)
  ·
    refine ⟨8681247888202427890378501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11574997184269903853838001 8681247888202427890378501)
    ·
      refine ⟨1627733979037955229445969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8681247888202427890378501 1627733979037955229445969)
      ·
        refine ⟨1220800484278466422084477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1627733979037955229445969 1220800484278466422084477)
        ·
          refine ⟨457800181604424908281679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1220800484278466422084477 457800181604424908281679)
          ·
            refine ⟨686700272406637362422519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457800181604424908281679 686700272406637362422519)
            ·
              refine ⟨1030050408609956043633779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686700272406637362422519 1030050408609956043633779)
              ·
                refine ⟨1545075612914934065450669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030050408609956043633779 1545075612914934065450669)
                ·
                  refine ⟨579403354843100274544001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1545075612914934065450669 579403354843100274544001)
                  ·
                    refine ⟨434552516132325205908001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 579403354843100274544001 434552516132325205908001)
                    ·
                      refine ⟨325914387099243904431001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434552516132325205908001 325914387099243904431001)
                      ·
                        rfl

theorem cell23_634716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_634716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634716 prefixEnd_634716 := by exact prefixLift 634716
  have htrace : WordTrace (prefixWord ++ tailWord_634716) baseStart_634716 baseEnd_634716 := by
    simpa [prefixWord, tailWord_634716, baseEnd_634716] using wordTrace_append hprefix tailTrace_634716
  have hstable : (prefixWord ++ tailWord_634716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634716).length < 2 ^ (prefixWord ++ tailWord_634716).sum := by decide
  have hdescent : baseEnd_634716 < baseStart_634716 := by decide
  rcases family_descends (prefixWord ++ tailWord_634716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634721 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_634721 : Nat := 118140960795 + 634721 * 2 ^ 59
def prefixEnd_634721 : Nat := 4983230072969 + 3 ^ 40 * 634721 * 2
def baseEnd_634721 : Nat := 325916954502516384868477

theorem tailTrace_634721 : CollatzResearch.WordTrace tailWord_634721 prefixEnd_634721 325916954502516384868477 := by
  unfold tailWord_634721
  simp only [CollatzResearch.WordTrace]
  refine ⟨23150176733521693561608017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15433451155681129041072011 23150176733521693561608017)
  ·
    refine ⟨17362632550141270171206013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23150176733521693561608017 17362632550141270171206013)
    ·
      refine ⟨6510987206302976314202255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17362632550141270171206013 6510987206302976314202255)
      ·
        refine ⟨9766480809454464471303383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6510987206302976314202255 9766480809454464471303383)
        ·
          refine ⟨14649721214181696706955075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9766480809454464471303383 14649721214181696706955075)
          ·
            refine ⟨21974581821272545060432613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14649721214181696706955075 21974581821272545060432613)
            ·
              refine ⟨4120234091488602198831115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21974581821272545060432613 4120234091488602198831115)
              ·
                refine ⟨6180351137232903298246673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120234091488602198831115 6180351137232903298246673)
                ·
                  refine ⟨4635263352924677473685005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6180351137232903298246673 4635263352924677473685005)
                  ·
                    refine ⟨1738223757346754052631877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4635263352924677473685005 1738223757346754052631877)
                    ·
                      refine ⟨325916954502516384868477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1738223757346754052631877 325916954502516384868477)
                      ·
                        rfl

theorem cell23_634721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_634721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634721 prefixEnd_634721 := by exact prefixLift 634721
  have htrace : WordTrace (prefixWord ++ tailWord_634721) baseStart_634721 baseEnd_634721 := by
    simpa [prefixWord, tailWord_634721, baseEnd_634721] using wordTrace_append hprefix tailTrace_634721
  have hstable : (prefixWord ++ tailWord_634721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634721).length < 2 ^ (prefixWord ++ tailWord_634721).sum := by decide
  have hdescent : baseEnd_634721 < baseStart_634721 := by decide
  rcases family_descends (prefixWord ++ tailWord_634721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634732 : List Nat := [2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 3]
def baseStart_634732 : Nat := 118140960795 + 634732 * 2 ^ 59
def prefixEnd_634732 : Nat := 4983230072969 + 3 ^ 40 * 634732 * 2
def baseEnd_634732 : Nat := 325922602789715841830927

theorem tailTrace_634732 : CollatzResearch.WordTrace tailWord_634732 prefixEnd_634732 325922602789715841830927 := by
  unfold tailWord_634732
  simp only [CollatzResearch.WordTrace]
  refine ⟨11575288968240921220129225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15433718624321228293505633 11575288968240921220129225)
  ·
    refine ⟨8681466726180690915096919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11575288968240921220129225 8681466726180690915096919)
    ·
      refine ⟨13022200089271036372645379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8681466726180690915096919 13022200089271036372645379)
      ·
        refine ⟨19533300133906554558968069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13022200089271036372645379 19533300133906554558968069)
        ·
          refine ⟨3662493775107478979806513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19533300133906554558968069 3662493775107478979806513)
          ·
            refine ⟨2746870331330609234854885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3662493775107478979806513 2746870331330609234854885)
            ·
              refine ⟨515038187124489231535291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2746870331330609234854885 515038187124489231535291)
              ·
                refine ⟨772557280686733847302937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515038187124489231535291 772557280686733847302937)
                ·
                  refine ⟨579417960515050385477203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 772557280686733847302937 579417960515050385477203)
                  ·
                    refine ⟨869126940772575578215805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 579417960515050385477203 869126940772575578215805)
                    ·
                      refine ⟨325922602789715841830927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 869126940772575578215805 325922602789715841830927)
                      ·
                        rfl

theorem cell23_634732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 3].length) (baseStart_634732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634732 prefixEnd_634732 := by exact prefixLift 634732
  have htrace : WordTrace (prefixWord ++ tailWord_634732) baseStart_634732 baseEnd_634732 := by
    simpa [prefixWord, tailWord_634732, baseEnd_634732] using wordTrace_append hprefix tailTrace_634732
  have hstable : (prefixWord ++ tailWord_634732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634732).length < 2 ^ (prefixWord ++ tailWord_634732).sum := by decide
  have hdescent : baseEnd_634732 < baseStart_634732 := by decide
  rcases family_descends (prefixWord ++ tailWord_634732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634751 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 4]
def baseStart_634751 : Nat := 118140960795 + 634751 * 2 ^ 59
def prefixEnd_634751 : Nat := 4983230072969 + 3 ^ 40 * 634751 * 2
def baseEnd_634751 : Nat := 325932358922151267493339

theorem tailTrace_634751 : CollatzResearch.WordTrace tailWord_634751 prefixEnd_634751 325932358922151267493339 := by
  unfold tailWord_634751
  simp only [CollatzResearch.WordTrace]
  refine ⟨23151270923413008685200107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15434180615608672456800071 23151270923413008685200107)
  ·
    refine ⟨34726906385119513027800161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23151270923413008685200107 34726906385119513027800161)
    ·
      refine ⟨26045179788839634770850121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34726906385119513027800161 26045179788839634770850121)
      ·
        refine ⟨19533884841629726078137591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26045179788839634770850121 19533884841629726078137591)
        ·
          refine ⟨29300827262444589117206387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19533884841629726078137591 29300827262444589117206387)
          ·
            refine ⟨43951240893666883675809581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29300827262444589117206387 43951240893666883675809581)
            ·
              refine ⟨16481715335125081378428593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43951240893666883675809581 16481715335125081378428593)
              ·
                refine ⟨12361286501343811033821445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16481715335125081378428593 12361286501343811033821445)
                ·
                  refine ⟨2317741219001964568841521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12361286501343811033821445 2317741219001964568841521)
                  ·
                    refine ⟨1738305914251473426631141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2317741219001964568841521 1738305914251473426631141)
                    ·
                      refine ⟨325932358922151267493339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1738305914251473426631141 325932358922151267493339)
                      ·
                        rfl

theorem cell23_634751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_634751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634751 prefixEnd_634751 := by exact prefixLift 634751
  have htrace : WordTrace (prefixWord ++ tailWord_634751) baseStart_634751 baseEnd_634751 := by
    simpa [prefixWord, tailWord_634751, baseEnd_634751] using wordTrace_append hprefix tailTrace_634751
  have hstable : (prefixWord ++ tailWord_634751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634751).length < 2 ^ (prefixWord ++ tailWord_634751).sum := by decide
  have hdescent : baseEnd_634751 < baseStart_634751 := by decide
  rcases family_descends (prefixWord ++ tailWord_634751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634755 : List Nat := [1, 1, 1, 3, 4, 3, 1, 2, 1, 4, 2]
def baseStart_634755 : Nat := 118140960795 + 634755 * 2 ^ 59
def prefixEnd_634755 : Nat := 4983230072969 + 3 ^ 40 * 634755 * 2
def baseEnd_634755 : Nat := 325934412844769251843321

theorem tailTrace_634755 : CollatzResearch.WordTrace tailWord_634755 prefixEnd_634755 325934412844769251843321 := by
  unfold tailWord_634755
  simp only [CollatzResearch.WordTrace]
  refine ⟨23151416815398517368345719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15434277876932344912230479 23151416815398517368345719)
  ·
    refine ⟨34727125223097776052518579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23151416815398517368345719 34727125223097776052518579)
    ·
      refine ⟨52090687834646664078777869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34727125223097776052518579 52090687834646664078777869)
      ·
        refine ⟨19534007937992499029541701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52090687834646664078777869 19534007937992499029541701)
        ·
          refine ⟨3662626488373593568039069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19534007937992499029541701 3662626488373593568039069)
          ·
            refine ⟨1373484933140097588014651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3662626488373593568039069 1373484933140097588014651)
            ·
              refine ⟨2060227399710146382021977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373484933140097588014651 2060227399710146382021977)
              ·
                refine ⟨1545170549782609786516483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2060227399710146382021977 1545170549782609786516483)
                ·
                  refine ⟨2317755824673914679774725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545170549782609786516483 2317755824673914679774725)
                  ·
                    refine ⟨434579217126359002457761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2317755824673914679774725 434579217126359002457761)
                    ·
                      refine ⟨325934412844769251843321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434579217126359002457761 325934412844769251843321)
                      ·
                        rfl

theorem cell23_634755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 4, 2].length) (baseStart_634755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634755 prefixEnd_634755 := by exact prefixLift 634755
  have htrace : WordTrace (prefixWord ++ tailWord_634755) baseStart_634755 baseEnd_634755 := by
    simpa [prefixWord, tailWord_634755, baseEnd_634755] using wordTrace_append hprefix tailTrace_634755
  have hstable : (prefixWord ++ tailWord_634755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634755).length < 2 ^ (prefixWord ++ tailWord_634755).sum := by decide
  have hdescent : baseEnd_634755 < baseStart_634755 := by decide
  rcases family_descends (prefixWord ++ tailWord_634755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634759 : List Nat := [1, 1, 4, 2, 4, 1, 3, 1, 1, 3, 2]
def baseStart_634759 : Nat := 118140960795 + 634759 * 2 ^ 59
def prefixEnd_634759 : Nat := 4983230072969 + 3 ^ 40 * 634759 * 2
def baseEnd_634759 : Nat := 325936466767387236193303

theorem tailTrace_634759 : CollatzResearch.WordTrace tailWord_634759 prefixEnd_634759 325936466767387236193303 := by
  unfold tailWord_634759
  simp only [CollatzResearch.WordTrace]
  refine ⟨23151562707384026051491331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15434375138256017367660887 23151562707384026051491331)
  ·
    refine ⟨34727344061076039077236997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23151562707384026051491331 34727344061076039077236997)
    ·
      refine ⟨6511377011451757326981937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34727344061076039077236997 6511377011451757326981937)
      ·
        refine ⟨4883532758588817995236453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6511377011451757326981937 4883532758588817995236453)
        ·
          refine ⟨915662392235403374106835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4883532758588817995236453 915662392235403374106835)
          ·
            refine ⟨1373493588353105061160253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915662392235403374106835 1373493588353105061160253)
            ·
              refine ⟨515060095632414397935095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1373493588353105061160253 515060095632414397935095)
              ·
                refine ⟨772590143448621596902643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515060095632414397935095 772590143448621596902643)
                ·
                  refine ⟨1158885215172932395353965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772590143448621596902643 1158885215172932395353965)
                  ·
                    refine ⟨434581955689849648257737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1158885215172932395353965 434581955689849648257737)
                    ·
                      refine ⟨325936466767387236193303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434581955689849648257737 325936466767387236193303)
                      ·
                        rfl

theorem cell23_634759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_634759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634759 prefixEnd_634759 := by exact prefixLift 634759
  have htrace : WordTrace (prefixWord ++ tailWord_634759) baseStart_634759 baseEnd_634759 := by
    simpa [prefixWord, tailWord_634759, baseEnd_634759] using wordTrace_append hprefix tailTrace_634759
  have hstable : (prefixWord ++ tailWord_634759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634759).length < 2 ^ (prefixWord ++ tailWord_634759).sum := by decide
  have hdescent : baseEnd_634759 < baseStart_634759 := by decide
  rcases family_descends (prefixWord ++ tailWord_634759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634782 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_634782 : Nat := 118140960795 + 634782 * 2 ^ 59
def prefixEnd_634782 : Nat := 4983230072969 + 3 ^ 40 * 634782 * 2
def baseEnd_634782 : Nat := 108649425607480215401899

theorem tailTrace_634782 : CollatzResearch.WordTrace tailWord_634782 prefixEnd_634782 108649425607480215401899 := by
  unfold tailWord_634782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2894050198287587622447325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15434934390867133986385733 2894050198287587622447325)
  ·
    refine ⟨1085268824357845358417747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2894050198287587622447325 1085268824357845358417747)
    ·
      refine ⟨1627903236536768037626621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1085268824357845358417747 1627903236536768037626621)
      ·
        refine ⟨610463713701288014109983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1627903236536768037626621 610463713701288014109983)
        ·
          refine ⟨915695570551932021164975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610463713701288014109983 915695570551932021164975)
          ·
            refine ⟨1373543355827898031747463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915695570551932021164975 1373543355827898031747463)
            ·
              refine ⟨2060315033741847047621195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373543355827898031747463 2060315033741847047621195)
              ·
                refine ⟨3090472550612770571431793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060315033741847047621195 3090472550612770571431793)
                ·
                  refine ⟨2317854412959577928573845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3090472550612770571431793 2317854412959577928573845)
                  ·
                    refine ⟨108649425607480215401899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2317854412959577928573845 108649425607480215401899)
                    ·
                      rfl

theorem cell23_634782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_634782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634782 prefixEnd_634782 := by exact prefixLift 634782
  have htrace : WordTrace (prefixWord ++ tailWord_634782) baseStart_634782 baseEnd_634782 := by
    simpa [prefixWord, tailWord_634782, baseEnd_634782] using wordTrace_append hprefix tailTrace_634782
  have hstable : (prefixWord ++ tailWord_634782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634782).length < 2 ^ (prefixWord ++ tailWord_634782).sum := by decide
  have hdescent : baseEnd_634782 < baseStart_634782 := by decide
  rcases family_descends (prefixWord ++ tailWord_634782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634785 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_634785 : Nat := 118140960795 + 634785 * 2 ^ 59
def prefixEnd_634785 : Nat := 4983230072969 + 3 ^ 40 * 634785 * 2
def baseEnd_634785 : Nat := 325949817264404134468183

theorem tailTrace_634785 : CollatzResearch.WordTrace tailWord_634785 prefixEnd_634785 325949817264404134468183 := by
  unfold tailWord_634785
  simp only [CollatzResearch.WordTrace]
  refine ⟨23152511005289832491937809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15435007336859888327958539 23152511005289832491937809)
  ·
    refine ⟨17364383253967374368953357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23152511005289832491937809 17364383253967374368953357)
    ·
      refine ⟨6511643720237765388357509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17364383253967374368953357 6511643720237765388357509)
      ·
        refine ⟨1220933197544581010317033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6511643720237765388357509 1220933197544581010317033)
        ·
          refine ⟨915699898158435757737775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1220933197544581010317033 915699898158435757737775)
          ·
            refine ⟨1373549847237653636606663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915699898158435757737775 1373549847237653636606663)
            ·
              refine ⟨2060324770856480454909995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373549847237653636606663 2060324770856480454909995)
              ·
                refine ⟨3090487156284720682364993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060324770856480454909995 3090487156284720682364993)
                ·
                  refine ⟨2317865367213540511773745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3090487156284720682364993 2317865367213540511773745)
                  ·
                    refine ⟨1738399025410155383830309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2317865367213540511773745 1738399025410155383830309)
                    ·
                      refine ⟨325949817264404134468183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1738399025410155383830309 325949817264404134468183)
                      ·
                        rfl

theorem cell23_634785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_634785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634785 prefixEnd_634785 := by exact prefixLift 634785
  have htrace : WordTrace (prefixWord ++ tailWord_634785) baseStart_634785 baseEnd_634785 := by
    simpa [prefixWord, tailWord_634785, baseEnd_634785] using wordTrace_append hprefix tailTrace_634785
  have hstable : (prefixWord ++ tailWord_634785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634785).length < 2 ^ (prefixWord ++ tailWord_634785).sum := by decide
  have hdescent : baseEnd_634785 < baseStart_634785 := by decide
  rcases family_descends (prefixWord ++ tailWord_634785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634788 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_634788 : Nat := 118140960795 + 634788 * 2 ^ 59
def prefixEnd_634788 : Nat := 4983230072969 + 3 ^ 40 * 634788 * 2
def baseEnd_634788 : Nat := 325951357706367622730669

theorem tailTrace_634788 : CollatzResearch.WordTrace tailWord_634788 prefixEnd_634788 325951357706367622730669 := by
  unfold tailWord_634788
  simp only [CollatzResearch.WordTrace]
  refine ⟨11576310212139482002148509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15435080282852642669531345 11576310212139482002148509)
  ·
    refine ⟨4341116329552305750805691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11576310212139482002148509 4341116329552305750805691)
    ·
      refine ⟨6511674494328458626208537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4341116329552305750805691 6511674494328458626208537)
      ·
        refine ⟨4883755870746343969656403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6511674494328458626208537 4883755870746343969656403)
        ·
          refine ⟨7325633806119515954484605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4883755870746343969656403 7325633806119515954484605)
          ·
            refine ⟨2747112677294818482931727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7325633806119515954484605 2747112677294818482931727)
            ·
              refine ⟨4120669015942227724397591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2747112677294818482931727 4120669015942227724397591)
              ·
                refine ⟨6181003523913341586596387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4120669015942227724397591 6181003523913341586596387)
                ·
                  refine ⟨9271505285870012379894581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6181003523913341586596387 9271505285870012379894581)
                  ·
                    refine ⟨869203620550313660615117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9271505285870012379894581 869203620550313660615117)
                    ·
                      refine ⟨325951357706367622730669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 869203620550313660615117 325951357706367622730669)
                      ·
                        rfl

theorem cell23_634788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_634788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634788 prefixEnd_634788 := by exact prefixLift 634788
  have htrace : WordTrace (prefixWord ++ tailWord_634788) baseStart_634788 baseEnd_634788 := by
    simpa [prefixWord, tailWord_634788, baseEnd_634788] using wordTrace_append hprefix tailTrace_634788
  have hstable : (prefixWord ++ tailWord_634788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634788).length < 2 ^ (prefixWord ++ tailWord_634788).sum := by decide
  have hdescent : baseEnd_634788 < baseStart_634788 := by decide
  rcases family_descends (prefixWord ++ tailWord_634788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634858 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_634858 : Nat := 118140960795 + 634858 * 2 ^ 59
def prefixEnd_634858 : Nat := 4983230072969 + 3 ^ 40 * 634858 * 2
def baseEnd_634858 : Nat := 325987301352182348855347

theorem tailTrace_634858 : CollatzResearch.WordTrace tailWord_634858 prefixEnd_634858 325987301352182348855347 := by
  unfold tailWord_634858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5788793383506341489836307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15436782356016910639563485 5788793383506341489836307)
  ·
    refine ⟨8683190075259512234754461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5788793383506341489836307 8683190075259512234754461)
    ·
      refine ⟨3256196278222317088032923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8683190075259512234754461 3256196278222317088032923)
      ·
        refine ⟨4884294417333475632049385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3256196278222317088032923 4884294417333475632049385)
        ·
          refine ⟨3663220813000106724037039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4884294417333475632049385 3663220813000106724037039)
          ·
            refine ⟨5494831219500160086055559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3663220813000106724037039 5494831219500160086055559)
            ·
              refine ⟨8242246829250240129083339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5494831219500160086055559 8242246829250240129083339)
              ·
                refine ⟨12363370243875360193625009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8242246829250240129083339 12363370243875360193625009)
                ·
                  refine ⟨9272527682906520145218757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12363370243875360193625009 9272527682906520145218757)
                  ·
                    refine ⟨1738598940544972527228517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9272527682906520145218757 1738598940544972527228517)
                    ·
                      refine ⟨325987301352182348855347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1738598940544972527228517 325987301352182348855347)
                      ·
                        rfl

theorem cell23_634858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_634858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634858 prefixEnd_634858 := by exact prefixLift 634858
  have htrace : WordTrace (prefixWord ++ tailWord_634858) baseStart_634858 baseEnd_634858 := by
    simpa [prefixWord, tailWord_634858, baseEnd_634858] using wordTrace_append hprefix tailTrace_634858
  have hstable : (prefixWord ++ tailWord_634858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634858).length < 2 ^ (prefixWord ++ tailWord_634858).sum := by decide
  have hdescent : baseEnd_634858 < baseStart_634858 := by decide
  rcases family_descends (prefixWord ++ tailWord_634858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634872 : List Nat := [2, 1, 2, 1, 1, 3, 5, 3, 1, 4]
def baseStart_634872 : Nat := 118140960795 + 634872 * 2 ^ 59
def prefixEnd_634872 : Nat := 4983230072969 + 3 ^ 40 * 634872 * 2
def baseEnd_634872 : Nat := 108664830027115098026761

theorem tailTrace_634872 : CollatzResearch.WordTrace tailWord_634872 prefixEnd_634872 108664830027115098026761 := by
  unfold tailWord_634872
  simp only [CollatzResearch.WordTrace]
  refine ⟨11577842077987323175177435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15437122770649764233569913 11577842077987323175177435)
  ·
    refine ⟨17366763116980984762766153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11577842077987323175177435 17366763116980984762766153)
    ·
      refine ⟨13025072337735738572074615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17366763116980984762766153 13025072337735738572074615)
      ·
        refine ⟨19537608506603607858111923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13025072337735738572074615 19537608506603607858111923)
        ·
          refine ⟨29306412759905411787167885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19537608506603607858111923 29306412759905411787167885)
          ·
            refine ⟨10989904784964529420187957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29306412759905411787167885 10989904784964529420187957)
            ·
              refine ⟨1030303573590424633142621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10989904784964529420187957 1030303573590424633142621)
              ·
                refine ⟨386363840096409237428483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1030303573590424633142621 386363840096409237428483)
                ·
                  refine ⟨579545760144613856142725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386363840096409237428483 579545760144613856142725)
                  ·
                    refine ⟨108664830027115098026761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 579545760144613856142725 108664830027115098026761)
                    ·
                      rfl

theorem cell23_634872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_634872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634872 prefixEnd_634872 := by exact prefixLift 634872
  have htrace : WordTrace (prefixWord ++ tailWord_634872) baseStart_634872 baseEnd_634872 := by
    simpa [prefixWord, tailWord_634872, baseEnd_634872] using wordTrace_append hprefix tailTrace_634872
  have hstable : (prefixWord ++ tailWord_634872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634872).length < 2 ^ (prefixWord ++ tailWord_634872).sum := by decide
  have hdescent : baseEnd_634872 < baseStart_634872 := by decide
  rcases family_descends (prefixWord ++ tailWord_634872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634886 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_634886 : Nat := 118140960795 + 634886 * 2 ^ 59
def prefixEnd_634886 : Nat := 4983230072969 + 3 ^ 40 * 634886 * 2
def baseEnd_634886 : Nat := 326001678810508239305219

theorem tailTrace_634886 : CollatzResearch.WordTrace tailWord_634886 prefixEnd_634886 326001678810508239305219 := by
  unfold tailWord_634886
  simp only [CollatzResearch.WordTrace]
  refine ⟨723631086810122710667641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15437463185282617827576341 723631086810122710667641)
  ·
    refine ⟨542723315107592033000731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 723631086810122710667641 542723315107592033000731)
    ·
      refine ⟨814084972661388049501097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 542723315107592033000731 814084972661388049501097)
      ·
        refine ⟨610563729496041037125823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 814084972661388049501097 610563729496041037125823)
        ·
          refine ⟨915845594244061555688735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610563729496041037125823 915845594244061555688735)
          ·
            refine ⟨1373768391366092333533103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915845594244061555688735 1373768391366092333533103)
            ·
              refine ⟨2060652587049138500299655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1373768391366092333533103 2060652587049138500299655)
              ·
                refine ⟨3090978880573707750449483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060652587049138500299655 3090978880573707750449483)
                ·
                  refine ⟨4636468320860561625674225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3090978880573707750449483 4636468320860561625674225)
                  ·
                    refine ⟨3477351240645421219255669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4636468320860561625674225 3477351240645421219255669)
                    ·
                      refine ⟨326001678810508239305219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3477351240645421219255669 326001678810508239305219)
                      ·
                        rfl

theorem cell23_634886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_634886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634886 prefixEnd_634886 := by exact prefixLift 634886
  have htrace : WordTrace (prefixWord ++ tailWord_634886) baseStart_634886 baseEnd_634886 := by
    simpa [prefixWord, tailWord_634886, baseEnd_634886] using wordTrace_append hprefix tailTrace_634886
  have hstable : (prefixWord ++ tailWord_634886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634886).length < 2 ^ (prefixWord ++ tailWord_634886).sum := by decide
  have hdescent : baseEnd_634886 < baseStart_634886 := by decide
  rcases family_descends (prefixWord ++ tailWord_634886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634905 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 6, 3, 2]
def baseStart_634905 : Nat := 118140960795 + 634905 * 2 ^ 59
def prefixEnd_634905 : Nat := 4983230072969 + 3 ^ 40 * 634905 * 2
def baseEnd_634905 : Nat := 326011434942943664967631

theorem tailTrace_634905 : CollatzResearch.WordTrace tailWord_634905 prefixEnd_634905 326011434942943664967631 := by
  unfold tailWord_634905
  simp only [CollatzResearch.WordTrace]
  refine ⟨23156887764855092986306169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15437925176570061990870779 23156887764855092986306169)
  ·
    refine ⟨17367665823641319739729627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23156887764855092986306169 17367665823641319739729627)
    ·
      refine ⟨26051498735461979609594441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17367665823641319739729627 26051498735461979609594441)
      ·
        refine ⟨19538624051596484707195831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26051498735461979609594441 19538624051596484707195831)
        ·
          refine ⟨29307936077394727060793747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19538624051596484707195831 29307936077394727060793747)
          ·
            refine ⟨43961904116092090591190621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29307936077394727060793747 43961904116092090591190621)
            ·
              refine ⟨16485714043534533971696483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43961904116092090591190621 16485714043534533971696483)
              ·
                refine ⟨24728571065301800957544725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16485714043534533971696483 24728571065301800957544725)
                ·
                  refine ⟨1159151768686021919884909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 24728571065301800957544725 1159151768686021919884909)
                  ·
                    refine ⟨434681913257258219956841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1159151768686021919884909 434681913257258219956841)
                    ·
                      refine ⟨326011434942943664967631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434681913257258219956841 326011434942943664967631)
                      ·
                        rfl

theorem cell23_634905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 3, 2].length) (baseStart_634905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634905 prefixEnd_634905 := by exact prefixLift 634905
  have htrace : WordTrace (prefixWord ++ tailWord_634905) baseStart_634905 baseEnd_634905 := by
    simpa [prefixWord, tailWord_634905, baseEnd_634905] using wordTrace_append hprefix tailTrace_634905
  have hstable : (prefixWord ++ tailWord_634905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634905).length < 2 ^ (prefixWord ++ tailWord_634905).sum := by decide
  have hdescent : baseEnd_634905 < baseStart_634905 := by decide
  rcases family_descends (prefixWord ++ tailWord_634905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634928 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 3, 6]
def baseStart_634928 : Nat := 118140960795 + 634928 * 2 ^ 59
def prefixEnd_634928 : Nat := 4983230072969 + 3 ^ 40 * 634928 * 2
def baseEnd_634928 : Nat := 108674414999332358326675

theorem tailTrace_634928 : CollatzResearch.WordTrace tailWord_634928 prefixEnd_634928 108674414999332358326675 := by
  unfold tailWord_634928
  simp only [CollatzResearch.WordTrace]
  refine ⟨11578863321885883957196719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15438484429181178609595625 11578863321885883957196719)
  ·
    refine ⟨17368294982828825935795079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11578863321885883957196719 17368294982828825935795079)
    ·
      refine ⟨26052442474243238903692619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17368294982828825935795079 26052442474243238903692619)
      ·
        refine ⟨39078663711364858355538929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26052442474243238903692619 39078663711364858355538929)
        ·
          refine ⟨29308997783523643766654197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39078663711364858355538929 29308997783523643766654197)
          ·
            refine ⟨2747718542205341603123831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29308997783523643766654197 2747718542205341603123831)
            ·
              refine ⟨4121577813308012404685747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2747718542205341603123831 4121577813308012404685747)
              ·
                refine ⟨6182366719962018607028621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4121577813308012404685747 6182366719962018607028621)
                ·
                  refine ⟨2318387519985756977635733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6182366719962018607028621 2318387519985756977635733)
                  ·
                    refine ⟨108674414999332358326675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2318387519985756977635733 108674414999332358326675)
                    ·
                      rfl

theorem cell23_634928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 3, 6].length) (baseStart_634928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634928 prefixEnd_634928 := by exact prefixLift 634928
  have htrace : WordTrace (prefixWord ++ tailWord_634928) baseStart_634928 baseEnd_634928 := by
    simpa [prefixWord, tailWord_634928, baseEnd_634928] using wordTrace_append hprefix tailTrace_634928
  have hstable : (prefixWord ++ tailWord_634928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634928).length < 2 ^ (prefixWord ++ tailWord_634928).sum := by decide
  have hdescent : baseEnd_634928 < baseStart_634928 := by decide
  rcases family_descends (prefixWord ++ tailWord_634928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634935 : List Nat := [1, 1, 3, 1, 2, 2, 2, 5, 1, 1, 4]
def baseStart_634935 : Nat := 118140960795 + 634935 * 2 ^ 59
def prefixEnd_634935 : Nat := 4983230072969 + 3 ^ 40 * 634935 * 2
def baseEnd_634935 : Nat := 326026839362578547592493

theorem tailTrace_634935 : CollatzResearch.WordTrace tailWord_634935 prefixEnd_634935 326026839362578547592493 := by
  unfold tailWord_634935
  simp only [CollatzResearch.WordTrace]
  refine ⟨23157981954746408109898259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15438654636497605406598839 23157981954746408109898259)
  ·
    refine ⟨34736972932119612164847389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23157981954746408109898259 34736972932119612164847389)
    ·
      refine ⟨13026364849544854561817771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34736972932119612164847389 13026364849544854561817771)
      ·
        refine ⟨19539547274317281842726657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13026364849544854561817771 19539547274317281842726657)
        ·
          refine ⟨14654660455737961382044993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19539547274317281842726657 14654660455737961382044993)
          ·
            refine ⟨10990995341803471036533745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14654660455737961382044993 10990995341803471036533745)
            ·
              refine ⟨8243246506352603277400309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10990995341803471036533745 8243246506352603277400309)
              ·
                refine ⟨772804359970556557256279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8243246506352603277400309 772804359970556557256279)
                ·
                  refine ⟨1159206539955834835884419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772804359970556557256279 1159206539955834835884419)
                  ·
                    refine ⟨1738809809933752253826629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1159206539955834835884419 1738809809933752253826629)
                    ·
                      refine ⟨326026839362578547592493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1738809809933752253826629 326026839362578547592493)
                      ·
                        rfl

theorem cell23_634935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_634935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634935 prefixEnd_634935 := by exact prefixLift 634935
  have htrace : WordTrace (prefixWord ++ tailWord_634935) baseStart_634935 baseEnd_634935 := by
    simpa [prefixWord, tailWord_634935, baseEnd_634935] using wordTrace_append hprefix tailTrace_634935
  have hstable : (prefixWord ++ tailWord_634935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634935).length < 2 ^ (prefixWord ++ tailWord_634935).sum := by decide
  have hdescent : baseEnd_634935 < baseStart_634935 := by decide
  rcases family_descends (prefixWord ++ tailWord_634935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634962 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_634962 : Nat := 118140960795 + 634962 * 2 ^ 59
def prefixEnd_634962 : Nat := 4983230072969 + 3 ^ 40 * 634962 * 2
def baseEnd_634962 : Nat := 108680234446749980651623

theorem tailTrace_634962 : CollatzResearch.WordTrace tailWord_634962 prefixEnd_634962 108680234446749980651623 := by
  unfold tailWord_634962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5789741681412147930282785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15439311150432394480754093 5789741681412147930282785)
  ·
    refine ⟨4342306261059110947712089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5789741681412147930282785 4342306261059110947712089)
    ·
      refine ⟨3256729695794333210784067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4342306261059110947712089 3256729695794333210784067)
      ·
        refine ⟨4885094543691499816176101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3256729695794333210784067 4885094543691499816176101)
        ·
          refine ⟨915955226942156215533019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4885094543691499816176101 915955226942156215533019)
          ·
            refine ⟨1373932840413234323299529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915955226942156215533019 1373932840413234323299529)
            ·
              refine ⟨1030449630309925742474647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373932840413234323299529 1030449630309925742474647)
              ·
                refine ⟨1545674445464888613711971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030449630309925742474647 1545674445464888613711971)
                ·
                  refine ⟨2318511668197332920567957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545674445464888613711971 2318511668197332920567957)
                  ·
                    refine ⟨108680234446749980651623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2318511668197332920567957 108680234446749980651623)
                    ·
                      rfl

theorem cell23_634962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_634962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634962 prefixEnd_634962 := by exact prefixLift 634962
  have htrace : WordTrace (prefixWord ++ tailWord_634962) baseStart_634962 baseEnd_634962 := by
    simpa [prefixWord, tailWord_634962, baseEnd_634962] using wordTrace_append hprefix tailTrace_634962
  have hstable : (prefixWord ++ tailWord_634962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634962).length < 2 ^ (prefixWord ++ tailWord_634962).sum := by decide
  have hdescent : baseEnd_634962 < baseStart_634962 := by decide
  rcases family_descends (prefixWord ++ tailWord_634962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634965 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_634965 : Nat := 118140960795 + 634965 * 2 ^ 59
def prefixEnd_634965 : Nat := 4983230072969 + 3 ^ 40 * 634965 * 2
def baseEnd_634965 : Nat := 326042243782213430217355

theorem tailTrace_634965 : CollatzResearch.WordTrace tailWord_634965 prefixEnd_634965 326042243782213430217355 := by
  unfold tailWord_634965
  simp only [CollatzResearch.WordTrace]
  refine ⟨23159076144637723233490349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15439384096425148822326899 23159076144637723233490349)
  ·
    refine ⟨8684653554239146212558881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23159076144637723233490349 8684653554239146212558881)
    ·
      refine ⟨6513490165679359659419161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8684653554239146212558881 6513490165679359659419161)
      ·
        refine ⟨4885117624259519744564371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6513490165679359659419161 4885117624259519744564371)
        ·
          refine ⟨7327676436389279616846557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4885117624259519744564371 7327676436389279616846557)
          ·
            refine ⟨2747878663645979856317459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7327676436389279616846557 2747878663645979856317459)
            ·
              refine ⟨4121817995468969784476189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2747878663645979856317459 4121817995468969784476189)
              ·
                refine ⟨1545681748300863669178571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4121817995468969784476189 1545681748300863669178571)
                ·
                  refine ⟨2318522622451295503767857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545681748300863669178571 2318522622451295503767857)
                  ·
                    refine ⟨1738891966838471627825893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2318522622451295503767857 1738891966838471627825893)
                    ·
                      refine ⟨326042243782213430217355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1738891966838471627825893 326042243782213430217355)
                      ·
                        rfl

theorem cell23_634965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_634965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634965 prefixEnd_634965 := by exact prefixLift 634965
  have htrace : WordTrace (prefixWord ++ tailWord_634965) baseStart_634965 baseEnd_634965 := by
    simpa [prefixWord, tailWord_634965, baseEnd_634965] using wordTrace_append hprefix tailTrace_634965
  have hstable : (prefixWord ++ tailWord_634965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634965).length < 2 ^ (prefixWord ++ tailWord_634965).sum := by decide
  have hdescent : baseEnd_634965 < baseStart_634965 := by decide
  rcases family_descends (prefixWord ++ tailWord_634965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634972 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_634972 : Nat := 118140960795 + 634972 * 2 ^ 59
def prefixEnd_634972 : Nat := 4983230072969 + 3 ^ 40 * 634972 * 2
def baseEnd_634972 : Nat := 326045838146794902829823

theorem tailTrace_634972 : CollatzResearch.WordTrace tailWord_634972 prefixEnd_634972 326045838146794902829823 := by
  unfold tailWord_634972
  simp only [CollatzResearch.WordTrace]
  refine ⟨11579665727806181714497585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15439554303741575619330113 11579665727806181714497585)
  ·
    refine ⟨8684749295854636285873189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11579665727806181714497585 8684749295854636285873189)
    ·
      refine ⟨1628390492972744303601223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8684749295854636285873189 1628390492972744303601223)
      ·
        refine ⟨2442585739459116455401835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628390492972744303601223 2442585739459116455401835)
        ·
          refine ⟨3663878609188674683102753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2442585739459116455401835 3663878609188674683102753)
          ·
            refine ⟨2747908956891506012327065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3663878609188674683102753 2747908956891506012327065)
            ·
              refine ⟨2060931717668629509245299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2747908956891506012327065 2060931717668629509245299)
              ·
                refine ⟨3091397576502944263867949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2060931717668629509245299 3091397576502944263867949)
                ·
                  refine ⟨1159274091188604098950481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3091397576502944263867949 1159274091188604098950481)
                  ·
                    refine ⟨869455568391453074212861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1159274091188604098950481 869455568391453074212861)
                    ·
                      refine ⟨326045838146794902829823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 869455568391453074212861 326045838146794902829823)
                      ·
                        rfl

theorem cell23_634972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_634972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634972 prefixEnd_634972 := by exact prefixLift 634972
  have htrace : WordTrace (prefixWord ++ tailWord_634972) baseStart_634972 baseEnd_634972 := by
    simpa [prefixWord, tailWord_634972, baseEnd_634972] using wordTrace_append hprefix tailTrace_634972
  have hstable : (prefixWord ++ tailWord_634972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634972).length < 2 ^ (prefixWord ++ tailWord_634972).sum := by decide
  have hdescent : baseEnd_634972 < baseStart_634972 := by decide
  rcases family_descends (prefixWord ++ tailWord_634972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634985 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 1, 3, 3]
def baseStart_634985 : Nat := 118140960795 + 634985 * 2 ^ 59
def prefixEnd_634985 : Nat := 4983230072969 + 3 ^ 40 * 634985 * 2
def baseEnd_634985 : Nat := 326052513395303351967263

theorem tailTrace_634985 : CollatzResearch.WordTrace tailWord_634985 prefixEnd_634985 326052513395303351967263 := by
  unfold tailWord_634985
  simp only [CollatzResearch.WordTrace]
  refine ⟨23159805604565266649218409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15439870403043511099478939 23159805604565266649218409)
  ·
    refine ⟨17369854203423949986913807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23159805604565266649218409 17369854203423949986913807)
    ·
      refine ⟨26054781305135924980370711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17369854203423949986913807 26054781305135924980370711)
      ·
        refine ⟨39082171957703887470556067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26054781305135924980370711 39082171957703887470556067)
        ·
          refine ⟨58623257936555831205834101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39082171957703887470556067 58623257936555831205834101)
          ·
            refine ⟨5495930431552109175546947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58623257936555831205834101 5495930431552109175546947)
            ·
              refine ⟨8243895647328163763320421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5495930431552109175546947 8243895647328163763320421)
              ·
                refine ⟨1545730433874030705622579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8243895647328163763320421 1545730433874030705622579)
                ·
                  refine ⟨2318595650811046058433869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1545730433874030705622579 2318595650811046058433869)
                  ·
                    refine ⟨869473369054142271912701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2318595650811046058433869 869473369054142271912701)
                    ·
                      refine ⟨326052513395303351967263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 869473369054142271912701 326052513395303351967263)
                      ·
                        rfl

theorem cell23_634985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 3, 3].length) (baseStart_634985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634985 prefixEnd_634985 := by exact prefixLift 634985
  have htrace : WordTrace (prefixWord ++ tailWord_634985) baseStart_634985 baseEnd_634985 := by
    simpa [prefixWord, tailWord_634985, baseEnd_634985] using wordTrace_append hprefix tailTrace_634985
  have hstable : (prefixWord ++ tailWord_634985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634985).length < 2 ^ (prefixWord ++ tailWord_634985).sum := by decide
  have hdescent : baseEnd_634985 < baseStart_634985 := by decide
  rcases family_descends (prefixWord ++ tailWord_634985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_634986 : List Nat := [3, 1, 3, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_634986 : Nat := 118140960795 + 634986 * 2 ^ 59
def prefixEnd_634986 : Nat := 4983230072969 + 3 ^ 40 * 634986 * 2
def baseEnd_634986 : Nat := 326053026875957848054759

theorem tailTrace_634986 : CollatzResearch.WordTrace tailWord_634986 prefixEnd_634986 326053026875957848054759 := by
  unfold tailWord_634986
  simp only [CollatzResearch.WordTrace]
  refine ⟨5789960519390410955001203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15439894718374429213336541 5789960519390410955001203)
  ·
    refine ⟨8684940779085616432501805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5789960519390410955001203 8684940779085616432501805)
    ·
      refine ⟨3256852792157106162188177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8684940779085616432501805 3256852792157106162188177)
      ·
        refine ⟨2442639594117829621641133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3256852792157106162188177 2442639594117829621641133)
        ·
          refine ⟨915989847794186108115425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2442639594117829621641133 915989847794186108115425)
          ·
            refine ⟨686992385845639581086569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 915989847794186108115425 686992385845639581086569)
            ·
              refine ⟨515244289384229685814927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686992385845639581086569 515244289384229685814927)
              ·
                refine ⟨772866434076344528722391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515244289384229685814927 772866434076344528722391)
                ·
                  refine ⟨1159299651114516793083587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772866434076344528722391 1159299651114516793083587)
                  ·
                    refine ⟨1738949476671775189625381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1159299651114516793083587 1738949476671775189625381)
                    ·
                      refine ⟨326053026875957848054759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1738949476671775189625381 326053026875957848054759)
                      ·
                        rfl

theorem cell23_634986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_634986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_634986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_634986 prefixEnd_634986 := by exact prefixLift 634986
  have htrace : WordTrace (prefixWord ++ tailWord_634986) baseStart_634986 baseEnd_634986 := by
    simpa [prefixWord, tailWord_634986, baseEnd_634986] using wordTrace_append hprefix tailTrace_634986
  have hstable : (prefixWord ++ tailWord_634986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_634986).length < 2 ^ (prefixWord ++ tailWord_634986).sum := by decide
  have hdescent : baseEnd_634986 < baseStart_634986 := by decide
  rcases family_descends (prefixWord ++ tailWord_634986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635029 : List Nat := [1, 3, 2, 1, 1, 1, 6, 2, 1, 3, 2]
def baseStart_635029 : Nat := 118140960795 + 635029 * 2 ^ 59
def prefixEnd_635029 : Nat := 4983230072969 + 3 ^ 40 * 635029 * 2
def baseEnd_635029 : Nat := 326075106544101179817061

theorem tailTrace_635029 : CollatzResearch.WordTrace tailWord_635029 prefixEnd_635029 326075106544101179817061 := by
  unfold tailWord_635029
  simp only [CollatzResearch.WordTrace]
  refine ⟨23161410416405862163820141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15440940277603908109213427 23161410416405862163820141)
  ·
    refine ⟨8685528906152198311432553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23161410416405862163820141 8685528906152198311432553)
    ·
      refine ⟨6514146679614148733574415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8685528906152198311432553 6514146679614148733574415)
      ·
        refine ⟨9771220019421223100361623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6514146679614148733574415 9771220019421223100361623)
        ·
          refine ⟨14656830029131834650542435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9771220019421223100361623 14656830029131834650542435)
          ·
            refine ⟨21985245043697751975813653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14656830029131834650542435 21985245043697751975813653)
            ·
              refine ⟨1030558361423332123866265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21985245043697751975813653 1030558361423332123866265)
              ·
                refine ⟨772918771067499092899699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1030558361423332123866265 772918771067499092899699)
                ·
                  refine ⟨1159378156601248639349549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772918771067499092899699 1159378156601248639349549)
                  ·
                    refine ⟨434766808725468239756081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1159378156601248639349549 434766808725468239756081)
                    ·
                      refine ⟨326075106544101179817061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434766808725468239756081 326075106544101179817061)
                      ·
                        rfl

theorem cell23_635029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_635029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635029 prefixEnd_635029 := by exact prefixLift 635029
  have htrace : WordTrace (prefixWord ++ tailWord_635029) baseStart_635029 baseEnd_635029 := by
    simpa [prefixWord, tailWord_635029, baseEnd_635029] using wordTrace_append hprefix tailTrace_635029
  have hstable : (prefixWord ++ tailWord_635029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635029).length < 2 ^ (prefixWord ++ tailWord_635029).sum := by decide
  have hdescent : baseEnd_635029 < baseStart_635029 := by decide
  rcases family_descends (prefixWord ++ tailWord_635029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635045 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_635045 : Nat := 118140960795 + 635045 * 2 ^ 59
def prefixEnd_635045 : Nat := 4983230072969 + 3 ^ 40 * 635045 * 2
def baseEnd_635045 : Nat := 326083322234573117216987

theorem tailTrace_635045 : CollatzResearch.WordTrace tailWord_635045 prefixEnd_635045 326083322234573117216987 := by
  unfold tailWord_635045
  simp only [CollatzResearch.WordTrace]
  refine ⟨23161993984347896896402589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15441329322898597930935059 23161993984347896896402589)
  ·
    refine ⟨8685747744130461336150971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23161993984347896896402589 8685747744130461336150971)
    ·
      refine ⟨13028621616195692004226457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8685747744130461336150971 13028621616195692004226457)
      ·
        refine ⟨9771466212146769003169843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13028621616195692004226457 9771466212146769003169843)
        ·
          refine ⟨14657199318220153504754765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9771466212146769003169843 14657199318220153504754765)
          ·
            refine ⟨5496449744332557564283037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14657199318220153504754765 5496449744332557564283037)
            ·
              refine ⟨2061168654124709086606139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5496449744332557564283037 2061168654124709086606139)
              ·
                refine ⟨3091752981187063629909209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061168654124709086606139 3091752981187063629909209)
                ·
                  refine ⟨2318814735890297722431907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3091752981187063629909209 2318814735890297722431907)
                  ·
                    refine ⟨3478222103835446583647861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2318814735890297722431907 3478222103835446583647861)
                    ·
                      refine ⟨326083322234573117216987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3478222103835446583647861 326083322234573117216987)
                      ·
                        rfl

theorem cell23_635045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_635045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635045 prefixEnd_635045 := by exact prefixLift 635045
  have htrace : WordTrace (prefixWord ++ tailWord_635045) baseStart_635045 baseEnd_635045 := by
    simpa [prefixWord, tailWord_635045, baseEnd_635045] using wordTrace_append hprefix tailTrace_635045
  have hstable : (prefixWord ++ tailWord_635045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635045).length < 2 ^ (prefixWord ++ tailWord_635045).sum := by decide
  have hdescent : baseEnd_635045 < baseStart_635045 := by decide
  rcases family_descends (prefixWord ++ tailWord_635045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635059 : List Nat := [1, 1, 1, 2, 3, 2, 1, 6, 2, 2, 2]
def baseStart_635059 : Nat := 118140960795 + 635059 * 2 ^ 59
def prefixEnd_635059 : Nat := 4983230072969 + 3 ^ 40 * 635059 * 2
def baseEnd_635059 : Nat := 326090510963736062441923

theorem tailTrace_635059 : CollatzResearch.WordTrace tailWord_635059 prefixEnd_635059 326090510963736062441923 := by
  unfold tailWord_635059
  simp only [CollatzResearch.WordTrace]
  refine ⟨23162504606297177287412231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15441669737531451524941487 23162504606297177287412231)
  ·
    refine ⟨34743756909445765931118347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23162504606297177287412231 34743756909445765931118347)
    ·
      refine ⟨52115635364168648896677521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34743756909445765931118347 52115635364168648896677521)
      ·
        refine ⟨39086726523126486672508141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52115635364168648896677521 39086726523126486672508141)
        ·
          refine ⟨14657522446172432502190553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39086726523126486672508141 14657522446172432502190553)
          ·
            refine ⟨10993141834629324376642915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14657522446172432502190553 10993141834629324376642915)
            ·
              refine ⟨16489712751943986564964373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10993141834629324376642915 16489712751943986564964373)
              ·
                refine ⟨772955285247374370232705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16489712751943986564964373 772955285247374370232705)
                ·
                  refine ⟨579716463935530777674529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 772955285247374370232705 579716463935530777674529)
                  ·
                    refine ⟨434787347951648083255897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 579716463935530777674529 434787347951648083255897)
                    ·
                      refine ⟨326090510963736062441923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434787347951648083255897 326090510963736062441923)
                      ·
                        rfl

theorem cell23_635059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 2, 2].length) (baseStart_635059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635059 prefixEnd_635059 := by exact prefixLift 635059
  have htrace : WordTrace (prefixWord ++ tailWord_635059) baseStart_635059 baseEnd_635059 := by
    simpa [prefixWord, tailWord_635059, baseEnd_635059] using wordTrace_append hprefix tailTrace_635059
  have hstable : (prefixWord ++ tailWord_635059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635059).length < 2 ^ (prefixWord ++ tailWord_635059).sum := by decide
  have hdescent : baseEnd_635059 < baseStart_635059 := by decide
  rcases family_descends (prefixWord ++ tailWord_635059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635070 : List Nat := [4, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_635070 : Nat := 118140960795 + 635070 * 2 ^ 59
def prefixEnd_635070 : Nat := 4983230072969 + 3 ^ 40 * 635070 * 2
def baseEnd_635070 : Nat := 326096159250935519404373

theorem tailTrace_635070 : CollatzResearch.WordTrace tailWord_635070 prefixEnd_635070 326096159250935519404373 := by
  unfold tailWord_635070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2895363226157165770757833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15441937206171550777375109 2895363226157165770757833)
  ·
    refine ⟨2171522419617874328068375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2895363226157165770757833 2171522419617874328068375)
    ·
      refine ⟨3257283629426811492102563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2171522419617874328068375 3257283629426811492102563)
      ·
        refine ⟨4885925444140217238153845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257283629426811492102563 4885925444140217238153845)
        ·
          refine ⟨458055510388145366076923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4885925444140217238153845 458055510388145366076923)
          ·
            refine ⟨687083265582218049115385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458055510388145366076923 687083265582218049115385)
            ·
              refine ⟨515312449186663536836539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687083265582218049115385 515312449186663536836539)
              ·
                refine ⟨772968673779995305254809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515312449186663536836539 772968673779995305254809)
                ·
                  refine ⟨579726505334996478941107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 772968673779995305254809 579726505334996478941107)
                  ·
                    refine ⟨869589758002494718411661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 579726505334996478941107 869589758002494718411661)
                    ·
                      refine ⟨326096159250935519404373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 869589758002494718411661 326096159250935519404373)
                      ·
                        rfl

theorem cell23_635070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_635070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635070 prefixEnd_635070 := by exact prefixLift 635070
  have htrace : WordTrace (prefixWord ++ tailWord_635070) baseStart_635070 baseEnd_635070 := by
    simpa [prefixWord, tailWord_635070, baseEnd_635070] using wordTrace_append hprefix tailTrace_635070
  have hstable : (prefixWord ++ tailWord_635070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635070).length < 2 ^ (prefixWord ++ tailWord_635070).sum := by decide
  have hdescent : baseEnd_635070 < baseStart_635070 := by decide
  rcases family_descends (prefixWord ++ tailWord_635070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635075 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 3]
def baseStart_635075 : Nat := 118140960795 + 635075 * 2 ^ 59
def prefixEnd_635075 : Nat := 4983230072969 + 3 ^ 40 * 635075 * 2
def baseEnd_635075 : Nat := 326098726654207999841849

theorem tailTrace_635075 : CollatzResearch.WordTrace tailWord_635075 prefixEnd_635075 326098726654207999841849 := by
  unfold tailWord_635075
  simp only [CollatzResearch.WordTrace]
  refine ⟨23163088174239212019994679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15442058782826141346663119 23163088174239212019994679)
  ·
    refine ⟨34744632261358818029992019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23163088174239212019994679 34744632261358818029992019)
    ·
      refine ⟨52116948392038227044988029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34744632261358818029992019 52116948392038227044988029)
      ·
        refine ⟨19543855647014335141870511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52116948392038227044988029 19543855647014335141870511)
        ·
          refine ⟨29315783470521502712805767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19543855647014335141870511 29315783470521502712805767)
          ·
            refine ⟨43973675205782254069208651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29315783470521502712805767 43973675205782254069208651)
            ·
              refine ⟨65960512808673381103812977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43973675205782254069208651 65960512808673381103812977)
              ·
                refine ⟨49470384606505035827859733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65960512808673381103812977 49470384606505035827859733)
                ·
                  refine ⟨2318924278429923554430925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49470384606505035827859733 2318924278429923554430925)
                  ·
                    refine ⟨869596604411221332911597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2318924278429923554430925 869596604411221332911597)
                    ·
                      refine ⟨326098726654207999841849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 869596604411221332911597 326098726654207999841849)
                      ·
                        rfl

theorem cell23_635075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_635075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635075 prefixEnd_635075 := by exact prefixLift 635075
  have htrace : WordTrace (prefixWord ++ tailWord_635075) baseStart_635075 baseEnd_635075 := by
    simpa [prefixWord, tailWord_635075, baseEnd_635075] using wordTrace_append hprefix tailTrace_635075
  have hstable : (prefixWord ++ tailWord_635075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635075).length < 2 ^ (prefixWord ++ tailWord_635075).sum := by decide
  have hdescent : baseEnd_635075 < baseStart_635075 := by decide
  rcases family_descends (prefixWord ++ tailWord_635075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635105 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_635105 : Nat := 118140960795 + 635105 * 2 ^ 59
def prefixEnd_635105 : Nat := 4983230072969 + 3 ^ 40 * 635105 * 2
def baseEnd_635105 : Nat := 326114131073842882466711

theorem tailTrace_635105 : CollatzResearch.WordTrace tailWord_635105 prefixEnd_635105 326114131073842882466711 := by
  unfold tailWord_635105
  simp only [CollatzResearch.WordTrace]
  refine ⟨23164182364130527143586769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15442788242753684762391179 23164182364130527143586769)
  ·
    refine ⟨17373136773097895357690077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23164182364130527143586769 17373136773097895357690077)
    ·
      refine ⟨6514926289911710759133779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17373136773097895357690077 6514926289911710759133779)
      ·
        refine ⟨9772389434867566138700669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6514926289911710759133779 9772389434867566138700669)
        ·
          refine ⟨3664646038075337302012751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9772389434867566138700669 3664646038075337302012751)
          ·
            refine ⟨5496969057113005953019127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3664646038075337302012751 5496969057113005953019127)
            ·
              refine ⟨8245453585669508929528691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5496969057113005953019127 8245453585669508929528691)
              ·
                refine ⟨12368180378504263394293037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8245453585669508929528691 12368180378504263394293037)
                ·
                  refine ⟨4638067641939098772859889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12368180378504263394293037 4638067641939098772859889)
                  ·
                    refine ⟨3478550731454324079644917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4638067641939098772859889 3478550731454324079644917)
                    ·
                      refine ⟨326114131073842882466711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3478550731454324079644917 326114131073842882466711)
                      ·
                        rfl

theorem cell23_635105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_635105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635105 prefixEnd_635105 := by exact prefixLift 635105
  have htrace : WordTrace (prefixWord ++ tailWord_635105) baseStart_635105 baseEnd_635105 := by
    simpa [prefixWord, tailWord_635105, baseEnd_635105] using wordTrace_append hprefix tailTrace_635105
  have hstable : (prefixWord ++ tailWord_635105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635105).length < 2 ^ (prefixWord ++ tailWord_635105).sum := by decide
  have hdescent : baseEnd_635105 < baseStart_635105 := by decide
  rcases family_descends (prefixWord ++ tailWord_635105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635112 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 2, 5]
def baseStart_635112 : Nat := 118140960795 + 635112 * 2 ^ 59
def prefixEnd_635112 : Nat := 4983230072969 + 3 ^ 40 * 635112 * 2
def baseEnd_635112 : Nat := 108705908479474785026393

theorem tailTrace_635112 : CollatzResearch.WordTrace tailWord_635112 prefixEnd_635112 108705908479474785026393 := by
  unfold tailWord_635112
  simp only [CollatzResearch.WordTrace]
  refine ⟨11582218837552583669545795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15442958450070111559394393 11582218837552583669545795)
  ·
    refine ⟨17373328256328875504318693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11582218837552583669545795 17373328256328875504318693)
    ·
      refine ⟨3257499048061664157059755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17373328256328875504318693 3257499048061664157059755)
      ·
        refine ⟨4886248572092496235589633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257499048061664157059755 4886248572092496235589633)
        ·
          refine ⟨3664686429069372176692225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4886248572092496235589633 3664686429069372176692225)
          ·
            refine ⟨2748514821802029132519169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3664686429069372176692225 2748514821802029132519169)
            ·
              refine ⟨2061386116351521849389377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2748514821802029132519169 2061386116351521849389377)
              ·
                refine ⟨1546039587263641387042033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2061386116351521849389377 1546039587263641387042033)
                ·
                  refine ⟨1159529690447731040281525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1546039587263641387042033 1159529690447731040281525)
                  ·
                    refine ⟨108705908479474785026393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1159529690447731040281525 108705908479474785026393)
                    ·
                      rfl

theorem cell23_635112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_635112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635112 prefixEnd_635112 := by exact prefixLift 635112
  have htrace : WordTrace (prefixWord ++ tailWord_635112) baseStart_635112 baseEnd_635112 := by
    simpa [prefixWord, tailWord_635112, baseEnd_635112] using wordTrace_append hprefix tailTrace_635112
  have hstable : (prefixWord ++ tailWord_635112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635112).length < 2 ^ (prefixWord ++ tailWord_635112).sum := by decide
  have hdescent : baseEnd_635112 < baseStart_635112 := by decide
  rcases family_descends (prefixWord ++ tailWord_635112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635122 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_635122 : Nat := 118140960795 + 635122 * 2 ^ 59
def prefixEnd_635122 : Nat := 4983230072969 + 3 ^ 40 * 635122 * 2
def baseEnd_635122 : Nat := 326122860244969315954133

theorem tailTrace_635122 : CollatzResearch.WordTrace tailWord_635122 prefixEnd_635122 326122860244969315954133 := by
  unfold tailWord_635122
  simp only [CollatzResearch.WordTrace]
  refine ⟨5791200601267234761738905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15443201603379292697970413 5791200601267234761738905)
  ·
    refine ⟨4343400450950426071304179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5791200601267234761738905 4343400450950426071304179)
    ·
      refine ⟨6515100676425639106956269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4343400450950426071304179 6515100676425639106956269)
      ·
        refine ⟨2443162753659614665108601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6515100676425639106956269 2443162753659614665108601)
        ·
          refine ⟨1832372065244710998831451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2443162753659614665108601 1832372065244710998831451)
          ·
            refine ⟨2748558097867066498247177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1832372065244710998831451 2748558097867066498247177)
            ·
              refine ⟨2061418573400299873685383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2748558097867066498247177 2061418573400299873685383)
              ·
                refine ⟨3092127860100449810528075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061418573400299873685383 3092127860100449810528075)
                ·
                  refine ⟨4638191790150674715792113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3092127860100449810528075 4638191790150674715792113)
                  ·
                    refine ⟨3478643842613006036844085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4638191790150674715792113 3478643842613006036844085)
                    ·
                      refine ⟨326122860244969315954133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3478643842613006036844085 326122860244969315954133)
                      ·
                        rfl

theorem cell23_635122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_635122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635122 prefixEnd_635122 := by exact prefixLift 635122
  have htrace : WordTrace (prefixWord ++ tailWord_635122) baseStart_635122 baseEnd_635122 := by
    simpa [prefixWord, tailWord_635122, baseEnd_635122] using wordTrace_append hprefix tailTrace_635122
  have hstable : (prefixWord ++ tailWord_635122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635122).length < 2 ^ (prefixWord ++ tailWord_635122).sum := by decide
  have hdescent : baseEnd_635122 < baseStart_635122 := by decide
  rcases family_descends (prefixWord ++ tailWord_635122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635172 : List Nat := [2, 3, 1, 3, 1, 3, 1, 1, 8]
def baseStart_635172 : Nat := 118140960795 + 635172 * 2 ^ 59
def prefixEnd_635172 : Nat := 4983230072969 + 3 ^ 40 * 635172 * 2
def baseEnd_635172 : Nat := 36238726030854902258767

theorem tailTrace_635172 : CollatzResearch.WordTrace tailWord_635172 prefixEnd_635172 36238726030854902258767 := by
  unfold tailWord_635172
  simp only [CollatzResearch.WordTrace]
  refine ⟨11583313027443898793137885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15444417369925198390850513 11583313027443898793137885)
  ·
    refine ⟨4343742385291462047426707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11583313027443898793137885 4343742385291462047426707)
    ·
      refine ⟨6515613577937193071140061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4343742385291462047426707 6515613577937193071140061)
      ·
        refine ⟨2443355091726447401677523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6515613577937193071140061 2443355091726447401677523)
        ·
          refine ⟨3665032637589671102516285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2443355091726447401677523 3665032637589671102516285)
          ·
            refine ⟨1374387239096126663443607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3665032637589671102516285 1374387239096126663443607)
            ·
              refine ⟨2061580858644189995165411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374387239096126663443607 2061580858644189995165411)
              ·
                refine ⟨3092371287966284992748117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061580858644189995165411 3092371287966284992748117)
                ·
                  refine ⟨36238726030854902258767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3092371287966284992748117 36238726030854902258767)
                  ·
                    rfl

theorem cell23_635172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_635172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635172 prefixEnd_635172 := by exact prefixLift 635172
  have htrace : WordTrace (prefixWord ++ tailWord_635172) baseStart_635172 baseEnd_635172 := by
    simpa [prefixWord, tailWord_635172, baseEnd_635172] using wordTrace_append hprefix tailTrace_635172
  have hstable : (prefixWord ++ tailWord_635172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635172).length < 2 ^ (prefixWord ++ tailWord_635172).sum := by decide
  have hdescent : baseEnd_635172 < baseStart_635172 := by decide
  rcases family_descends (prefixWord ++ tailWord_635172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635176 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 3, 4]
def baseStart_635176 : Nat := 118140960795 + 635176 * 2 ^ 59
def prefixEnd_635176 : Nat := 4983230072969 + 3 ^ 40 * 635176 * 2
def baseEnd_635176 : Nat := 108716862733437368226295

theorem tailTrace_635176 : CollatzResearch.WordTrace tailWord_635176 prefixEnd_635176 108716862733437368226295 := by
  unfold tailWord_635176
  simp only [CollatzResearch.WordTrace]
  refine ⟨11583385973436653134710691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15444514631248870846280921 11583385973436653134710691)
  ·
    refine ⟨17375078960154979702066037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11583385973436653134710691 17375078960154979702066037)
    ·
      refine ⟨1628913652514529347068691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17375078960154979702066037 1628913652514529347068691)
      ·
        refine ⟨2443370478771794020603037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628913652514529347068691 2443370478771794020603037)
        ·
          refine ⟨916263929539422757726139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2443370478771794020603037 916263929539422757726139)
          ·
            refine ⟨1374395894309134136589209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916263929539422757726139 1374395894309134136589209)
            ·
              refine ⟨1030796920731850602441907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1374395894309134136589209 1030796920731850602441907)
              ·
                refine ⟨1546195381097775903662861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1030796920731850602441907 1546195381097775903662861)
                ·
                  refine ⟨579823267911665963873573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1546195381097775903662861 579823267911665963873573)
                  ·
                    refine ⟨108716862733437368226295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 579823267911665963873573 108716862733437368226295)
                    ·
                      rfl

theorem cell23_635176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_635176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635176 prefixEnd_635176 := by exact prefixLift 635176
  have htrace : WordTrace (prefixWord ++ tailWord_635176) baseStart_635176 baseEnd_635176 := by
    simpa [prefixWord, tailWord_635176, baseEnd_635176] using wordTrace_append hprefix tailTrace_635176
  have hstable : (prefixWord ++ tailWord_635176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635176).length < 2 ^ (prefixWord ++ tailWord_635176).sum := by decide
  have hdescent : baseEnd_635176 < baseStart_635176 := by decide
  rcases family_descends (prefixWord ++ tailWord_635176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635189 : List Nat := [1, 3, 3, 1, 2, 1, 5, 1, 6]
def baseStart_635189 : Nat := 118140960795 + 635189 * 2 ^ 59
def prefixEnd_635189 : Nat := 4983230072969 + 3 ^ 40 * 635189 * 2
def baseEnd_635189 : Nat := 36239695938757839312925

theorem tailTrace_635189 : CollatzResearch.WordTrace tailWord_635189 prefixEnd_635189 36239695938757839312925 := by
  unfold tailWord_635189
  simp only [CollatzResearch.WordTrace]
  refine ⟨23167246095826209489644621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15444830730550806326429747 23167246095826209489644621)
  ·
    refine ⟨8687717285934828558616733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23167246095826209489644621 8687717285934828558616733)
    ·
      refine ⟨3257893982225560709481275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8687717285934828558616733 3257893982225560709481275)
      ·
        refine ⟨4886840973338341064221913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257893982225560709481275 4886840973338341064221913)
        ·
          refine ⟨3665130730003755798166435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4886840973338341064221913 3665130730003755798166435)
          ·
            refine ⟨5497696095005633697249653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665130730003755798166435 5497696095005633697249653)
            ·
              refine ⟨515409008906778159117155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5497696095005633697249653 515409008906778159117155)
              ·
                refine ⟨773113513360167238675733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515409008906778159117155 773113513360167238675733)
                ·
                  refine ⟨36239695938757839312925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 773113513360167238675733 36239695938757839312925)
                  ·
                    rfl

theorem cell23_635189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 6].length) (baseStart_635189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635189 prefixEnd_635189 := by exact prefixLift 635189
  have htrace : WordTrace (prefixWord ++ tailWord_635189) baseStart_635189 baseEnd_635189 := by
    simpa [prefixWord, tailWord_635189, baseEnd_635189] using wordTrace_append hprefix tailTrace_635189
  have hstable : (prefixWord ++ tailWord_635189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635189).length < 2 ^ (prefixWord ++ tailWord_635189).sum := by decide
  have hdescent : baseEnd_635189 < baseStart_635189 := by decide
  rcases family_descends (prefixWord ++ tailWord_635189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635199 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 3, 1, 3]
def baseStart_635199 : Nat := 118140960795 + 635199 * 2 ^ 59
def prefixEnd_635199 : Nat := 4983230072969 + 3 ^ 40 * 635199 * 2
def baseEnd_635199 : Nat := 326162398255365514691279

theorem tailTrace_635199 : CollatzResearch.WordTrace tailWord_635199 prefixEnd_635199 326162398255365514691279 := by
  unfold tailWord_635199
  simp only [CollatzResearch.WordTrace]
  refine ⟨23167610825789981197508651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15445073883859987465005767 23167610825789981197508651)
  ·
    refine ⟨34751416238684971796262977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23167610825789981197508651 34751416238684971796262977)
    ·
      refine ⟨26063562179013728847197233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34751416238684971796262977 26063562179013728847197233)
      ·
        refine ⟨19547671634260296635397925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26063562179013728847197233 19547671634260296635397925)
        ·
          refine ⟨3665188431423805619137111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19547671634260296635397925 3665188431423805619137111)
          ·
            refine ⟨5497782647135708428705667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3665188431423805619137111 5497782647135708428705667)
            ·
              refine ⟨8246673970703562643058501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5497782647135708428705667 8246673970703562643058501)
              ·
                refine ⟨1546251369506917995573469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8246673970703562643058501 1546251369506917995573469)
                ·
                  refine ⟨579844263565094248340051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1546251369506917995573469 579844263565094248340051)
                  ·
                    refine ⟨869766395347641372510077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 579844263565094248340051 869766395347641372510077)
                    ·
                      refine ⟨326162398255365514691279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 869766395347641372510077 326162398255365514691279)
                      ·
                        rfl

theorem cell23_635199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_635199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635199 prefixEnd_635199 := by exact prefixLift 635199
  have htrace : WordTrace (prefixWord ++ tailWord_635199) baseStart_635199 baseEnd_635199 := by
    simpa [prefixWord, tailWord_635199, baseEnd_635199] using wordTrace_append hprefix tailTrace_635199
  have hstable : (prefixWord ++ tailWord_635199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635199).length < 2 ^ (prefixWord ++ tailWord_635199).sum := by decide
  have hdescent : baseEnd_635199 < baseStart_635199 := by decide
  rcases family_descends (prefixWord ++ tailWord_635199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635209 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 2, 3, 2]
def baseStart_635209 : Nat := 118140960795 + 635209 * 2 ^ 59
def prefixEnd_635209 : Nat := 4983230072969 + 3 ^ 40 * 635209 * 2
def baseEnd_635209 : Nat := 326167533061910475566233

theorem tailTrace_635209 : CollatzResearch.WordTrace tailWord_635209 prefixEnd_635209 326167533061910475566233 := by
  unfold tailWord_635209
  simp only [CollatzResearch.WordTrace]
  refine ⟨23167975555753752905372681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15445317037169168603581787 23167975555753752905372681)
  ·
    refine ⟨17375981666815314679029511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23167975555753752905372681 17375981666815314679029511)
    ·
      refine ⟨26063972500222972018544267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17375981666815314679029511 26063972500222972018544267)
      ·
        refine ⟨39095958750334458027816401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26063972500222972018544267 39095958750334458027816401)
        ·
          refine ⟨29321969062750843520862301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39095958750334458027816401 29321969062750843520862301)
          ·
            refine ⟨10995738398531566320323363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29321969062750843520862301 10995738398531566320323363)
            ·
              refine ⟨16493607597797349480485045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10995738398531566320323363 16493607597797349480485045)
              ·
                refine ⟨1546275712293501513795473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16493607597797349480485045 1546275712293501513795473)
                ·
                  refine ⟨1159706784220126135346605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1546275712293501513795473 1159706784220126135346605)
                  ·
                    refine ⟨434890044082547300754977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1159706784220126135346605 434890044082547300754977)
                    ·
                      refine ⟨326167533061910475566233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434890044082547300754977 326167533061910475566233)
                      ·
                        rfl

theorem cell23_635209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 3, 2].length) (baseStart_635209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635209 prefixEnd_635209 := by exact prefixLift 635209
  have htrace : WordTrace (prefixWord ++ tailWord_635209) baseStart_635209 baseEnd_635209 := by
    simpa [prefixWord, tailWord_635209, baseEnd_635209] using wordTrace_append hprefix tailTrace_635209
  have hstable : (prefixWord ++ tailWord_635209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635209).length < 2 ^ (prefixWord ++ tailWord_635209).sum := by decide
  have hdescent : baseEnd_635209 < baseStart_635209 := by decide
  rcases family_descends (prefixWord ++ tailWord_635209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635259 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 3]
def baseStart_635259 : Nat := 118140960795 + 635259 * 2 ^ 59
def prefixEnd_635259 : Nat := 4983230072969 + 3 ^ 40 * 635259 * 2
def baseEnd_635259 : Nat := 326193207094635279941003

theorem tailTrace_635259 : CollatzResearch.WordTrace tailWord_635259 prefixEnd_635259 326193207094635279941003 := by
  unfold tailWord_635259
  simp only [CollatzResearch.WordTrace]
  refine ⟨23169799205572611444692831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15446532803715074296461887 23169799205572611444692831)
  ·
    refine ⟨34754698808358917167039247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23169799205572611444692831 34754698808358917167039247)
    ·
      refine ⟨52132048212538375750558871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34754698808358917167039247 52132048212538375750558871)
      ·
        refine ⟨78198072318807563625838307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52132048212538375750558871 78198072318807563625838307)
        ·
          refine ⟨117297108478211345438757461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78198072318807563625838307 117297108478211345438757461)
          ·
            refine ⟨1374575489979039204360439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 117297108478211345438757461 1374575489979039204360439)
            ·
              refine ⟨2061863234968558806540659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374575489979039204360439 2061863234968558806540659)
              ·
                refine ⟨3092794852452838209810989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2061863234968558806540659 3092794852452838209810989)
                ·
                  refine ⟨1159798069669814328679121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3092794852452838209810989 1159798069669814328679121)
                  ·
                    refine ⟨869848552252360746509341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1159798069669814328679121 869848552252360746509341)
                    ·
                      refine ⟨326193207094635279941003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 869848552252360746509341 326193207094635279941003)
                      ·
                        rfl

theorem cell23_635259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 3].length) (baseStart_635259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635259 prefixEnd_635259 := by exact prefixLift 635259
  have htrace : WordTrace (prefixWord ++ tailWord_635259) baseStart_635259 baseEnd_635259 := by
    simpa [prefixWord, tailWord_635259, baseEnd_635259] using wordTrace_append hprefix tailTrace_635259
  have hstable : (prefixWord ++ tailWord_635259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635259).length < 2 ^ (prefixWord ++ tailWord_635259).sum := by decide
  have hdescent : baseEnd_635259 < baseStart_635259 := by decide
  rcases family_descends (prefixWord ++ tailWord_635259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635284 : List Nat := [2, 4, 2, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_635284 : Nat := 118140960795 + 635284 * 2 ^ 59
def prefixEnd_635284 : Nat := 4983230072969 + 3 ^ 40 * 635284 * 2
def baseEnd_635284 : Nat := 326206044110997682128389

theorem tailTrace_635284 : CollatzResearch.WordTrace tailWord_635284 prefixEnd_635284 326206044110997682128389 := by
  unfold tailWord_635284
  simp only [CollatzResearch.WordTrace]
  refine ⟨11585355515241020357176453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15447140686988027142901937 11585355515241020357176453)
  ·
    refine ⟨2172254159107691316970585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11585355515241020357176453 2172254159107691316970585)
    ·
      refine ⟨1629190619330768487727939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2172254159107691316970585 1629190619330768487727939)
      ·
        refine ⟨2443785928996152731591909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1629190619330768487727939 2443785928996152731591909)
        ·
          refine ⟨458209861686778637173483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2443785928996152731591909 458209861686778637173483)
          ·
            refine ⟨687314792530167955760225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458209861686778637173483 687314792530167955760225)
            ·
              refine ⟨515486094397625966820169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687314792530167955760225 515486094397625966820169)
              ·
                refine ⟨386614570798219475115127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515486094397625966820169 386614570798219475115127)
                ·
                  refine ⟨579921856197329212672691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386614570798219475115127 579921856197329212672691)
                  ·
                    refine ⟨869882784295993819009037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 579921856197329212672691 869882784295993819009037)
                    ·
                      refine ⟨326206044110997682128389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 869882784295993819009037 326206044110997682128389)
                      ·
                        rfl

theorem cell23_635284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_635284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635284 prefixEnd_635284 := by exact prefixLift 635284
  have htrace : WordTrace (prefixWord ++ tailWord_635284) baseStart_635284 baseEnd_635284 := by
    simpa [prefixWord, tailWord_635284, baseEnd_635284] using wordTrace_append hprefix tailTrace_635284
  have hstable : (prefixWord ++ tailWord_635284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635284).length < 2 ^ (prefixWord ++ tailWord_635284).sum := by decide
  have hdescent : baseEnd_635284 < baseStart_635284 := by decide
  rcases family_descends (prefixWord ++ tailWord_635284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635290 : List Nat := [3, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2]
def baseStart_635290 : Nat := 118140960795 + 635290 * 2 ^ 59
def prefixEnd_635290 : Nat := 4983230072969 + 3 ^ 40 * 635290 * 2
def baseEnd_635290 : Nat := 326209124994924658653361

theorem tailTrace_635290 : CollatzResearch.WordTrace tailWord_635290 prefixEnd_635290 326209124994924658653361 := by
  unfold tailWord_635290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5792732467115075934767831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15447286578973535826047549 5792732467115075934767831)
  ·
    refine ⟨8689098700672613902151747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5792732467115075934767831 8689098700672613902151747)
    ·
      refine ⟨13033648051008920853227621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8689098700672613902151747 13033648051008920853227621)
      ·
        refine ⟨2443809009564172659980179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13033648051008920853227621 2443809009564172659980179)
        ·
          refine ⟨3665713514346258989970269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2443809009564172659980179 3665713514346258989970269)
          ·
            refine ⟨1374642567879847121238851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3665713514346258989970269 1374642567879847121238851)
            ·
              refine ⟨2061963851819770681858277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374642567879847121238851 2061963851819770681858277)
              ·
                refine ⟨386618222216207002848427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2061963851819770681858277 386618222216207002848427)
                ·
                  refine ⟨579927333324310504272641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386618222216207002848427 579927333324310504272641)
                  ·
                    refine ⟨434945499993232878204481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 579927333324310504272641 434945499993232878204481)
                    ·
                      refine ⟨326209124994924658653361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 434945499993232878204481 326209124994924658653361)
                      ·
                        rfl

theorem cell23_635290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_635290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635290 prefixEnd_635290 := by exact prefixLift 635290
  have htrace : WordTrace (prefixWord ++ tailWord_635290) baseStart_635290 baseEnd_635290 := by
    simpa [prefixWord, tailWord_635290, baseEnd_635290] using wordTrace_append hprefix tailTrace_635290
  have hstable : (prefixWord ++ tailWord_635290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635290).length < 2 ^ (prefixWord ++ tailWord_635290).sum := by decide
  have hdescent : baseEnd_635290 < baseStart_635290 := by decide
  rcases family_descends (prefixWord ++ tailWord_635290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635340 : List Nat := [2, 2, 1, 4, 3, 2, 1, 2, 2, 1, 3]
def baseStart_635340 : Nat := 118140960795 + 635340 * 2 ^ 59
def prefixEnd_635340 : Nat := 4983230072969 + 3 ^ 40 * 635340 * 2
def baseEnd_635340 : Nat := 326234799027649463028131

theorem tailTrace_635340 : CollatzResearch.WordTrace tailWord_635340 prefixEnd_635340 326234799027649463028131 := by
  unfold tailWord_635340
  simp only [CollatzResearch.WordTrace]
  refine ⟨11586376759139581139195737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15448502345519441518927649 11586376759139581139195737)
  ·
    refine ⟨8689782569354685854396803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11586376759139581139195737 8689782569354685854396803)
    ·
      refine ⟨13034673854032028781595205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8689782569354685854396803 13034673854032028781595205)
      ·
        refine ⟨2444001347631005396549101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13034673854032028781595205 2444001347631005396549101)
        ·
          refine ⟨916500505361627023705913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2444001347631005396549101 916500505361627023705913)
          ·
            refine ⟨687375379021220267779435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 916500505361627023705913 687375379021220267779435)
            ·
              refine ⟨1031063068531830401669153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687375379021220267779435 1031063068531830401669153)
              ·
                refine ⟨773297301398872801251865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1031063068531830401669153 773297301398872801251865)
                ·
                  refine ⟨579972976049154600938899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 773297301398872801251865 579972976049154600938899)
                  ·
                    refine ⟨869959464073731901408349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 579972976049154600938899 869959464073731901408349)
                    ·
                      refine ⟨326234799027649463028131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 869959464073731901408349 326234799027649463028131)
                      ·
                        rfl

theorem cell23_635340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_635340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635340 prefixEnd_635340 := by exact prefixLift 635340
  have htrace : WordTrace (prefixWord ++ tailWord_635340) baseStart_635340 baseEnd_635340 := by
    simpa [prefixWord, tailWord_635340, baseEnd_635340] using wordTrace_append hprefix tailTrace_635340
  have hstable : (prefixWord ++ tailWord_635340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635340).length < 2 ^ (prefixWord ++ tailWord_635340).sum := by decide
  have hdescent : baseEnd_635340 < baseStart_635340 := by decide
  rcases family_descends (prefixWord ++ tailWord_635340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635359 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 4]
def baseStart_635359 : Nat := 118140960795 + 635359 * 2 ^ 59
def prefixEnd_635359 : Nat := 4983230072969 + 3 ^ 40 * 635359 * 2
def baseEnd_635359 : Nat := 326244555160084888690543

theorem tailTrace_635359 : CollatzResearch.WordTrace tailWord_635359 prefixEnd_635359 326244555160084888690543 := by
  unfold tailWord_635359
  simp only [CollatzResearch.WordTrace]
  refine ⟨23173446505210328523333131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15448964336806885682222087 23173446505210328523333131)
  ·
    refine ⟨34760169757815492784999697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23173446505210328523333131 34760169757815492784999697)
    ·
      refine ⟨26070127318361619588749773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34760169757815492784999697 26070127318361619588749773)
      ·
        refine ⟨9776297744385607345781165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26070127318361619588749773 9776297744385607345781165)
        ·
          refine ⟨3666111654144602754667937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9776297744385607345781165 3666111654144602754667937)
          ·
            refine ⟨2749583740608452066000953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3666111654144602754667937 2749583740608452066000953)
            ·
              refine ⟨2062187805456339049500715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2749583740608452066000953 2062187805456339049500715)
              ·
                refine ⟨3093281708184508574251073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062187805456339049500715 3093281708184508574251073)
                ·
                  refine ⟨2319961281138381430688305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3093281708184508574251073 2319961281138381430688305)
                  ·
                    refine ⟨1739970960853786073016229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2319961281138381430688305 1739970960853786073016229)
                    ·
                      refine ⟨326244555160084888690543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1739970960853786073016229 326244555160084888690543)
                      ·
                        rfl

theorem cell23_635359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_635359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635359 prefixEnd_635359 := by exact prefixLift 635359
  have htrace : WordTrace (prefixWord ++ tailWord_635359) baseStart_635359 baseEnd_635359 := by
    simpa [prefixWord, tailWord_635359, baseEnd_635359] using wordTrace_append hprefix tailTrace_635359
  have hstable : (prefixWord ++ tailWord_635359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635359).length < 2 ^ (prefixWord ++ tailWord_635359).sum := by decide
  have hdescent : baseEnd_635359 < baseStart_635359 := by decide
  rcases family_descends (prefixWord ++ tailWord_635359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635392 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 7]
def baseStart_635392 : Nat := 118140960795 + 635392 * 2 ^ 59
def prefixEnd_635392 : Nat := 4983230072969 + 3 ^ 40 * 635392 * 2
def baseEnd_635392 : Nat := 326261500021683259577891

theorem tailTrace_635392 : CollatzResearch.WordTrace tailWord_635392 prefixEnd_635392 326261500021683259577891 := by
  unfold tailWord_635392
  simp only [CollatzResearch.WordTrace]
  refine ⟨11587325057045387579642215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15449766742727183439522953 11587325057045387579642215)
  ·
    refine ⟨17380987585568081369463323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11587325057045387579642215 17380987585568081369463323)
    ·
      refine ⟨26071481378352122054194985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17380987585568081369463323 26071481378352122054194985)
      ·
        refine ⟨19553611033764091540646239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26071481378352122054194985 19553611033764091540646239)
        ·
          refine ⟨29330416550646137310969359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19553611033764091540646239 29330416550646137310969359)
          ·
            refine ⟨43995624825969205966454039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29330416550646137310969359 43995624825969205966454039)
            ·
              refine ⟨65993437238953808949681059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43995624825969205966454039 65993437238953808949681059)
              ·
                refine ⟨98990155858430713424521589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65993437238953808949681059 98990155858430713424521589)
                ·
                  refine ⟨9280327111727879383548899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98990155858430713424521589 9280327111727879383548899)
                  ·
                    refine ⟨13920490667591819075323349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9280327111727879383548899 13920490667591819075323349)
                    ·
                      refine ⟨326261500021683259577891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13920490667591819075323349 326261500021683259577891)
                      ·
                        rfl

theorem cell23_635392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_635392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635392 prefixEnd_635392 := by exact prefixLift 635392
  have htrace : WordTrace (prefixWord ++ tailWord_635392) baseStart_635392 baseEnd_635392 := by
    simpa [prefixWord, tailWord_635392, baseEnd_635392] using wordTrace_append hprefix tailTrace_635392
  have hstable : (prefixWord ++ tailWord_635392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635392).length < 2 ^ (prefixWord ++ tailWord_635392).sum := by decide
  have hdescent : baseEnd_635392 < baseStart_635392 := by decide
  rcases family_descends (prefixWord ++ tailWord_635392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635403 : List Nat := [1, 1, 1, 1, 7, 2, 3, 2, 5]
def baseStart_635403 : Nat := 118140960795 + 635403 * 2 ^ 59
def prefixEnd_635403 : Nat := 4983230072969 + 3 ^ 40 * 635403 * 2
def baseEnd_635403 : Nat := 36251905367653635171149

theorem tailTrace_635403 : CollatzResearch.WordTrace tailWord_635403 prefixEnd_635403 36251905367653635171149 := by
  unfold tailWord_635403
  simp only [CollatzResearch.WordTrace]
  refine ⟨23175051317050924037934863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15450034211367282691956575 23175051317050924037934863)
  ·
    refine ⟨34762576975576386056902295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23175051317050924037934863 34762576975576386056902295)
    ·
      refine ⟨52143865463364579085353443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34762576975576386056902295 52143865463364579085353443)
      ·
        refine ⟨78215798195046868628030165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52143865463364579085353443 78215798195046868628030165)
        ·
          refine ⟨1833182770196410983469457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 78215798195046868628030165 1833182770196410983469457)
          ·
            refine ⟨1374887077647308237602093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1833182770196410983469457 1374887077647308237602093)
            ·
              refine ⟨515582654117740589100785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1374887077647308237602093 515582654117740589100785)
              ·
                refine ⟨386686990588305441825589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515582654117740589100785 386686990588305441825589)
                ·
                  refine ⟨36251905367653635171149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 386686990588305441825589 36251905367653635171149)
                  ·
                    rfl

theorem cell23_635403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2, 5].length) (baseStart_635403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635403 prefixEnd_635403 := by exact prefixLift 635403
  have htrace : WordTrace (prefixWord ++ tailWord_635403) baseStart_635403 baseEnd_635403 := by
    simpa [prefixWord, tailWord_635403, baseEnd_635403] using wordTrace_append hprefix tailTrace_635403
  have hstable : (prefixWord ++ tailWord_635403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635403).length < 2 ^ (prefixWord ++ tailWord_635403).sum := by decide
  have hdescent : baseEnd_635403 < baseStart_635403 := by decide
  rcases family_descends (prefixWord ++ tailWord_635403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635449 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 6]
def baseStart_635449 : Nat := 118140960795 + 635449 * 2 ^ 59
def prefixEnd_635449 : Nat := 4983230072969 + 3 ^ 40 * 635449 * 2
def baseEnd_635449 : Nat := 326290768418989536565129

theorem tailTrace_635449 : CollatzResearch.WordTrace tailWord_635449 prefixEnd_635449 326290768418989536565129 := by
  unfold tailWord_635449
  simp only [CollatzResearch.WordTrace]
  refine ⟨23176729074884273894109401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15451152716589515929406267 23176729074884273894109401)
  ·
    refine ⟨17382546806163205420582051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23176729074884273894109401 17382546806163205420582051)
    ·
      refine ⟨26073820209244808130873077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17382546806163205420582051 26073820209244808130873077)
      ·
        refine ⟨2444420644616700762269351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26073820209244808130873077 2444420644616700762269351)
        ·
          refine ⟨3666630966925051143404027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2444420644616700762269351 3666630966925051143404027)
          ·
            refine ⟨5499946450387576715106041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3666630966925051143404027 5499946450387576715106041)
            ·
              refine ⟨4124959837790682536329531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5499946450387576715106041 4124959837790682536329531)
              ·
                refine ⟨6187439756686023804494297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4124959837790682536329531 6187439756686023804494297)
                ·
                  refine ⟨4640579817514517853370723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6187439756686023804494297 4640579817514517853370723)
                  ·
                    refine ⟨6960869726271776780056085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4640579817514517853370723 6960869726271776780056085)
                    ·
                      refine ⟨326290768418989536565129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6960869726271776780056085 326290768418989536565129)
                      ·
                        rfl

theorem cell23_635449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_635449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635449 prefixEnd_635449 := by exact prefixLift 635449
  have htrace : WordTrace (prefixWord ++ tailWord_635449) baseStart_635449 baseEnd_635449 := by
    simpa [prefixWord, tailWord_635449, baseEnd_635449] using wordTrace_append hprefix tailTrace_635449
  have hstable : (prefixWord ++ tailWord_635449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635449).length < 2 ^ (prefixWord ++ tailWord_635449).sum := by decide
  have hdescent : baseEnd_635449 < baseStart_635449 := by decide
  rcases family_descends (prefixWord ++ tailWord_635449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635454 : List Nat := [4, 2, 1, 4, 2, 1, 2, 2, 5]
def baseStart_635454 : Nat := 118140960795 + 635454 * 2 ^ 59
def prefixEnd_635454 : Nat := 4983230072969 + 3 ^ 40 * 635454 * 2
def baseEnd_635454 : Nat := 36254815091362446333623

theorem tailTrace_635454 : CollatzResearch.WordTrace tailWord_635454 prefixEnd_635454 36254815091362446333623 := by
  unfold tailWord_635454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2897113929983269968505177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15451274293244106498694277 2897113929983269968505177)
  ·
    refine ⟨2172835447487452476378883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2897113929983269968505177 2172835447487452476378883)
    ·
      refine ⟨3259253171231178714568325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2172835447487452476378883 3259253171231178714568325)
      ·
        refine ⟨611109969605846008981561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3259253171231178714568325 611109969605846008981561)
        ·
          refine ⟨458332477204384506736171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 611109969605846008981561 458332477204384506736171)
          ·
            refine ⟨687498715806576760104257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458332477204384506736171 687498715806576760104257)
            ·
              refine ⟨515624036854932570078193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687498715806576760104257 515624036854932570078193)
              ·
                refine ⟨386718027641199427558645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515624036854932570078193 386718027641199427558645)
                ·
                  refine ⟨36254815091362446333623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 386718027641199427558645 36254815091362446333623)
                  ·
                    rfl

theorem cell23_635454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_635454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635454 prefixEnd_635454 := by exact prefixLift 635454
  have htrace : WordTrace (prefixWord ++ tailWord_635454) baseStart_635454 baseEnd_635454 := by
    simpa [prefixWord, tailWord_635454, baseEnd_635454] using wordTrace_append hprefix tailTrace_635454
  have hstable : (prefixWord ++ tailWord_635454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635454).length < 2 ^ (prefixWord ++ tailWord_635454).sum := by decide
  have hdescent : baseEnd_635454 < baseStart_635454 := by decide
  rcases family_descends (prefixWord ++ tailWord_635454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635456 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 3]
def baseStart_635456 : Nat := 118140960795 + 635456 * 2 ^ 59
def prefixEnd_635456 : Nat := 4983230072969 + 3 ^ 40 * 635456 * 2
def baseEnd_635456 : Nat := 326294362783571009177597

theorem tailTrace_635456 : CollatzResearch.WordTrace tailWord_635456 prefixEnd_635456 326294362783571009177597 := by
  unfold tailWord_635456
  simp only [CollatzResearch.WordTrace]
  refine ⟨11588492192929457044807111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15451322923905942726409481 11588492192929457044807111)
  ·
    refine ⟨17382738289394185567210667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11588492192929457044807111 17382738289394185567210667)
    ·
      refine ⟨26074107434091278350816001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17382738289394185567210667 26074107434091278350816001)
      ·
        refine ⟨19555580575568458763112001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26074107434091278350816001 19555580575568458763112001)
        ·
          refine ⟨14666685431676344072334001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19555580575568458763112001 14666685431676344072334001)
          ·
            refine ⟨11000014073757258054250501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14666685431676344072334001 11000014073757258054250501)
            ·
              refine ⟨2062502638829485885171969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11000014073757258054250501 2062502638829485885171969)
              ·
                refine ⟨1546876979122114413878977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2062502638829485885171969 1546876979122114413878977)
                ·
                  refine ⟨1160157734341585810409233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1546876979122114413878977 1160157734341585810409233)
                  ·
                    refine ⟨870118300756189357806925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1160157734341585810409233 870118300756189357806925)
                    ·
                      refine ⟨326294362783571009177597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 870118300756189357806925 326294362783571009177597)
                      ·
                        rfl

theorem cell23_635456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_635456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635456 prefixEnd_635456 := by exact prefixLift 635456
  have htrace : WordTrace (prefixWord ++ tailWord_635456) baseStart_635456 baseEnd_635456 := by
    simpa [prefixWord, tailWord_635456, baseEnd_635456] using wordTrace_append hprefix tailTrace_635456
  have hstable : (prefixWord ++ tailWord_635456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635456).length < 2 ^ (prefixWord ++ tailWord_635456).sum := by decide
  have hdescent : baseEnd_635456 < baseStart_635456 := by decide
  rcases family_descends (prefixWord ++ tailWord_635456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635476 : List Nat := [2, 4, 1, 1, 1, 3, 2, 3, 6]
def baseStart_635476 : Nat := 118140960795 + 635476 * 2 ^ 59
def prefixEnd_635476 : Nat := 4983230072969 + 3 ^ 40 * 635476 * 2
def baseEnd_635476 : Nat := 36256070266295658991945

theorem tailTrace_635476 : CollatzResearch.WordTrace tailWord_635476 prefixEnd_635476 36256070266295658991945 := by
  unfold tailWord_635476
  simp only [CollatzResearch.WordTrace]
  refine ⟨11588856922893228752671141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15451809230524305003561521 11588856922893228752671141)
  ·
    refine ⟨2172910673042480391125839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11588856922893228752671141 2172910673042480391125839)
    ·
      refine ⟨3259366009563720586688759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2172910673042480391125839 3259366009563720586688759)
      ·
        refine ⟨4889049014345580880033139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3259366009563720586688759 4889049014345580880033139)
        ·
          refine ⟨7333573521518371320049709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4889049014345580880033139 7333573521518371320049709)
          ·
            refine ⟨2750090070569389245018641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7333573521518371320049709 2750090070569389245018641)
            ·
              refine ⟨2062567552927041933763981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2750090070569389245018641 2062567552927041933763981)
              ·
                refine ⟨773462832347640725161493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2062567552927041933763981 773462832347640725161493)
                ·
                  refine ⟨36256070266295658991945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 773462832347640725161493 36256070266295658991945)
                  ·
                    rfl

theorem cell23_635476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_635476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635476 prefixEnd_635476 := by exact prefixLift 635476
  have htrace : WordTrace (prefixWord ++ tailWord_635476) baseStart_635476 baseEnd_635476 := by
    simpa [prefixWord, tailWord_635476, baseEnd_635476] using wordTrace_append hprefix tailTrace_635476
  have hstable : (prefixWord ++ tailWord_635476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635476).length < 2 ^ (prefixWord ++ tailWord_635476).sum := by decide
  have hdescent : baseEnd_635476 < baseStart_635476 := by decide
  rcases family_descends (prefixWord ++ tailWord_635476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635490 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_635490 : Nat := 118140960795 + 635490 * 2 ^ 59
def prefixEnd_635490 : Nat := 4983230072969 + 3 ^ 40 * 635490 * 2
def baseEnd_635490 : Nat := 326311821125823876152441

theorem tailTrace_635490 : CollatzResearch.WordTrace tailWord_635490 prefixEnd_635490 326311821125823876152441 := by
  unfold tailWord_635490
  simp only [CollatzResearch.WordTrace]
  refine ⟨5794556116933934474087981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15452149645157158597567949 5794556116933934474087981)
  ·
    refine ⟨2172958543850225427782993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5794556116933934474087981 2172958543850225427782993)
    ·
      refine ⟨1629718907887669070837245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2172958543850225427782993 1629718907887669070837245)
      ·
        refine ⟨611144590457875901563967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1629718907887669070837245 611144590457875901563967)
        ·
          refine ⟨916716885686813852345951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611144590457875901563967 916716885686813852345951)
          ·
            refine ⟨1375075328530220778518927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916716885686813852345951 1375075328530220778518927)
            ·
              refine ⟨2062612992795331167778391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375075328530220778518927 2062612992795331167778391)
              ·
                refine ⟨3093919489192996751667587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062612992795331167778391 3093919489192996751667587)
                ·
                  refine ⟨4640879233789495127501381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3093919489192996751667587 4640879233789495127501381)
                  ·
                    refine ⟨870164856335530336406509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4640879233789495127501381 870164856335530336406509)
                    ·
                      refine ⟨326311821125823876152441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 870164856335530336406509 326311821125823876152441)
                      ·
                        rfl

theorem cell23_635490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_635490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635490 prefixEnd_635490 := by exact prefixLift 635490
  have htrace : WordTrace (prefixWord ++ tailWord_635490) baseStart_635490 baseEnd_635490 := by
    simpa [prefixWord, tailWord_635490, baseEnd_635490] using wordTrace_append hprefix tailTrace_635490
  have hstable : (prefixWord ++ tailWord_635490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635490).length < 2 ^ (prefixWord ++ tailWord_635490).sum := by decide
  have hdescent : baseEnd_635490 < baseStart_635490 := by decide
  rcases family_descends (prefixWord ++ tailWord_635490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635510 : List Nat := [5, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_635510 : Nat := 118140960795 + 635510 * 2 ^ 59
def prefixEnd_635510 : Nat := 4983230072969 + 3 ^ 40 * 635510 * 2
def baseEnd_635510 : Nat := 36258010082101533100261

theorem tailTrace_635510 : CollatzResearch.WordTrace tailWord_635510 prefixEnd_635510 36258010082101533100261 := by
  unfold tailWord_635510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1448684620478955082004999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15452635951775520874719989 1448684620478955082004999)
  ·
    refine ⟨2173026930718432623007499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1448684620478955082004999 2173026930718432623007499)
    ·
      refine ⟨3259540396077648934511249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2173026930718432623007499 3259540396077648934511249)
      ·
        refine ⟨2444655297058236700883437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3259540396077648934511249 2444655297058236700883437)
        ·
          refine ⟨916745736396838762831289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2444655297058236700883437 916745736396838762831289)
          ·
            refine ⟨687559302297629072123467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 916745736396838762831289 687559302297629072123467)
            ·
              refine ⟨1031338953446443608185201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687559302297629072123467 1031338953446443608185201)
              ·
                refine ⟨773504215084832706138901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1031338953446443608185201 773504215084832706138901)
                ·
                  refine ⟨36258010082101533100261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 773504215084832706138901 36258010082101533100261)
                  ·
                    rfl

theorem cell23_635510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_635510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635510 prefixEnd_635510 := by exact prefixLift 635510
  have htrace : WordTrace (prefixWord ++ tailWord_635510) baseStart_635510 baseEnd_635510 := by
    simpa [prefixWord, tailWord_635510, baseEnd_635510] using wordTrace_append hprefix tailTrace_635510
  have hstable : (prefixWord ++ tailWord_635510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635510).length < 2 ^ (prefixWord ++ tailWord_635510).sum := by decide
  have hdescent : baseEnd_635510 < baseStart_635510 := by decide
  rcases family_descends (prefixWord ++ tailWord_635510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635520 : List Nat := [2, 1, 1, 2, 1, 5, 2, 4, 1, 1, 3]
def baseStart_635520 : Nat := 118140960795 + 635520 * 2 ^ 59
def prefixEnd_635520 : Nat := 4983230072969 + 3 ^ 40 * 635520 * 2
def baseEnd_635520 : Nat := 326327225545458758777303

theorem tailTrace_635520 : CollatzResearch.WordTrace tailWord_635520 prefixEnd_635520 326327225545458758777303 := by
  unfold tailWord_635520
  simp only [CollatzResearch.WordTrace]
  refine ⟨11589659328813526509972007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15452879105084702013296009 11589659328813526509972007)
  ·
    refine ⟨17384488993220289764958011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11589659328813526509972007 17384488993220289764958011)
    ·
      refine ⟨26076733489830434647437017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17384488993220289764958011 26076733489830434647437017)
      ·
        refine ⟨19557550117372825985577763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26076733489830434647437017 19557550117372825985577763)
        ·
          refine ⟨29336325176059238978366645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19557550117372825985577763 29336325176059238978366645)
          ·
            refine ⟨2750280485255553654221873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29336325176059238978366645 2750280485255553654221873)
            ·
              refine ⟨2062710363941665240666405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2750280485255553654221873 2062710363941665240666405)
              ·
                refine ⟨386758193239062232624951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2062710363941665240666405 386758193239062232624951)
                ·
                  refine ⟨580137289858593348937427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386758193239062232624951 580137289858593348937427)
                  ·
                    refine ⟨870205934787890023406141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 580137289858593348937427 870205934787890023406141)
                    ·
                      refine ⟨326327225545458758777303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 870205934787890023406141 326327225545458758777303)
                      ·
                        rfl

theorem cell23_635520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 1, 1, 3].length) (baseStart_635520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635520 prefixEnd_635520 := by exact prefixLift 635520
  have htrace : WordTrace (prefixWord ++ tailWord_635520) baseStart_635520 baseEnd_635520 := by
    simpa [prefixWord, tailWord_635520, baseEnd_635520] using wordTrace_append hprefix tailTrace_635520
  have hstable : (prefixWord ++ tailWord_635520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635520).length < 2 ^ (prefixWord ++ tailWord_635520).sum := by decide
  have hdescent : baseEnd_635520 < baseStart_635520 := by decide
  rcases family_descends (prefixWord ++ tailWord_635520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635539 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 6]
def baseStart_635539 : Nat := 118140960795 + 635539 * 2 ^ 59
def prefixEnd_635539 : Nat := 4983230072969 + 3 ^ 40 * 635539 * 2
def baseEnd_635539 : Nat := 326336981677894184439715

theorem tailTrace_635539 : CollatzResearch.WordTrace tailWord_635539 prefixEnd_635539 326336981677894184439715 := by
  unfold tailWord_635539
  simp only [CollatzResearch.WordTrace]
  refine ⟨23180011644558219264885671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15453341096372146176590447 23180011644558219264885671)
  ·
    refine ⟨34770017466837328897328507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23180011644558219264885671 34770017466837328897328507)
    ·
      refine ⟨52155026200255993345992761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34770017466837328897328507 52155026200255993345992761)
      ·
        refine ⟨39116269650191995009494571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52155026200255993345992761 39116269650191995009494571)
        ·
          refine ⟨58674404475287992514241857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39116269650191995009494571 58674404475287992514241857)
          ·
            refine ⟨44005803356465994385681393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58674404475287992514241857 44005803356465994385681393)
            ·
              refine ⟨33004352517349495789261045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44005803356465994385681393 33004352517349495789261045)
              ·
                refine ⟨3094158048501515230243223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33004352517349495789261045 3094158048501515230243223)
                ·
                  refine ⟨4641237072752272845364835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094158048501515230243223 4641237072752272845364835)
                  ·
                    refine ⟨6961855609128409268047253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4641237072752272845364835 6961855609128409268047253)
                    ·
                      refine ⟨326336981677894184439715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6961855609128409268047253 326336981677894184439715)
                      ·
                        rfl

theorem cell23_635539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_635539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635539 prefixEnd_635539 := by exact prefixLift 635539
  have htrace : WordTrace (prefixWord ++ tailWord_635539) baseStart_635539 baseEnd_635539 := by
    simpa [prefixWord, tailWord_635539, baseEnd_635539] using wordTrace_append hprefix tailTrace_635539
  have hstable : (prefixWord ++ tailWord_635539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635539).length < 2 ^ (prefixWord ++ tailWord_635539).sum := by decide
  have hdescent : baseEnd_635539 < baseStart_635539 := by decide
  rcases family_descends (prefixWord ++ tailWord_635539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635540 : List Nat := [2, 4, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_635540 : Nat := 118140960795 + 635540 * 2 ^ 59
def prefixEnd_635540 : Nat := 4983230072969 + 3 ^ 40 * 635540 * 2
def baseEnd_635540 : Nat := 108779165052849560175737

theorem tailTrace_635540 : CollatzResearch.WordTrace tailWord_635540 prefixEnd_635540 108779165052849560175737 := by
  unfold tailWord_635540
  simp only [CollatzResearch.WordTrace]
  refine ⟨11590024058777298217836037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15453365411703064290448049 11590024058777298217836037)
  ·
    refine ⟨2173129511020743415844257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11590024058777298217836037 2173129511020743415844257)
    ·
      refine ⟨1629847133265557561883193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2173129511020743415844257 1629847133265557561883193)
      ·
        refine ⟨1222385349949168171412395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1629847133265557561883193 1222385349949168171412395)
        ·
          refine ⟨1833578024923752257118593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222385349949168171412395 1833578024923752257118593)
          ·
            refine ⟨1375183518692814192838945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1833578024923752257118593 1375183518692814192838945)
            ·
              refine ⟨1031387639019610644629209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1375183518692814192838945 1031387639019610644629209)
              ·
                refine ⟨773540729264707983471907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1031387639019610644629209 773540729264707983471907)
                ·
                  refine ⟨1160311093897061975207861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773540729264707983471907 1160311093897061975207861)
                  ·
                    refine ⟨108779165052849560175737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1160311093897061975207861 108779165052849560175737)
                    ·
                      rfl

theorem cell23_635540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_635540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635540 prefixEnd_635540 := by exact prefixLift 635540
  have htrace : WordTrace (prefixWord ++ tailWord_635540) baseStart_635540 baseEnd_635540 := by
    simpa [prefixWord, tailWord_635540, baseEnd_635540] using wordTrace_append hprefix tailTrace_635540
  have hstable : (prefixWord ++ tailWord_635540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635540).length < 2 ^ (prefixWord ++ tailWord_635540).sum := by decide
  have hdescent : baseEnd_635540 < baseStart_635540 := by decide
  rcases family_descends (prefixWord ++ tailWord_635540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635543 : List Nat := [1, 1, 3, 3, 2, 1, 4, 2, 1, 1, 4]
def baseStart_635543 : Nat := 118140960795 + 635543 * 2 ^ 59
def prefixEnd_635543 : Nat := 4983230072969 + 3 ^ 40 * 635543 * 2
def baseEnd_635543 : Nat := 326339035600512168789697

theorem tailTrace_635543 : CollatzResearch.WordTrace tailWord_635543 prefixEnd_635543 326339035600512168789697 := by
  unfold tailWord_635543
  simp only [CollatzResearch.WordTrace]
  refine ⟨23180157536543727948031283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15453438357695818632020855 23180157536543727948031283)
  ·
    refine ⟨34770236304815591922046925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23180157536543727948031283 34770236304815591922046925)
    ·
      refine ⟨13038838614305846970767597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34770236304815591922046925 13038838614305846970767597)
      ·
        refine ⟨4889564480364692614037849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13038838614305846970767597 4889564480364692614037849)
        ·
          refine ⟨3667173360273519460528387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4889564480364692614037849 3667173360273519460528387)
          ·
            refine ⟨5500760040410279190792581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3667173360273519460528387 5500760040410279190792581)
            ·
              refine ⟨1031392507576927348273609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5500760040410279190792581 1031392507576927348273609)
              ·
                refine ⟨773544380682695511205207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1031392507576927348273609 773544380682695511205207)
                ·
                  refine ⟨1160316571024043266807811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773544380682695511205207 1160316571024043266807811)
                  ·
                    refine ⟨1740474856536064900211717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1160316571024043266807811 1740474856536064900211717)
                    ·
                      refine ⟨326339035600512168789697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1740474856536064900211717 326339035600512168789697)
                      ·
                        rfl

theorem cell23_635543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_635543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635543 prefixEnd_635543 := by exact prefixLift 635543
  have htrace : WordTrace (prefixWord ++ tailWord_635543) baseStart_635543 baseEnd_635543 := by
    simpa [prefixWord, tailWord_635543, baseEnd_635543] using wordTrace_append hprefix tailTrace_635543
  have hstable : (prefixWord ++ tailWord_635543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635543).length < 2 ^ (prefixWord ++ tailWord_635543).sum := by decide
  have hdescent : baseEnd_635543 < baseStart_635543 := by decide
  rcases family_descends (prefixWord ++ tailWord_635543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635556 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_635556 : Nat := 118140960795 + 635556 * 2 ^ 59
def prefixEnd_635556 : Nat := 4983230072969 + 3 ^ 40 * 635556 * 2
def baseEnd_635556 : Nat := 326345710849020617927137

theorem tailTrace_635556 : CollatzResearch.WordTrace tailWord_635556 prefixEnd_635556 326345710849020617927137 := by
  unfold tailWord_635556
  simp only [CollatzResearch.WordTrace]
  refine ⟨11590315842748315584127261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15453754456997754112169681 11590315842748315584127261)
  ·
    refine ⟨4346368441030618344047723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11590315842748315584127261 4346368441030618344047723)
    ·
      refine ⟨6519552661545927516071585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4346368441030618344047723 6519552661545927516071585)
      ·
        refine ⟨4889664496159445637053689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6519552661545927516071585 4889664496159445637053689)
        ·
          refine ⟨3667248372119584227790267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4889664496159445637053689 3667248372119584227790267)
          ·
            refine ⟨5500872558179376341685401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3667248372119584227790267 5500872558179376341685401)
            ·
              refine ⟨4125654418634532256264051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5500872558179376341685401 4125654418634532256264051)
              ·
                refine ⟨6188481627951798384396077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4125654418634532256264051 6188481627951798384396077)
                ·
                  refine ⟨2320680610481924394148529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6188481627951798384396077 2320680610481924394148529)
                  ·
                    refine ⟨1740510457861443295611397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2320680610481924394148529 1740510457861443295611397)
                    ·
                      refine ⟨326345710849020617927137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1740510457861443295611397 326345710849020617927137)
                      ·
                        rfl

theorem cell23_635556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_635556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635556 prefixEnd_635556 := by exact prefixLift 635556
  have htrace : WordTrace (prefixWord ++ tailWord_635556) baseStart_635556 baseEnd_635556 := by
    simpa [prefixWord, tailWord_635556, baseEnd_635556] using wordTrace_append hprefix tailTrace_635556
  have hstable : (prefixWord ++ tailWord_635556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635556).length < 2 ^ (prefixWord ++ tailWord_635556).sum := by decide
  have hdescent : baseEnd_635556 < baseStart_635556 := by decide
  rcases family_descends (prefixWord ++ tailWord_635556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635597 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_635597 : Nat := 118140960795 + 635597 * 2 ^ 59
def prefixEnd_635597 : Nat := 4983230072969 + 3 ^ 40 * 635597 * 2
def baseEnd_635597 : Nat := 326366763555854957514449

theorem tailTrace_635597 : CollatzResearch.WordTrace tailWord_635597 prefixEnd_635597 326366763555854957514449 := by
  unfold tailWord_635597
  simp only [CollatzResearch.WordTrace]
  refine ⟨23182127078348095170497045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15454751385565396780331363 23182127078348095170497045)
  ·
    refine ⟨1086662206797566961117049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23182127078348095170497045 1086662206797566961117049)
    ·
      refine ⟨814996655098175220837787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1086662206797566961117049 814996655098175220837787)
      ·
        refine ⟨1222494982647262831256681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814996655098175220837787 1222494982647262831256681)
        ·
          refine ⟨916871236985447123442511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1222494982647262831256681 916871236985447123442511)
          ·
            refine ⟨1375306855478170685163767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916871236985447123442511 1375306855478170685163767)
            ·
              refine ⟨2062960283217256027745651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375306855478170685163767 2062960283217256027745651)
              ·
                refine ⟨3094440424825884041618477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062960283217256027745651 3094440424825884041618477)
                ·
                  refine ⟨1160415159309706515606929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3094440424825884041618477 1160415159309706515606929)
                  ·
                    refine ⟨870311369482279886705197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1160415159309706515606929 870311369482279886705197)
                    ·
                      refine ⟨326366763555854957514449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 870311369482279886705197 326366763555854957514449)
                      ·
                        rfl

theorem cell23_635597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_635597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635597 prefixEnd_635597 := by exact prefixLift 635597
  have htrace : WordTrace (prefixWord ++ tailWord_635597) baseStart_635597 baseEnd_635597 := by
    simpa [prefixWord, tailWord_635597, baseEnd_635597] using wordTrace_append hprefix tailTrace_635597
  have hstable : (prefixWord ++ tailWord_635597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635597).length < 2 ^ (prefixWord ++ tailWord_635597).sum := by decide
  have hdescent : baseEnd_635597 < baseStart_635597 := by decide
  rcases family_descends (prefixWord ++ tailWord_635597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635599 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 10]
def baseStart_635599 : Nat := 118140960795 + 635599 * 2 ^ 59
def prefixEnd_635599 : Nat := 4983230072969 + 3 ^ 40 * 635599 * 2
def baseEnd_635599 : Nat := 326367790517163949689439

theorem tailTrace_635599 : CollatzResearch.WordTrace tailWord_635599 prefixEnd_635599 326367790517163949689439 := by
  unfold tailWord_635599
  simp only [CollatzResearch.WordTrace]
  refine ⟨23182200024340849512069851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15454800016227233008046567 23182200024340849512069851)
  ·
    refine ⟨34773300036511274268104777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23182200024340849512069851 34773300036511274268104777)
    ·
      refine ⟨26079975027383455701078583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34773300036511274268104777 26079975027383455701078583)
      ·
        refine ⟨39119962541075183551617875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26079975027383455701078583 39119962541075183551617875)
        ·
          refine ⟨58679943811612775327426813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39119962541075183551617875 58679943811612775327426813)
          ·
            refine ⟨22004978929354790747785055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58679943811612775327426813 22004978929354790747785055)
            ·
              refine ⟨33007468394032186121677583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22004978929354790747785055 33007468394032186121677583)
              ·
                refine ⟨49511202591048279182516375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33007468394032186121677583 49511202591048279182516375)
                ·
                  refine ⟨74266803886572418773774563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49511202591048279182516375 74266803886572418773774563)
                  ·
                    refine ⟨111400205829858628160661845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74266803886572418773774563 111400205829858628160661845)
                    ·
                      refine ⟨326367790517163949689439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 111400205829858628160661845 326367790517163949689439)
                      ·
                        rfl

theorem cell23_635599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_635599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635599 prefixEnd_635599 := by exact prefixLift 635599
  have htrace : WordTrace (prefixWord ++ tailWord_635599) baseStart_635599 baseEnd_635599 := by
    simpa [prefixWord, tailWord_635599, baseEnd_635599] using wordTrace_append hprefix tailTrace_635599
  have hstable : (prefixWord ++ tailWord_635599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635599).length < 2 ^ (prefixWord ++ tailWord_635599).sum := by decide
  have hdescent : baseEnd_635599 < baseStart_635599 := by decide
  rcases family_descends (prefixWord ++ tailWord_635599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635626 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 2, 6]
def baseStart_635626 : Nat := 118140960795 + 635626 * 2 ^ 59
def prefixEnd_635626 : Nat := 4983230072969 + 3 ^ 40 * 635626 * 2
def baseEnd_635626 : Nat := 108793884831611781350605

theorem tailTrace_635626 : CollatzResearch.WordTrace tailWord_635626 prefixEnd_635626 108793884831611781350605 := by
  unfold tailWord_635626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5795796198810758280825683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15455456530162022082201821 5795796198810758280825683)
  ·
    refine ⟨8693694298216137421238525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5795796198810758280825683 8693694298216137421238525)
    ·
      refine ⟨3260135361831051532964447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8693694298216137421238525 3260135361831051532964447)
      ·
        refine ⟨4890203042746577299446671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3260135361831051532964447 4890203042746577299446671)
        ·
          refine ⟨7335304564119865949170007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4890203042746577299446671 7335304564119865949170007)
          ·
            refine ⟨11002956846179798923755011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7335304564119865949170007 11002956846179798923755011)
            ·
              refine ⟨16504435269269698385632517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11002956846179798923755011 16504435269269698385632517)
              ·
                refine ⟨3094581612988068447306097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16504435269269698385632517 3094581612988068447306097)
                ·
                  refine ⟨2320936209741051335479573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3094581612988068447306097 2320936209741051335479573)
                  ·
                    refine ⟨108793884831611781350605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2320936209741051335479573 108793884831611781350605)
                    ·
                      rfl

theorem cell23_635626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_635626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635626 prefixEnd_635626 := by exact prefixLift 635626
  have htrace : WordTrace (prefixWord ++ tailWord_635626) baseStart_635626 baseEnd_635626 := by
    simpa [prefixWord, tailWord_635626, baseEnd_635626] using wordTrace_append hprefix tailTrace_635626
  have hstable : (prefixWord ++ tailWord_635626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635626).length < 2 ^ (prefixWord ++ tailWord_635626).sum := by decide
  have hdescent : baseEnd_635626 < baseStart_635626 := by decide
  rcases family_descends (prefixWord ++ tailWord_635626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635633 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 3, 4, 2]
def baseStart_635633 : Nat := 118140960795 + 635633 * 2 ^ 59
def prefixEnd_635633 : Nat := 4983230072969 + 3 ^ 40 * 635633 * 2
def baseEnd_635633 : Nat := 326385248859416816664283

theorem tailTrace_635633 : CollatzResearch.WordTrace tailWord_635633 prefixEnd_635633 326385248859416816664283 := by
  unfold tailWord_635633
  simp only [CollatzResearch.WordTrace]
  refine ⟨23183440106217673318807553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15455626737478448879205035 23183440106217673318807553)
  ·
    refine ⟨17387580079663254989105665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23183440106217673318807553 17387580079663254989105665)
    ·
      refine ⟨13040685059747441241829249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17387580079663254989105665 13040685059747441241829249)
      ·
        refine ⟨9780513794810580931371937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13040685059747441241829249 9780513794810580931371937)
        ·
          refine ⟨7335385346107935698528953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9780513794810580931371937 7335385346107935698528953)
          ·
            refine ⟨5501539009580951773896715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7335385346107935698528953 5501539009580951773896715)
            ·
              refine ⟨8252308514371427660845073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5501539009580951773896715 8252308514371427660845073)
              ·
                refine ⟨6189231385778570745633805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8252308514371427660845073 6189231385778570745633805)
                ·
                  refine ⟨2320961769666964029612677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6189231385778570745633805 2320961769666964029612677)
                  ·
                    refine ⟨435180331812555755552377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2320961769666964029612677 435180331812555755552377)
                    ·
                      refine ⟨326385248859416816664283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 435180331812555755552377 326385248859416816664283)
                      ·
                        rfl

theorem cell23_635633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_635633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635633 prefixEnd_635633 := by exact prefixLift 635633
  have htrace : WordTrace (prefixWord ++ tailWord_635633) baseStart_635633 baseEnd_635633 := by
    simpa [prefixWord, tailWord_635633, baseEnd_635633] using wordTrace_append hprefix tailTrace_635633
  have hstable : (prefixWord ++ tailWord_635633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635633).length < 2 ^ (prefixWord ++ tailWord_635633).sum := by decide
  have hdescent : baseEnd_635633 < baseStart_635633 := by decide
  rcases family_descends (prefixWord ++ tailWord_635633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635656 : List Nat := [2, 1, 3, 2, 2, 2, 1, 1, 9]
def baseStart_635656 : Nat := 118140960795 + 635656 * 2 ^ 59
def prefixEnd_635656 : Nat := 4983230072969 + 3 ^ 40 * 635656 * 2
def baseEnd_635656 : Nat := 36266339879385580741853

theorem tailTrace_635656 : CollatzResearch.WordTrace tailWord_635656 prefixEnd_635656 36266339879385580741853 := by
  unfold tailWord_635656
  simp only [CollatzResearch.WordTrace]
  refine ⟨11592139492567174123447411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15456185990089565497929881 11592139492567174123447411)
  ·
    refine ⟨17388209238850761185171117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11592139492567174123447411 17388209238850761185171117)
    ·
      refine ⟨6520578464569035444439169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17388209238850761185171117 6520578464569035444439169)
      ·
        refine ⟨4890433848426776583329377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6520578464569035444439169 4890433848426776583329377)
        ·
          refine ⟨3667825386320082437497033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4890433848426776583329377 3667825386320082437497033)
          ·
            refine ⟨2750869039740061828122775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3667825386320082437497033 2750869039740061828122775)
            ·
              refine ⟨4126303559610092742184163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2750869039740061828122775 4126303559610092742184163)
              ·
                refine ⟨6189455339415139113276245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4126303559610092742184163 6189455339415139113276245)
                ·
                  refine ⟨36266339879385580741853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6189455339415139113276245 36266339879385580741853)
                  ·
                    rfl

theorem cell23_635656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 9].length) (baseStart_635656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635656 prefixEnd_635656 := by exact prefixLift 635656
  have htrace : WordTrace (prefixWord ++ tailWord_635656) baseStart_635656 baseEnd_635656 := by
    simpa [prefixWord, tailWord_635656, baseEnd_635656] using wordTrace_append hprefix tailTrace_635656
  have hstable : (prefixWord ++ tailWord_635656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635656).length < 2 ^ (prefixWord ++ tailWord_635656).sum := by decide
  have hdescent : baseEnd_635656 < baseStart_635656 := by decide
  rcases family_descends (prefixWord ++ tailWord_635656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635671 : List Nat := [1, 1, 3, 4, 4, 1, 2, 1, 1, 3, 2]
def baseStart_635671 : Nat := 118140960795 + 635671 * 2 ^ 59
def prefixEnd_635671 : Nat := 4983230072969 + 3 ^ 40 * 635671 * 2
def baseEnd_635671 : Nat := 326404761124287667989109

theorem tailTrace_635671 : CollatzResearch.WordTrace tailWord_635671 prefixEnd_635671 326404761124287667989109 := by
  unfold tailWord_635671
  simp only [CollatzResearch.WordTrace]
  refine ⟨23184826080080005808690867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15456550720053337205793911 23184826080080005808690867)
  ·
    refine ⟨34777239120120008713036301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23184826080080005808690867 34777239120120008713036301)
    ·
      refine ⟨13041464670045003267388613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34777239120120008713036301 13041464670045003267388613)
      ·
        refine ⟨2445274625633438112635365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13041464670045003267388613 2445274625633438112635365)
        ·
          refine ⟨458488992306269646119131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2445274625633438112635365 458488992306269646119131)
          ·
            refine ⟨687733488459404469178697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458488992306269646119131 687733488459404469178697)
            ·
              refine ⟨515800116344553351884023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687733488459404469178697 515800116344553351884023)
              ·
                refine ⟨773700174516830027826035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515800116344553351884023 773700174516830027826035)
                ·
                  refine ⟨1160550261775245041739053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773700174516830027826035 1160550261775245041739053)
                  ·
                    refine ⟨435206348165716890652145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1160550261775245041739053 435206348165716890652145)
                    ·
                      refine ⟨326404761124287667989109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 435206348165716890652145 326404761124287667989109)
                      ·
                        rfl

theorem cell23_635671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_635671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635671 prefixEnd_635671 := by exact prefixLift 635671
  have htrace : WordTrace (prefixWord ++ tailWord_635671) baseStart_635671 baseEnd_635671 := by
    simpa [prefixWord, tailWord_635671, baseEnd_635671] using wordTrace_append hprefix tailTrace_635671
  have hstable : (prefixWord ++ tailWord_635671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635671).length < 2 ^ (prefixWord ++ tailWord_635671).sum := by decide
  have hdescent : baseEnd_635671 < baseStart_635671 := by decide
  rcases family_descends (prefixWord ++ tailWord_635671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635696 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 5]
def baseStart_635696 : Nat := 118140960795 + 635696 * 2 ^ 59
def prefixEnd_635696 : Nat := 4983230072969 + 3 ^ 40 * 635696 * 2
def baseEnd_635696 : Nat := 326417598140650070176493

theorem tailTrace_635696 : CollatzResearch.WordTrace tailWord_635696 prefixEnd_635696 326417598140650070176493 := by
  unfold tailWord_635696
  simp only [CollatzResearch.WordTrace]
  refine ⟨11592868952494717539175471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15457158603326290052233961 11592868952494717539175471)
  ·
    refine ⟨17389303428742076308763207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11592868952494717539175471 17389303428742076308763207)
    ·
      refine ⟨26083955143113114463144811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17389303428742076308763207 26083955143113114463144811)
      ·
        refine ⟨39125932714669671694717217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26083955143113114463144811 39125932714669671694717217)
        ·
          refine ⟨29344449536002253771037913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39125932714669671694717217 29344449536002253771037913)
          ·
            refine ⟨22008337152001690328278435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29344449536002253771037913 22008337152001690328278435)
            ·
              refine ⟨33012505728002535492417653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22008337152001690328278435 33012505728002535492417653)
              ·
                refine ⟨3094922412000237702414155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33012505728002535492417653 3094922412000237702414155)
                ·
                  refine ⟨4642383618000356553621233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094922412000237702414155 4642383618000356553621233)
                  ·
                    refine ⟨3481787713500267415215925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4642383618000356553621233 3481787713500267415215925)
                    ·
                      refine ⟨326417598140650070176493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3481787713500267415215925 326417598140650070176493)
                      ·
                        rfl

theorem cell23_635696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_635696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635696 prefixEnd_635696 := by exact prefixLift 635696
  have htrace : WordTrace (prefixWord ++ tailWord_635696) baseStart_635696 baseEnd_635696 := by
    simpa [prefixWord, tailWord_635696, baseEnd_635696] using wordTrace_append hprefix tailTrace_635696
  have hstable : (prefixWord ++ tailWord_635696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635696).length < 2 ^ (prefixWord ++ tailWord_635696).sum := by decide
  have hdescent : baseEnd_635696 < baseStart_635696 := by decide
  rcases family_descends (prefixWord ++ tailWord_635696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635736 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_635736 : Nat := 118140960795 + 635736 * 2 ^ 59
def prefixEnd_635736 : Nat := 4983230072969 + 3 ^ 40 * 635736 * 2
def baseEnd_635736 : Nat := 326438137366829913676309

theorem tailTrace_635736 : CollatzResearch.WordTrace tailWord_635736 prefixEnd_635736 326438137366829913676309 := by
  unfold tailWord_635736
  simp only [CollatzResearch.WordTrace]
  refine ⟨11593598412422260954903531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15458131216563014606538041 11593598412422260954903531)
  ·
    refine ⟨17390397618633391432355297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11593598412422260954903531 17390397618633391432355297)
    ·
      refine ⟨13042798213975043574266473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17390397618633391432355297 13042798213975043574266473)
      ·
        refine ⟨9782098660481282680699855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13042798213975043574266473 9782098660481282680699855)
        ·
          refine ⟨14673147990721924021049783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9782098660481282680699855 14673147990721924021049783)
          ·
            refine ⟨22009721986082886031574675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14673147990721924021049783 22009721986082886031574675)
            ·
              refine ⟨33014582979124329047362013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22009721986082886031574675 33014582979124329047362013)
              ·
                refine ⟨12380468617171623392760755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33014582979124329047362013 12380468617171623392760755)
                ·
                  refine ⟨18570702925757435089141133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12380468617171623392760755 18570702925757435089141133)
                  ·
                    refine ⟨6964013597159038158427925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18570702925757435089141133 6964013597159038158427925)
                    ·
                      refine ⟨326438137366829913676309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6964013597159038158427925 326438137366829913676309)
                      ·
                        rfl

theorem cell23_635736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_635736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635736 prefixEnd_635736 := by exact prefixLift 635736
  have htrace : WordTrace (prefixWord ++ tailWord_635736) baseStart_635736 baseEnd_635736 := by
    simpa [prefixWord, tailWord_635736, baseEnd_635736] using wordTrace_append hprefix tailTrace_635736
  have hstable : (prefixWord ++ tailWord_635736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635736).length < 2 ^ (prefixWord ++ tailWord_635736).sum := by decide
  have hdescent : baseEnd_635736 < baseStart_635736 := by decide
  rcases family_descends (prefixWord ++ tailWord_635736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635740 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_635740 : Nat := 118140960795 + 635740 * 2 ^ 59
def prefixEnd_635740 : Nat := 4983230072969 + 3 ^ 40 * 635740 * 2
def baseEnd_635740 : Nat := 326440191289447898026291

theorem tailTrace_635740 : CollatzResearch.WordTrace tailWord_635740 prefixEnd_635740 326440191289447898026291 := by
  unfold tailWord_635740
  simp only [CollatzResearch.WordTrace]
  refine ⟨11593671358415015296476337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15458228477886687061968449 11593671358415015296476337)
  ·
    refine ⟨8695253518811261472357253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11593671358415015296476337 8695253518811261472357253)
    ·
      refine ⟨1630360034777111526066985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8695253518811261472357253 1630360034777111526066985)
      ·
        refine ⟨1222770026082833644550239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1630360034777111526066985 1222770026082833644550239)
        ·
          refine ⟨1834155039124250466825359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222770026082833644550239 1834155039124250466825359)
          ·
            refine ⟨2751232558686375700238039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834155039124250466825359 2751232558686375700238039)
            ·
              refine ⟨4126848838029563550357059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751232558686375700238039 4126848838029563550357059)
              ·
                refine ⟨6190273257044345325535589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4126848838029563550357059 6190273257044345325535589)
                ·
                  refine ⟨1160676235695814748537923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6190273257044345325535589 1160676235695814748537923)
                  ·
                    refine ⟨1741014353543722122806885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1160676235695814748537923 1741014353543722122806885)
                    ·
                      refine ⟨326440191289447898026291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1741014353543722122806885 326440191289447898026291)
                      ·
                        rfl

theorem cell23_635740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_635740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635740 prefixEnd_635740 := by exact prefixLift 635740
  have htrace : WordTrace (prefixWord ++ tailWord_635740) baseStart_635740 baseEnd_635740 := by
    simpa [prefixWord, tailWord_635740, baseEnd_635740] using wordTrace_append hprefix tailTrace_635740
  have hstable : (prefixWord ++ tailWord_635740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635740).length < 2 ^ (prefixWord ++ tailWord_635740).sum := by decide
  have hdescent : baseEnd_635740 < baseStart_635740 := by decide
  rcases family_descends (prefixWord ++ tailWord_635740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635773 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_635773 : Nat := 118140960795 + 635773 * 2 ^ 59
def prefixEnd_635773 : Nat := 4983230072969 + 3 ^ 40 * 635773 * 2
def baseEnd_635773 : Nat := 326457136151046268913639

theorem tailTrace_635773 : CollatzResearch.WordTrace tailWord_635773 prefixEnd_635773 326457136151046268913639 := by
  unfold tailWord_635773
  simp only [CollatzResearch.WordTrace]
  refine ⟨23188546325710477228903973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15459030883806984819269315 23188546325710477228903973)
  ·
    refine ⟨4347852436070714480419495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23188546325710477228903973 4347852436070714480419495)
    ·
      refine ⟨6521778654106071720629243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4347852436070714480419495 6521778654106071720629243)
      ·
        refine ⟨9782667981159107580943865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6521778654106071720629243 9782667981159107580943865)
        ·
          refine ⟨7337000985869330685707899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9782667981159107580943865 7337000985869330685707899)
          ·
            refine ⟨11005501478803996028561849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7337000985869330685707899 11005501478803996028561849)
            ·
              refine ⟨8254126109102997021421387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11005501478803996028561849 8254126109102997021421387)
              ·
                refine ⟨12381189163654495532132081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8254126109102997021421387 12381189163654495532132081)
                ·
                  refine ⟨9285891872740871649099061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12381189163654495532132081 9285891872740871649099061)
                  ·
                    refine ⟨870552363069456717103037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9285891872740871649099061 870552363069456717103037)
                    ·
                      refine ⟨326457136151046268913639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 870552363069456717103037 326457136151046268913639)
                      ·
                        rfl

theorem cell23_635773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_635773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635773 prefixEnd_635773 := by exact prefixLift 635773
  have htrace : WordTrace (prefixWord ++ tailWord_635773) baseStart_635773 baseEnd_635773 := by
    simpa [prefixWord, tailWord_635773, baseEnd_635773] using wordTrace_append hprefix tailTrace_635773
  have hstable : (prefixWord ++ tailWord_635773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635773).length < 2 ^ (prefixWord ++ tailWord_635773).sum := by decide
  have hdescent : baseEnd_635773 < baseStart_635773 := by decide
  rcases family_descends (prefixWord ++ tailWord_635773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635774 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_635774 : Nat := 118140960795 + 635774 * 2 ^ 59
def prefixEnd_635774 : Nat := 4983230072969 + 3 ^ 40 * 635774 * 2
def baseEnd_635774 : Nat := 326457649631700765001135

theorem tailTrace_635774 : CollatzResearch.WordTrace tailWord_635774 prefixEnd_635774 326457649631700765001135 := by
  unfold tailWord_635774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2898572849838356799961297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15459055199137902933126917 2898572849838356799961297)
  ·
    refine ⟨2173929637378767599970973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2898572849838356799961297 2173929637378767599970973)
    ·
      refine ⟨815223614017037849989115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2173929637378767599970973 815223614017037849989115)
      ·
        refine ⟨1222835421025556774983673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815223614017037849989115 1222835421025556774983673)
        ·
          refine ⟨917126565769167581237755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1222835421025556774983673 917126565769167581237755)
          ·
            refine ⟨1375689848653751371856633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917126565769167581237755 1375689848653751371856633)
            ·
              refine ⟨1031767386490313528892475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1375689848653751371856633 1031767386490313528892475)
              ·
                refine ⟨1547651079735470293338713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031767386490313528892475 1547651079735470293338713)
                ·
                  refine ⟨1160738309801602720004035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1547651079735470293338713 1160738309801602720004035)
                  ·
                    refine ⟨1741107464702404080006053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1160738309801602720004035 1741107464702404080006053)
                    ·
                      refine ⟨326457649631700765001135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1741107464702404080006053 326457649631700765001135)
                      ·
                        rfl

theorem cell23_635774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_635774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635774 prefixEnd_635774 := by exact prefixLift 635774
  have htrace : WordTrace (prefixWord ++ tailWord_635774) baseStart_635774 baseEnd_635774 := by
    simpa [prefixWord, tailWord_635774, baseEnd_635774] using wordTrace_append hprefix tailTrace_635774
  have hstable : (prefixWord ++ tailWord_635774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635774).length < 2 ^ (prefixWord ++ tailWord_635774).sum := by decide
  have hdescent : baseEnd_635774 < baseStart_635774 := by decide
  rcases family_descends (prefixWord ++ tailWord_635774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635810 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_635810 : Nat := 118140960795 + 635810 * 2 ^ 59
def prefixEnd_635810 : Nat := 4983230072969 + 3 ^ 40 * 635810 * 2
def baseEnd_635810 : Nat := 108825378311754208050323

theorem tailTrace_635810 : CollatzResearch.WordTrace tailWord_635810 prefixEnd_635810 108825378311754208050323 := by
  unfold tailWord_635810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5797473956644108137000221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15459930551050955032000589 5797473956644108137000221)
  ·
    refine ⟨2174052733741540551375083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5797473956644108137000221 2174052733741540551375083)
    ·
      refine ⟨3261079100612310827062625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2174052733741540551375083 3261079100612310827062625)
      ·
        refine ⟨2445809325459233120296969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3261079100612310827062625 2445809325459233120296969)
        ·
          refine ⟨1834356994094424840222727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2445809325459233120296969 1834356994094424840222727)
          ·
            refine ⟨2751535491141637260334091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834356994094424840222727 2751535491141637260334091)
            ·
              refine ⟨4127303236712455890501137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751535491141637260334091 4127303236712455890501137)
              ·
                refine ⟨3095477427534341917875853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4127303236712455890501137 3095477427534341917875853)
                ·
                  refine ⟨1160804035325378219203445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3095477427534341917875853 1160804035325378219203445)
                  ·
                    refine ⟨108825378311754208050323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1160804035325378219203445 108825378311754208050323)
                    ·
                      rfl

theorem cell23_635810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_635810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635810 prefixEnd_635810 := by exact prefixLift 635810
  have htrace : WordTrace (prefixWord ++ tailWord_635810) baseStart_635810 baseEnd_635810 := by
    simpa [prefixWord, tailWord_635810, baseEnd_635810] using wordTrace_append hprefix tailTrace_635810
  have hstable : (prefixWord ++ tailWord_635810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635810).length < 2 ^ (prefixWord ++ tailWord_635810).sum := by decide
  have hdescent : baseEnd_635810 < baseStart_635810 := by decide
  rcases family_descends (prefixWord ++ tailWord_635810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635844 : List Nat := [2, 3, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_635844 : Nat := 118140960795 + 635844 * 2 ^ 59
def prefixEnd_635844 : Nat := 4983230072969 + 3 ^ 40 * 635844 * 2
def baseEnd_635844 : Nat := 108831197759171830375271

theorem tailTrace_635844 : CollatzResearch.WordTrace tailWord_635844 prefixEnd_635844 108831197759171830375271 := by
  unfold tailWord_635844
  simp only [CollatzResearch.WordTrace]
  refine ⟨11595567954226628177369293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15460757272302170903159057 11595567954226628177369293)
  ·
    refine ⟨4348337982834985566513485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11595567954226628177369293 4348337982834985566513485)
    ·
      refine ⟨1630626743563119587442557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4348337982834985566513485 1630626743563119587442557)
      ·
        refine ⟨611485028836169845290959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1630626743563119587442557 611485028836169845290959)
        ·
          refine ⟨917227543254254767936439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611485028836169845290959 917227543254254767936439)
          ·
            refine ⟨1375841314881382151904659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917227543254254767936439 1375841314881382151904659)
            ·
              refine ⟨2063761972322073227856989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375841314881382151904659 2063761972322073227856989)
              ·
                refine ⟨773910739620777460446371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2063761972322073227856989 773910739620777460446371)
                ·
                  refine ⟨1160866109431166190669557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773910739620777460446371 1160866109431166190669557)
                  ·
                    refine ⟨108831197759171830375271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1160866109431166190669557 108831197759171830375271)
                    ·
                      rfl

theorem cell23_635844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_635844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635844 prefixEnd_635844 := by exact prefixLift 635844
  have htrace : WordTrace (prefixWord ++ tailWord_635844) baseStart_635844 baseEnd_635844 := by
    simpa [prefixWord, tailWord_635844, baseEnd_635844] using wordTrace_append hprefix tailTrace_635844
  have hstable : (prefixWord ++ tailWord_635844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635844).length < 2 ^ (prefixWord ++ tailWord_635844).sum := by decide
  have hdescent : baseEnd_635844 < baseStart_635844 := by decide
  rcases family_descends (prefixWord ++ tailWord_635844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635847 : List Nat := [1, 1, 4, 1, 1, 2, 6, 1, 1, 1, 4]
def baseStart_635847 : Nat := 118140960795 + 635847 * 2 ^ 59
def prefixEnd_635847 : Nat := 4983230072969 + 3 ^ 40 * 635847 * 2
def baseEnd_635847 : Nat := 326495133719478979388299

theorem tailTrace_635847 : CollatzResearch.WordTrace tailWord_635847 prefixEnd_635847 326495133719478979388299 := by
  unfold tailWord_635847
  simp only [CollatzResearch.WordTrace]
  refine ⟨23191245327442387867097795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15460830218294925244731863 23191245327442387867097795)
  ·
    refine ⟨34786867991163581800646693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23191245327442387867097795 34786867991163581800646693)
    ·
      refine ⟨6522537748343171587621255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34786867991163581800646693 6522537748343171587621255)
      ·
        refine ⟨9783806622514757381431883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6522537748343171587621255 9783806622514757381431883)
        ·
          refine ⟨14675709933772136072147825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9783806622514757381431883 14675709933772136072147825)
          ·
            refine ⟨11006782450329102054110869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14675709933772136072147825 11006782450329102054110869)
            ·
              refine ⟨515942927359176658786447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11006782450329102054110869 515942927359176658786447)
              ·
                refine ⟨773914391038764988179671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515942927359176658786447 773914391038764988179671)
                ·
                  refine ⟨1160871586558147482269507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 773914391038764988179671 1160871586558147482269507)
                  ·
                    refine ⟨1741307379837221223404261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1160871586558147482269507 1741307379837221223404261)
                    ·
                      refine ⟨326495133719478979388299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1741307379837221223404261 326495133719478979388299)
                      ·
                        rfl

theorem cell23_635847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_635847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635847 prefixEnd_635847 := by exact prefixLift 635847
  have htrace : WordTrace (prefixWord ++ tailWord_635847) baseStart_635847 baseEnd_635847 := by
    simpa [prefixWord, tailWord_635847, baseEnd_635847] using wordTrace_append hprefix tailTrace_635847
  have hstable : (prefixWord ++ tailWord_635847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635847).length < 2 ^ (prefixWord ++ tailWord_635847).sum := by decide
  have hdescent : baseEnd_635847 < baseStart_635847 := by decide
  rcases family_descends (prefixWord ++ tailWord_635847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635864 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 3, 2, 2]
def baseStart_635864 : Nat := 118140960795 + 635864 * 2 ^ 59
def prefixEnd_635864 : Nat := 4983230072969 + 3 ^ 40 * 635864 * 2
def baseEnd_635864 : Nat := 326503862890605412875721

theorem tailTrace_635864 : CollatzResearch.WordTrace tailWord_635864 prefixEnd_635864 326503862890605412875721 := by
  unfold tailWord_635864
  simp only [CollatzResearch.WordTrace]
  refine ⟨11595932684190399885233323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15461243578920533180311097 11595932684190399885233323)
  ·
    refine ⟨17393899026285599827849985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11595932684190399885233323 17393899026285599827849985)
    ·
      refine ⟨13045424269714199870887489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17393899026285599827849985 13045424269714199870887489)
      ·
        refine ⟨9784068202285649903165617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13045424269714199870887489 9784068202285649903165617)
        ·
          refine ⟨7338051151714237427374213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9784068202285649903165617 7338051151714237427374213)
          ·
            refine ⟨1375884590946419517632665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7338051151714237427374213 1375884590946419517632665)
            ·
              refine ⟨1031913443209814638224499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1375884590946419517632665 1031913443209814638224499)
              ·
                refine ⟨1547870164814721957336749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031913443209814638224499 1547870164814721957336749)
                ·
                  refine ⟨580451311805520734001281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1547870164814721957336749 580451311805520734001281)
                  ·
                    refine ⟨435338483854140550500961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 580451311805520734001281 435338483854140550500961)
                    ·
                      refine ⟨326503862890605412875721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 435338483854140550500961 326503862890605412875721)
                      ·
                        rfl

theorem cell23_635864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_635864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635864 prefixEnd_635864 := by exact prefixLift 635864
  have htrace : WordTrace (prefixWord ++ tailWord_635864) baseStart_635864 baseEnd_635864 := by
    simpa [prefixWord, tailWord_635864, baseEnd_635864] using wordTrace_append hprefix tailTrace_635864
  have hstable : (prefixWord ++ tailWord_635864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635864).length < 2 ^ (prefixWord ++ tailWord_635864).sum := by decide
  have hdescent : baseEnd_635864 < baseStart_635864 := by decide
  rcases family_descends (prefixWord ++ tailWord_635864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635874 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_635874 : Nat := 118140960795 + 635874 * 2 ^ 59
def prefixEnd_635874 : Nat := 4983230072969 + 3 ^ 40 * 635874 * 2
def baseEnd_635874 : Nat := 108836332565716791250225

theorem tailTrace_635874 : CollatzResearch.WordTrace tailWord_635874 prefixEnd_635874 108836332565716791250225 := by
  unfold tailWord_635874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5798057524586142869582669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15461486732229714318887117 5798057524586142869582669)
  ·
    refine ⟨2174271571719803576093501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5798057524586142869582669 2174271571719803576093501)
    ·
      refine ⟨815351839394926341035063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2174271571719803576093501 815351839394926341035063)
      ·
        refine ⟨1223027759092389511552595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815351839394926341035063 1223027759092389511552595)
        ·
          refine ⟨1834541638638584267328893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223027759092389511552595 1834541638638584267328893)
          ·
            refine ⟨687953114489469100248335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1834541638638584267328893 687953114489469100248335)
            ·
              refine ⟨1031929671734203650372503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687953114489469100248335 1031929671734203650372503)
              ·
                refine ⟨1547894507601305475558755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1031929671734203650372503 1547894507601305475558755)
                ·
                  refine ⟨2321841761401958213338133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547894507601305475558755 2321841761401958213338133)
                  ·
                    refine ⟨108836332565716791250225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2321841761401958213338133 108836332565716791250225)
                    ·
                      rfl

theorem cell23_635874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_635874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635874 prefixEnd_635874 := by exact prefixLift 635874
  have htrace : WordTrace (prefixWord ++ tailWord_635874) baseStart_635874 baseEnd_635874 := by
    simpa [prefixWord, tailWord_635874, baseEnd_635874] using wordTrace_append hprefix tailTrace_635874
  have hstable : (prefixWord ++ tailWord_635874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635874).length < 2 ^ (prefixWord ++ tailWord_635874).sum := by decide
  have hdescent : baseEnd_635874 < baseStart_635874 := by decide
  rcases family_descends (prefixWord ++ tailWord_635874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635877 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 6]
def baseStart_635877 : Nat := 118140960795 + 635877 * 2 ^ 59
def prefixEnd_635877 : Nat := 4983230072969 + 3 ^ 40 * 635877 * 2
def baseEnd_635877 : Nat := 326510538139113862013161

theorem tailTrace_635877 : CollatzResearch.WordTrace tailWord_635877 prefixEnd_635877 326510538139113862013161 := by
  unfold tailWord_635877
  simp only [CollatzResearch.WordTrace]
  refine ⟨23192339517333702990689885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15461559678222468660459923 23192339517333702990689885)
  ·
    refine ⟨8697127319000138621508707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23192339517333702990689885 8697127319000138621508707)
    ·
      refine ⟨13045690978500207932263061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8697127319000138621508707 13045690978500207932263061)
      ·
        refine ⟨611516764617197246824831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13045690978500207932263061 611516764617197246824831)
        ·
          refine ⟨917275146925795870237247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611516764617197246824831 917275146925795870237247)
          ·
            refine ⟨1375912720388693805355871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917275146925795870237247 1375912720388693805355871)
            ·
              refine ⟨2063869080583040708033807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375912720388693805355871 2063869080583040708033807)
              ·
                refine ⟨3095803620874561062050711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2063869080583040708033807 3095803620874561062050711)
                ·
                  refine ⟨4643705431311841593076067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3095803620874561062050711 4643705431311841593076067)
                  ·
                    refine ⟨6965558146967762389614101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4643705431311841593076067 6965558146967762389614101)
                    ·
                      refine ⟨326510538139113862013161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6965558146967762389614101 326510538139113862013161)
                      ·
                        rfl

theorem cell23_635877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_635877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635877 prefixEnd_635877 := by exact prefixLift 635877
  have htrace : WordTrace (prefixWord ++ tailWord_635877) baseStart_635877 baseEnd_635877 := by
    simpa [prefixWord, tailWord_635877, baseEnd_635877] using wordTrace_append hprefix tailTrace_635877
  have hstable : (prefixWord ++ tailWord_635877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635877).length < 2 ^ (prefixWord ++ tailWord_635877).sum := by decide
  have hdescent : baseEnd_635877 < baseStart_635877 := by decide
  rcases family_descends (prefixWord ++ tailWord_635877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635903 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 4]
def baseStart_635903 : Nat := 118140960795 + 635903 * 2 ^ 59
def prefixEnd_635903 : Nat := 4983230072969 + 3 ^ 40 * 635903 * 2
def baseEnd_635903 : Nat := 326523888636130760288041

theorem tailTrace_635903 : CollatzResearch.WordTrace tailWord_635903 prefixEnd_635903 326523888636130760288041 := by
  unfold tailWord_635903
  simp only [CollatzResearch.WordTrace]
  refine ⟨23193287815239509431136363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15462191876826339620757575 23193287815239509431136363)
  ·
    refine ⟨34789931722859264146704545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23193287815239509431136363 34789931722859264146704545)
    ·
      refine ⟨26092448792144448110028409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34789931722859264146704545 26092448792144448110028409)
      ·
        refine ⟨19569336594108336082521307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26092448792144448110028409 19569336594108336082521307)
        ·
          refine ⟨29354004891162504123781961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19569336594108336082521307 29354004891162504123781961)
          ·
            refine ⟨22015503668371878092836471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29354004891162504123781961 22015503668371878092836471)
            ·
              refine ⟨33023255502557817139254707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22015503668371878092836471 33023255502557817139254707)
              ·
                refine ⟨49534883253836725708882061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33023255502557817139254707 49534883253836725708882061)
                ·
                  refine ⟨18575581220188772140830773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49534883253836725708882061 18575581220188772140830773)
                  ·
                    refine ⟨1741460739392697388202885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18575581220188772140830773 1741460739392697388202885)
                    ·
                      refine ⟨326523888636130760288041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1741460739392697388202885 326523888636130760288041)
                      ·
                        rfl

theorem cell23_635903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_635903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635903 prefixEnd_635903 := by exact prefixLift 635903
  have htrace : WordTrace (prefixWord ++ tailWord_635903) baseStart_635903 baseEnd_635903 := by
    simpa [prefixWord, tailWord_635903, baseEnd_635903] using wordTrace_append hprefix tailTrace_635903
  have hstable : (prefixWord ++ tailWord_635903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635903).length < 2 ^ (prefixWord ++ tailWord_635903).sum := by decide
  have hdescent : baseEnd_635903 < baseStart_635903 := by decide
  rcases family_descends (prefixWord ++ tailWord_635903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635913 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 4, 6]
def baseStart_635913 : Nat := 118140960795 + 635913 * 2 ^ 59
def prefixEnd_635913 : Nat := 4983230072969 + 3 ^ 40 * 635913 * 2
def baseEnd_635913 : Nat := 108843007814225240387665

theorem tailTrace_635913 : CollatzResearch.WordTrace tailWord_635913 prefixEnd_635913 108843007814225240387665 := by
  unfold tailWord_635913
  simp only [CollatzResearch.WordTrace]
  refine ⟨23193652545203281139000393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15462435030135520759333595 23193652545203281139000393)
  ·
    refine ⟨17395239408902460854250295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23193652545203281139000393 17395239408902460854250295)
    ·
      refine ⟨26092859113353691281375443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17395239408902460854250295 26092859113353691281375443)
      ·
        refine ⟨39139288670030536922063165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26092859113353691281375443 39139288670030536922063165)
        ·
          refine ⟨14677233251261451345773687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39139288670030536922063165 14677233251261451345773687)
          ·
            refine ⟨22015849876892177018660531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14677233251261451345773687 22015849876892177018660531)
            ·
              refine ⟨33023774815338265527990797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22015849876892177018660531 33023774815338265527990797)
              ·
                refine ⟨12383915555751849572996549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33023774815338265527990797 12383915555751849572996549)
                ·
                  refine ⟨2321984166703471794936853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12383915555751849572996549 2321984166703471794936853)
                  ·
                    refine ⟨108843007814225240387665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2321984166703471794936853 108843007814225240387665)
                    ·
                      rfl

theorem cell23_635913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4, 6].length) (baseStart_635913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635913 prefixEnd_635913 := by exact prefixLift 635913
  have htrace : WordTrace (prefixWord ++ tailWord_635913) baseStart_635913 baseEnd_635913 := by
    simpa [prefixWord, tailWord_635913, baseEnd_635913] using wordTrace_append hprefix tailTrace_635913
  have hstable : (prefixWord ++ tailWord_635913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635913).length < 2 ^ (prefixWord ++ tailWord_635913).sum := by decide
  have hdescent : baseEnd_635913 < baseStart_635913 := by decide
  rcases family_descends (prefixWord ++ tailWord_635913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635920 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 2, 8, 2]
def baseStart_635920 : Nat := 118140960795 + 635920 * 2 ^ 59
def prefixEnd_635920 : Nat := 4983230072969 + 3 ^ 40 * 635920 * 2
def baseEnd_635920 : Nat := 326532617807257193775463

theorem tailTrace_635920 : CollatzResearch.WordTrace tailWord_635920 prefixEnd_635920 326532617807257193775463 := by
  unfold tailWord_635920
  simp only [CollatzResearch.WordTrace]
  refine ⟨11596953928088960667252607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15462605237451947556336809 11596953928088960667252607)
  ·
    refine ⟨17395430892133441000878911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11596953928088960667252607 17395430892133441000878911)
    ·
      refine ⟨26093146338200161501318367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17395430892133441000878911 26093146338200161501318367)
      ·
        refine ⟨39139719507300242251977551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26093146338200161501318367 39139719507300242251977551)
        ·
          refine ⟨58709579260950363377966327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39139719507300242251977551 58709579260950363377966327)
          ·
            refine ⟨88064368891425545066949491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58709579260950363377966327 88064368891425545066949491)
            ·
              refine ⟨132096553337138317600424237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88064368891425545066949491 132096553337138317600424237)
              ·
                refine ⟨49536207501426869100159089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132096553337138317600424237 49536207501426869100159089)
                ·
                  refine ⟨37152155626070151825119317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49536207501426869100159089 37152155626070151825119317)
                  ·
                    refine ⟨435376823743009591700617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37152155626070151825119317 435376823743009591700617)
                    ·
                      refine ⟨326532617807257193775463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 435376823743009591700617 326532617807257193775463)
                      ·
                        rfl

theorem cell23_635920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 2, 8, 2].length) (baseStart_635920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635920 prefixEnd_635920 := by exact prefixLift 635920
  have htrace : WordTrace (prefixWord ++ tailWord_635920) baseStart_635920 baseEnd_635920 := by
    simpa [prefixWord, tailWord_635920, baseEnd_635920] using wordTrace_append hprefix tailTrace_635920
  have hstable : (prefixWord ++ tailWord_635920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635920).length < 2 ^ (prefixWord ++ tailWord_635920).sum := by decide
  have hdescent : baseEnd_635920 < baseStart_635920 := by decide
  rcases family_descends (prefixWord ++ tailWord_635920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635923 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 5]
def baseStart_635923 : Nat := 118140960795 + 635923 * 2 ^ 59
def prefixEnd_635923 : Nat := 4983230072969 + 3 ^ 40 * 635923 * 2
def baseEnd_635923 : Nat := 326534158249220682037949

theorem tailTrace_635923 : CollatzResearch.WordTrace tailWord_635923 prefixEnd_635923 326534158249220682037949 := by
  unfold tailWord_635923
  simp only [CollatzResearch.WordTrace]
  refine ⟨23194017275167052846864423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15462678183444701897909615 23194017275167052846864423)
  ·
    refine ⟨34791025912750579270296635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23194017275167052846864423 34791025912750579270296635)
    ·
      refine ⟨52186538869125868905444953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34791025912750579270296635 52186538869125868905444953)
      ·
        refine ⟨39139904151844401679083715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52186538869125868905444953 39139904151844401679083715)
        ·
          refine ⟨58709856227766602518625573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39139904151844401679083715 58709856227766602518625573)
          ·
            refine ⟨11008098042706237972242295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58709856227766602518625573 11008098042706237972242295)
            ·
              refine ⟨16512147064059356958363443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11008098042706237972242295 16512147064059356958363443)
              ·
                refine ⟨24768220596089035437545165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16512147064059356958363443 24768220596089035437545165)
                ·
                  refine ⟨9288082723533388289079437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24768220596089035437545165 9288082723533388289079437)
                  ·
                    refine ⟨3483031021325020608404789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9288082723533388289079437 3483031021325020608404789)
                    ·
                      refine ⟨326534158249220682037949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3483031021325020608404789 326534158249220682037949)
                      ·
                        rfl

theorem cell23_635923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_635923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635923 prefixEnd_635923 := by exact prefixLift 635923
  have htrace : WordTrace (prefixWord ++ tailWord_635923) baseStart_635923 baseEnd_635923 := by
    simpa [prefixWord, tailWord_635923, baseEnd_635923] using wordTrace_append hprefix tailTrace_635923
  have hstable : (prefixWord ++ tailWord_635923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635923).length < 2 ^ (prefixWord ++ tailWord_635923).sum := by decide
  have hdescent : baseEnd_635923 < baseStart_635923 := by decide
  rcases family_descends (prefixWord ++ tailWord_635923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635958 : List Nat := [5, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_635958 : Nat := 118140960795 + 635958 * 2 ^ 59
def prefixEnd_635958 : Nat := 4983230072969 + 3 ^ 40 * 635958 * 2
def baseEnd_635958 : Nat := 326552130072128045100289

theorem tailTrace_635958 : CollatzResearch.WordTrace tailWord_635958 prefixEnd_635958 326552130072128045100289 := by
  unfold tailWord_635958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449705864377515864024283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15463529220026835882925685 1449705864377515864024283)
  ·
    refine ⟨2174558796566273796036425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1449705864377515864024283 2174558796566273796036425)
    ·
      refine ⟨1630919097424705347027319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2174558796566273796036425 1630919097424705347027319)
      ·
        refine ⟨2446378646137058020540979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1630919097424705347027319 2446378646137058020540979)
        ·
          refine ⟨3669567969205587030811469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446378646137058020540979 3669567969205587030811469)
          ·
            refine ⟨1376087988452095136554301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3669567969205587030811469 1376087988452095136554301)
            ·
              refine ⟨516032995669535676207863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1376087988452095136554301 516032995669535676207863)
              ·
                refine ⟨774049493504303514311795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 516032995669535676207863 774049493504303514311795)
                ·
                  refine ⟨1161074240256455271467693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 774049493504303514311795 1161074240256455271467693)
                  ·
                    refine ⟨435402840096170726800385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1161074240256455271467693 435402840096170726800385)
                    ·
                      refine ⟨326552130072128045100289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 435402840096170726800385 326552130072128045100289)
                      ·
                        rfl

theorem cell23_635958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_635958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635958 prefixEnd_635958 := by exact prefixLift 635958
  have htrace : WordTrace (prefixWord ++ tailWord_635958) baseStart_635958 baseEnd_635958 := by
    simpa [prefixWord, tailWord_635958, baseEnd_635958] using wordTrace_append hprefix tailTrace_635958
  have hstable : (prefixWord ++ tailWord_635958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635958).length < 2 ^ (prefixWord ++ tailWord_635958).sum := by decide
  have hdescent : baseEnd_635958 < baseStart_635958 := by decide
  rcases family_descends (prefixWord ++ tailWord_635958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635963 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 6]
def baseStart_635963 : Nat := 118140960795 + 635963 * 2 ^ 59
def prefixEnd_635963 : Nat := 4983230072969 + 3 ^ 40 * 635963 * 2
def baseEnd_635963 : Nat := 326554697475400525537765

theorem tailTrace_635963 : CollatzResearch.WordTrace tailWord_635963 prefixEnd_635963 326554697475400525537765 := by
  unfold tailWord_635963
  simp only [CollatzResearch.WordTrace]
  refine ⟨23195476195022139678320543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15463650796681426452213695 23195476195022139678320543)
  ·
    refine ⟨34793214292533209517480815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23195476195022139678320543 34793214292533209517480815)
    ·
      refine ⟨52189821438799814276221223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34793214292533209517480815 52189821438799814276221223)
      ·
        refine ⟨78284732158199721414331835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52189821438799814276221223 78284732158199721414331835)
        ·
          refine ⟨117427098237299582121497753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78284732158199721414331835 117427098237299582121497753)
          ·
            refine ⟨88070323677974686591123315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117427098237299582121497753 88070323677974686591123315)
            ·
              refine ⟨132105485516962029886684973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88070323677974686591123315 132105485516962029886684973)
              ·
                refine ⟨49539557068860761207506865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132105485516962029886684973 49539557068860761207506865)
                ·
                  refine ⟨37154667801645570905630149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49539557068860761207506865 37154667801645570905630149)
                  ·
                    refine ⟨6966500212808544544805653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37154667801645570905630149 6966500212808544544805653)
                    ·
                      refine ⟨326554697475400525537765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6966500212808544544805653 326554697475400525537765)
                      ·
                        rfl

theorem cell23_635963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 6].length) (baseStart_635963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635963 prefixEnd_635963 := by exact prefixLift 635963
  have htrace : WordTrace (prefixWord ++ tailWord_635963) baseStart_635963 baseEnd_635963 := by
    simpa [prefixWord, tailWord_635963, baseEnd_635963] using wordTrace_append hprefix tailTrace_635963
  have hstable : (prefixWord ++ tailWord_635963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635963).length < 2 ^ (prefixWord ++ tailWord_635963).sum := by decide
  have hdescent : baseEnd_635963 < baseStart_635963 := by decide
  rcases family_descends (prefixWord ++ tailWord_635963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_635974 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_635974 : Nat := 118140960795 + 635974 * 2 ^ 59
def prefixEnd_635974 : Nat := 4983230072969 + 3 ^ 40 * 635974 * 2
def baseEnd_635974 : Nat := 326560345762599982500215

theorem tailTrace_635974 : CollatzResearch.WordTrace tailWord_635974 prefixEnd_635974 326560345762599982500215 := by
  unfold tailWord_635974
  simp only [CollatzResearch.WordTrace]
  refine ⟨724871168686946517405343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15463918265321525704647317 724871168686946517405343)
  ·
    refine ⟨1087306753030419776108015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 724871168686946517405343 1087306753030419776108015)
    ·
      refine ⟨1630960129545629664162023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1087306753030419776108015 1630960129545629664162023)
      ·
        refine ⟨2446440194318444496243035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1630960129545629664162023 2446440194318444496243035)
        ·
          refine ⟨3669660291477666744364553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446440194318444496243035 3669660291477666744364553)
          ·
            refine ⟨2752245218608250058273415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3669660291477666744364553 2752245218608250058273415)
            ·
              refine ⟨4128367827912375087410123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2752245218608250058273415 4128367827912375087410123)
              ·
                refine ⟨6192551741868562631115185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4128367827912375087410123 6192551741868562631115185)
                ·
                  refine ⟨4644413806401421973336389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6192551741868562631115185 4644413806401421973336389)
                  ·
                    refine ⟨870827588700266620000573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4644413806401421973336389 870827588700266620000573)
                    ·
                      refine ⟨326560345762599982500215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 870827588700266620000573 326560345762599982500215)
                      ·
                        rfl

theorem cell23_635974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_635974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_635974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_635974 prefixEnd_635974 := by exact prefixLift 635974
  have htrace : WordTrace (prefixWord ++ tailWord_635974) baseStart_635974 baseEnd_635974 := by
    simpa [prefixWord, tailWord_635974, baseEnd_635974] using wordTrace_append hprefix tailTrace_635974
  have hstable : (prefixWord ++ tailWord_635974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_635974).length < 2 ^ (prefixWord ++ tailWord_635974).sum := by decide
  have hdescent : baseEnd_635974 < baseStart_635974 := by decide
  rcases family_descends (prefixWord ++ tailWord_635974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636007 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 2, 5]
def baseStart_636007 : Nat := 118140960795 + 636007 * 2 ^ 59
def prefixEnd_636007 : Nat := 4983230072969 + 3 ^ 40 * 636007 * 2
def baseEnd_636007 : Nat := 108859096874732784462521

theorem tailTrace_636007 : CollatzResearch.WordTrace tailWord_636007 prefixEnd_636007 108859096874732784462521 := by
  unfold tailWord_636007
  simp only [CollatzResearch.WordTrace]
  refine ⟨23197081006862735192922275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15464720671241823461948183 23197081006862735192922275)
  ·
    refine ⟨34795621510294102789383413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23197081006862735192922275 34795621510294102789383413)
    ·
      refine ⟨3262089516590072136504695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34795621510294102789383413 3262089516590072136504695)
      ·
        refine ⟨4893134274885108204757043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3262089516590072136504695 4893134274885108204757043)
        ·
          refine ⟨7339701412327662307135565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893134274885108204757043 7339701412327662307135565)
          ·
            refine ⟨2752388029622873365175837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7339701412327662307135565 2752388029622873365175837)
            ·
              refine ⟨1032145511108577511940939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2752388029622873365175837 1032145511108577511940939)
              ·
                refine ⟨1548218266662866267911409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1032145511108577511940939 1548218266662866267911409)
                ·
                  refine ⟨1161163699997149700933557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1548218266662866267911409 1161163699997149700933557)
                  ·
                    refine ⟨108859096874732784462521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1161163699997149700933557 108859096874732784462521)
                    ·
                      rfl

theorem cell23_636007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_636007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636007 prefixEnd_636007 := by exact prefixLift 636007
  have htrace : WordTrace (prefixWord ++ tailWord_636007) baseStart_636007 baseEnd_636007 := by
    simpa [prefixWord, tailWord_636007, baseEnd_636007] using wordTrace_append hprefix tailTrace_636007
  have hstable : (prefixWord ++ tailWord_636007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636007).length < 2 ^ (prefixWord ++ tailWord_636007).sum := by decide
  have hdescent : baseEnd_636007 < baseStart_636007 := by decide
  rcases family_descends (prefixWord ++ tailWord_636007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636090 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_636090 : Nat := 118140960795 + 636090 * 2 ^ 59
def prefixEnd_636090 : Nat := 4983230072969 + 3 ^ 40 * 636090 * 2
def baseEnd_636090 : Nat := 326619909518521528649681

theorem tailTrace_636090 : CollatzResearch.WordTrace tailWord_636090 prefixEnd_636090 326619909518521528649681 := by
  unfold tailWord_636090
  simp only [CollatzResearch.WordTrace]
  refine ⟨5800027066390510092048431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15466738843708026912129149 5800027066390510092048431)
  ·
    refine ⟨8700040599585765138072647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5800027066390510092048431 8700040599585765138072647)
    ·
      refine ⟨13050060899378647707108971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8700040599585765138072647 13050060899378647707108971)
      ·
        refine ⟨19575091349067971560663457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13050060899378647707108971 19575091349067971560663457)
        ·
          refine ⟨14681318511800978670497593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19575091349067971560663457 14681318511800978670497593)
          ·
            refine ⟨11010988883850734002873195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14681318511800978670497593 11010988883850734002873195)
            ·
              refine ⟨16516483325776101004309793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11010988883850734002873195 16516483325776101004309793)
              ·
                refine ⟨12387362494332075753232345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16516483325776101004309793 12387362494332075753232345)
                ·
                  refine ⟨9290521870749056814924259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12387362494332075753232345 9290521870749056814924259)
                  ·
                    refine ⟨13935782806123585222386389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9290521870749056814924259 13935782806123585222386389)
                    ·
                      refine ⟨326619909518521528649681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13935782806123585222386389 326619909518521528649681)
                      ·
                        rfl

theorem cell23_636090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_636090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636090 prefixEnd_636090 := by exact prefixLift 636090
  have htrace : WordTrace (prefixWord ++ tailWord_636090) baseStart_636090 baseEnd_636090 := by
    simpa [prefixWord, tailWord_636090, baseEnd_636090] using wordTrace_append hprefix tailTrace_636090
  have hstable : (prefixWord ++ tailWord_636090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636090).length < 2 ^ (prefixWord ++ tailWord_636090).sum := by decide
  have hdescent : baseEnd_636090 < baseStart_636090 := by decide
  rcases family_descends (prefixWord ++ tailWord_636090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636127 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 6, 4]
def baseStart_636127 : Nat := 118140960795 + 636127 * 2 ^ 59
def prefixEnd_636127 : Nat := 4983230072969 + 3 ^ 40 * 636127 * 2
def baseEnd_636127 : Nat := 108879636100912627962337

theorem tailTrace_636127 : CollatzResearch.WordTrace tailWord_636127 prefixEnd_636127 108879636100912627962337 := by
  unfold tailWord_636127
  simp only [CollatzResearch.WordTrace]
  refine ⟨23201457766427995687290635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15467638510951997124860423 23201457766427995687290635)
  ·
    refine ⟨34802186649641993530935953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23201457766427995687290635 34802186649641993530935953)
    ·
      refine ⟨26101639987231495148201965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34802186649641993530935953 26101639987231495148201965)
      ·
        refine ⟨9788114995211810680575737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26101639987231495148201965 9788114995211810680575737)
        ·
          refine ⟨7341086246408858010431803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9788114995211810680575737 7341086246408858010431803)
          ·
            refine ⟨11011629369613287015647705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7341086246408858010431803 11011629369613287015647705)
            ·
              refine ⟨8258722027209965261735779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11011629369613287015647705 8258722027209965261735779)
              ·
                refine ⟨12388083040814947892603669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8258722027209965261735779 12388083040814947892603669)
                ·
                  refine ⟨580691392538200682465797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12388083040814947892603669 580691392538200682465797)
                  ·
                    refine ⟨108879636100912627962337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 580691392538200682465797 108879636100912627962337)
                    ·
                      rfl

theorem cell23_636127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 6, 4].length) (baseStart_636127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636127 prefixEnd_636127 := by exact prefixLift 636127
  have htrace : WordTrace (prefixWord ++ tailWord_636127) baseStart_636127 baseEnd_636127 := by
    simpa [prefixWord, tailWord_636127, baseEnd_636127] using wordTrace_append hprefix tailTrace_636127
  have hstable : (prefixWord ++ tailWord_636127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636127).length < 2 ^ (prefixWord ++ tailWord_636127).sum := by decide
  have hdescent : baseEnd_636127 < baseStart_636127 := by decide
  rcases family_descends (prefixWord ++ tailWord_636127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636137 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 7, 2, 3]
def baseStart_636137 : Nat := 118140960795 + 636137 * 2 ^ 59
def prefixEnd_636137 : Nat := 4983230072969 + 3 ^ 40 * 636137 * 2
def baseEnd_636137 : Nat := 326644043109282844761965

theorem tailTrace_636137 : CollatzResearch.WordTrace tailWord_636137 prefixEnd_636137 326644043109282844761965 := by
  unfold tailWord_636137
  simp only [CollatzResearch.WordTrace]
  refine ⟨23201822496391767395154665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15467881664261178263436443 23201822496391767395154665)
  ·
    refine ⟨17401366872293825546365999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23201822496391767395154665 17401366872293825546365999)
    ·
      refine ⟨26102050308440738319548999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17401366872293825546365999 26102050308440738319548999)
      ·
        refine ⟨39153075462661107479323499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26102050308440738319548999 39153075462661107479323499)
        ·
          refine ⟨58729613193991661218985249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39153075462661107479323499 58729613193991661218985249)
          ·
            refine ⟨44047209895493745914238937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58729613193991661218985249 44047209895493745914238937)
            ·
              refine ⟨33035407421620309435679203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44047209895493745914238937 33035407421620309435679203)
              ·
                refine ⟨49553111132430464153518805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33035407421620309435679203 49553111132430464153518805)
                ·
                  refine ⟨1161401042166339003598097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 49553111132430464153518805 1161401042166339003598097)
                  ·
                    refine ⟨871050781624754252698573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1161401042166339003598097 871050781624754252698573)
                    ·
                      refine ⟨326644043109282844761965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 871050781624754252698573 326644043109282844761965)
                      ·
                        rfl

theorem cell23_636137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 2, 3].length) (baseStart_636137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636137 prefixEnd_636137 := by exact prefixLift 636137
  have htrace : WordTrace (prefixWord ++ tailWord_636137) baseStart_636137 baseEnd_636137 := by
    simpa [prefixWord, tailWord_636137, baseEnd_636137] using wordTrace_append hprefix tailTrace_636137
  have hstable : (prefixWord ++ tailWord_636137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636137).length < 2 ^ (prefixWord ++ tailWord_636137).sum := by decide
  have hdescent : baseEnd_636137 < baseStart_636137 := by decide
  rcases family_descends (prefixWord ++ tailWord_636137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636140 : List Nat := [2, 2, 1, 1, 2, 15]
def baseStart_636140 : Nat := 118140960795 + 636140 * 2 ^ 59
def prefixEnd_636140 : Nat := 4983230072969 + 3 ^ 40 * 636140 * 2
def baseEnd_636140 : Nat := 1344220508441342934257

theorem tailTrace_636140 : CollatzResearch.WordTrace tailWord_636140 prefixEnd_636140 1344220508441342934257 := by
  unfold tailWord_636140
  simp only [CollatzResearch.WordTrace]
  refine ⟨11600965957690449453756937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15467954610253932605009249 11600965957690449453756937)
  ·
    refine ⟨8700724468267837090317703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11600965957690449453756937 8700724468267837090317703)
    ·
      refine ⟨13051086702401755635476555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8700724468267837090317703 13051086702401755635476555)
      ·
        refine ⟨19576630053602633453214833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13051086702401755635476555 19576630053602633453214833)
        ·
          refine ⟨14682472540201975089911125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19576630053602633453214833 14682472540201975089911125)
          ·
            refine ⟨1344220508441342934257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 14682472540201975089911125 1344220508441342934257)
            ·
              rfl

theorem cell23_636140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 15].length) (baseStart_636140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636140 prefixEnd_636140 := by exact prefixLift 636140
  have htrace : WordTrace (prefixWord ++ tailWord_636140) baseStart_636140 baseEnd_636140 := by
    simpa [prefixWord, tailWord_636140, baseEnd_636140] using wordTrace_append hprefix tailTrace_636140
  have hstable : (prefixWord ++ tailWord_636140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636140).length < 2 ^ (prefixWord ++ tailWord_636140).sum := by decide
  have hdescent : baseEnd_636140 < baseStart_636140 := by decide
  rcases family_descends (prefixWord ++ tailWord_636140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636164 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_636164 : Nat := 118140960795 + 636164 * 2 ^ 59
def prefixEnd_636164 : Nat := 4983230072969 + 3 ^ 40 * 636164 * 2
def baseEnd_636164 : Nat := 326657907086954239124341

theorem tailTrace_636164 : CollatzResearch.WordTrace tailWord_636164 prefixEnd_636164 326657907086954239124341 := by
  unfold tailWord_636164
  simp only [CollatzResearch.WordTrace]
  refine ⟨11601403633646975503193773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15468538178195967337591697 11601403633646975503193773)
  ·
    refine ⟨4350526362617615813697665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11601403633646975503193773 4350526362617615813697665)
    ·
      refine ⟨3262894771963211860273249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4350526362617615813697665 3262894771963211860273249)
      ·
        refine ⟨2447171078972408895204937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3262894771963211860273249 2447171078972408895204937)
        ·
          refine ⟨1835378309229306671403703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2447171078972408895204937 1835378309229306671403703)
          ·
            refine ⟨2753067463843960007105555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835378309229306671403703 2753067463843960007105555)
            ·
              refine ⟨4129601195765940010658333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753067463843960007105555 4129601195765940010658333)
              ·
                refine ⟨1548600448412227503996875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4129601195765940010658333 1548600448412227503996875)
                ·
                  refine ⟨2322900672618341255995313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548600448412227503996875 2322900672618341255995313)
                  ·
                    refine ⟨1742175504463755941996485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2322900672618341255995313 1742175504463755941996485)
                    ·
                      refine ⟨326657907086954239124341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1742175504463755941996485 326657907086954239124341)
                      ·
                        rfl

theorem cell23_636164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_636164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636164 prefixEnd_636164 := by exact prefixLift 636164
  have htrace : WordTrace (prefixWord ++ tailWord_636164) baseStart_636164 baseEnd_636164 := by
    simpa [prefixWord, tailWord_636164, baseEnd_636164] using wordTrace_append hprefix tailTrace_636164
  have hstable : (prefixWord ++ tailWord_636164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636164).length < 2 ^ (prefixWord ++ tailWord_636164).sum := by decide
  have hdescent : baseEnd_636164 < baseStart_636164 := by decide
  rcases family_descends (prefixWord ++ tailWord_636164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636168 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 3, 2, 2]
def baseStart_636168 : Nat := 118140960795 + 636168 * 2 ^ 59
def prefixEnd_636168 : Nat := 4983230072969 + 3 ^ 40 * 636168 * 2
def baseEnd_636168 : Nat := 326659961009572223474323

theorem tailTrace_636168 : CollatzResearch.WordTrace tailWord_636168 prefixEnd_636168 326659961009572223474323 := by
  unfold tailWord_636168
  simp only [CollatzResearch.WordTrace]
  refine ⟨11601476579639729844766579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15468635439519639793022105 11601476579639729844766579)
  ·
    refine ⟨17402214869459594767149869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11601476579639729844766579 17402214869459594767149869)
    ·
      refine ⟨6525830576047348037681201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17402214869459594767149869 6525830576047348037681201)
      ·
        refine ⟨4894372932035511028260901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6525830576047348037681201 4894372932035511028260901)
        ·
          refine ⟨917694924756658317798919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4894372932035511028260901 917694924756658317798919)
          ·
            refine ⟨1376542387134987476698379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917694924756658317798919 1376542387134987476698379)
            ·
              refine ⟨2064813580702481215047569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376542387134987476698379 2064813580702481215047569)
              ·
                refine ⟨1548610185526860911285677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2064813580702481215047569 1548610185526860911285677)
                ·
                  refine ⟨580728819572572841732129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1548610185526860911285677 580728819572572841732129)
                  ·
                    refine ⟨435546614679429631299097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 580728819572572841732129 435546614679429631299097)
                    ·
                      refine ⟨326659961009572223474323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 435546614679429631299097 326659961009572223474323)
                      ·
                        rfl

theorem cell23_636168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_636168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636168 prefixEnd_636168 := by exact prefixLift 636168
  have htrace : WordTrace (prefixWord ++ tailWord_636168) baseStart_636168 baseEnd_636168 := by
    simpa [prefixWord, tailWord_636168, baseEnd_636168] using wordTrace_append hprefix tailTrace_636168
  have hstable : (prefixWord ++ tailWord_636168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636168).length < 2 ^ (prefixWord ++ tailWord_636168).sum := by decide
  have hdescent : baseEnd_636168 < baseStart_636168 := by decide
  rcases family_descends (prefixWord ++ tailWord_636168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636174 : List Nat := [4, 1, 1, 2, 1, 4, 3, 7]
def baseStart_636174 : Nat := 118140960795 + 636174 * 2 ^ 59
def prefixEnd_636174 : Nat := 4983230072969 + 3 ^ 40 * 636174 * 2
def baseEnd_636174 : Nat := 12098631181240711111085

theorem tailTrace_636174 : CollatzResearch.WordTrace tailWord_636174 prefixEnd_636174 12098631181240711111085 := by
  unfold tailWord_636174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2900396499657215339281447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15468781331505148476167717 2900396499657215339281447)
  ·
    refine ⟨4350594749485823008922171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2900396499657215339281447 4350594749485823008922171)
    ·
      refine ⟨6525892124228734513383257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4350594749485823008922171 6525892124228734513383257)
      ·
        refine ⟨4894419093171550885037443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6525892124228734513383257 4894419093171550885037443)
        ·
          refine ⟨7341628639757326327556165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4894419093171550885037443 7341628639757326327556165)
          ·
            refine ⟨1376555369954498686416781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7341628639757326327556165 1376555369954498686416781)
            ·
              refine ⟨516208263732937007406293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1376555369954498686416781 516208263732937007406293)
              ·
                refine ⟨12098631181240711111085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 516208263732937007406293 12098631181240711111085)
                ·
                  rfl

theorem cell23_636174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 7].length) (baseStart_636174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636174 prefixEnd_636174 := by exact prefixLift 636174
  have htrace : WordTrace (prefixWord ++ tailWord_636174) baseStart_636174 baseEnd_636174 := by
    simpa [prefixWord, tailWord_636174, baseEnd_636174] using wordTrace_append hprefix tailTrace_636174
  have hstable : (prefixWord ++ tailWord_636174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636174).length < 2 ^ (prefixWord ++ tailWord_636174).sum := by decide
  have hdescent : baseEnd_636174 < baseStart_636174 := by decide
  rcases family_descends (prefixWord ++ tailWord_636174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636184 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 1, 3, 3]
def baseStart_636184 : Nat := 118140960795 + 636184 * 2 ^ 59
def prefixEnd_636184 : Nat := 4983230072969 + 3 ^ 40 * 636184 * 2
def baseEnd_636184 : Nat := 326668176700044160874249

theorem tailTrace_636184 : CollatzResearch.WordTrace tailWord_636184 prefixEnd_636184 326668176700044160874249 := by
  unfold tailWord_636184
  simp only [CollatzResearch.WordTrace]
  refine ⟨11601768363610747211057803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15469024484814329614743737 11601768363610747211057803)
  ·
    refine ⟨17402652545416120816586705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11601768363610747211057803 17402652545416120816586705)
    ·
      refine ⟨13051989409062090612440029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17402652545416120816586705 13051989409062090612440029)
      ·
        refine ⟨4894496028398283979665011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13051989409062090612440029 4894496028398283979665011)
        ·
          refine ⟨7341744042597425969497517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4894496028398283979665011 7341744042597425969497517)
          ·
            refine ⟨2753154015974034738561569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7341744042597425969497517 2753154015974034738561569)
            ·
              refine ⟨2064865511980526053921177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2753154015974034738561569 2064865511980526053921177)
              ·
                refine ⟨1548649133985394540440883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2064865511980526053921177 1548649133985394540440883)
                ·
                  refine ⟨2322973700978091810661325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548649133985394540440883 2322973700978091810661325)
                  ·
                    refine ⟨871115137866784428997997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2322973700978091810661325 871115137866784428997997)
                    ·
                      refine ⟨326668176700044160874249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 871115137866784428997997 326668176700044160874249)
                      ·
                        rfl

theorem cell23_636184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_636184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636184 prefixEnd_636184 := by exact prefixLift 636184
  have htrace : WordTrace (prefixWord ++ tailWord_636184) baseStart_636184 baseEnd_636184 := by
    simpa [prefixWord, tailWord_636184, baseEnd_636184] using wordTrace_append hprefix tailTrace_636184
  have hstable : (prefixWord ++ tailWord_636184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636184).length < 2 ^ (prefixWord ++ tailWord_636184).sum := by decide
  have hdescent : baseEnd_636184 < baseStart_636184 := by decide
  rcases family_descends (prefixWord ++ tailWord_636184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636218 : List Nat := [3, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3]
def baseStart_636218 : Nat := 118140960795 + 636218 * 2 ^ 59
def prefixEnd_636218 : Nat := 4983230072969 + 3 ^ 40 * 636218 * 2
def baseEnd_636218 : Nat := 326685635042297027849093

theorem tailTrace_636218 : CollatzResearch.WordTrace tailWord_636218 prefixEnd_636218 326685635042297027849093 := by
  unfold tailWord_636218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5801194202274579557213327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15469851206065545485902205 5801194202274579557213327)
  ·
    refine ⟨8701791303411869335819991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5801194202274579557213327 8701791303411869335819991)
    ·
      refine ⟨13052686955117804003729987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8701791303411869335819991 13052686955117804003729987)
      ·
        refine ⟨19579030432676706005594981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13052686955117804003729987 19579030432676706005594981)
        ·
          refine ⟨3671068206126882376049059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19579030432676706005594981 3671068206126882376049059)
          ·
            refine ⟨5506602309190323564073589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3671068206126882376049059 5506602309190323564073589)
            ·
              refine ⟨516243966486592834131899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5506602309190323564073589 516243966486592834131899)
              ·
                refine ⟨774365949729889251197849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 516243966486592834131899 774365949729889251197849)
                ·
                  refine ⟨580774462297416938398387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 774365949729889251197849 580774462297416938398387)
                  ·
                    refine ⟨871161693446125407597581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 580774462297416938398387 871161693446125407597581)
                    ·
                      refine ⟨326685635042297027849093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 871161693446125407597581 326685635042297027849093)
                      ·
                        rfl

theorem cell23_636218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 2, 1, 3].length) (baseStart_636218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636218 prefixEnd_636218 := by exact prefixLift 636218
  have htrace : WordTrace (prefixWord ++ tailWord_636218) baseStart_636218 baseEnd_636218 := by
    simpa [prefixWord, tailWord_636218, baseEnd_636218] using wordTrace_append hprefix tailTrace_636218
  have hstable : (prefixWord ++ tailWord_636218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636218).length < 2 ^ (prefixWord ++ tailWord_636218).sum := by decide
  have hdescent : baseEnd_636218 < baseStart_636218 := by decide
  rcases family_descends (prefixWord ++ tailWord_636218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636227 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 5]
def baseStart_636227 : Nat := 118140960795 + 636227 * 2 ^ 59
def prefixEnd_636227 : Nat := 4983230072969 + 3 ^ 40 * 636227 * 2
def baseEnd_636227 : Nat := 326690256368187492636551

theorem tailTrace_636227 : CollatzResearch.WordTrace tailWord_636227 prefixEnd_636227 326690256368187492636551 := by
  unfold tailWord_636227
  simp only [CollatzResearch.WordTrace]
  refine ⟨23205105066065712765930935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15470070044043808510620623 23205105066065712765930935)
  ·
    refine ⟨34807657599098569148896403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23205105066065712765930935 34807657599098569148896403)
    ·
      refine ⟨52211486398647853723344605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34807657599098569148896403 52211486398647853723344605)
      ·
        refine ⟨19579307399492945146254227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52211486398647853723344605 19579307399492945146254227)
        ·
          refine ⟨29368961099239417719381341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19579307399492945146254227 29368961099239417719381341)
          ·
            refine ⟨11013360412214781644768003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29368961099239417719381341 11013360412214781644768003)
            ·
              refine ⟨16520040618322172467152005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11013360412214781644768003 16520040618322172467152005)
              ·
                refine ⟨3097507615935407337591001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16520040618322172467152005 3097507615935407337591001)
                ·
                  refine ⟨2323130711951555503193251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3097507615935407337591001 2323130711951555503193251)
                  ·
                    refine ⟨3484696067927333254789877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2323130711951555503193251 3484696067927333254789877)
                    ·
                      refine ⟨326690256368187492636551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3484696067927333254789877 326690256368187492636551)
                      ·
                        rfl

theorem cell23_636227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_636227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636227 prefixEnd_636227 := by exact prefixLift 636227
  have htrace : WordTrace (prefixWord ++ tailWord_636227) baseStart_636227 baseEnd_636227 := by
    simpa [prefixWord, tailWord_636227, baseEnd_636227] using wordTrace_append hprefix tailTrace_636227
  have hstable : (prefixWord ++ tailWord_636227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636227).length < 2 ^ (prefixWord ++ tailWord_636227).sum := by decide
  have hdescent : baseEnd_636227 < baseStart_636227 := by decide
  rcases family_descends (prefixWord ++ tailWord_636227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636241 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 6, 2, 2]
def baseStart_636241 : Nat := 118140960795 + 636241 * 2 ^ 59
def prefixEnd_636241 : Nat := 4983230072969 + 3 ^ 40 * 636241 * 2
def baseEnd_636241 : Nat := 326697445097350437861487

theorem tailTrace_636241 : CollatzResearch.WordTrace tailWord_636241 prefixEnd_636241 326697445097350437861487 := by
  unfold tailWord_636241
  simp only [CollatzResearch.WordTrace]
  refine ⟨23205615688014993156940577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15470410458676662104627051 23205615688014993156940577)
  ·
    refine ⟨17404211766011244867705433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23205615688014993156940577 17404211766011244867705433)
    ·
      refine ⟨13053158824508433650779075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17404211766011244867705433 13053158824508433650779075)
      ·
        refine ⟨19579738236762650476168613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13053158824508433650779075 19579738236762650476168613)
        ·
          refine ⟨3671200919392996964281615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19579738236762650476168613 3671200919392996964281615)
          ·
            refine ⟨5506801379089495446422423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3671200919392996964281615 5506801379089495446422423)
            ·
              refine ⟨8260202068634243169633635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5506801379089495446422423 8260202068634243169633635)
              ·
                refine ⟨12390303102951364754450453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8260202068634243169633635 12390303102951364754450453)
                ·
                  refine ⟨580795457950845222864865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12390303102951364754450453 580795457950845222864865)
                  ·
                    refine ⟨435596593463133917148649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 580795457950845222864865 435596593463133917148649)
                    ·
                      refine ⟨326697445097350437861487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 435596593463133917148649 326697445097350437861487)
                      ·
                        rfl

theorem cell23_636241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 2, 2].length) (baseStart_636241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636241 prefixEnd_636241 := by exact prefixLift 636241
  have htrace : WordTrace (prefixWord ++ tailWord_636241) baseStart_636241 baseEnd_636241 := by
    simpa [prefixWord, tailWord_636241, baseEnd_636241] using wordTrace_append hprefix tailTrace_636241
  have hstable : (prefixWord ++ tailWord_636241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636241).length < 2 ^ (prefixWord ++ tailWord_636241).sum := by decide
  have hdescent : baseEnd_636241 < baseStart_636241 := by decide
  rcases family_descends (prefixWord ++ tailWord_636241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636244 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_636244 : Nat := 118140960795 + 636244 * 2 ^ 59
def prefixEnd_636244 : Nat := 4983230072969 + 3 ^ 40 * 636244 * 2
def baseEnd_636244 : Nat := 326698985539313926123973

theorem tailTrace_636244 : CollatzResearch.WordTrace tailWord_636244 prefixEnd_636244 326698985539313926123973 := by
  unfold tailWord_636244
  simp only [CollatzResearch.WordTrace]
  refine ⟨11602862553502062334649893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15470483404669416446199857 11602862553502062334649893)
  ·
    refine ⟨2175536728781636687746855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11602862553502062334649893 2175536728781636687746855)
    ·
      refine ⟨3263305093172455031620283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2175536728781636687746855 3263305093172455031620283)
      ·
        refine ⟨4894957639758682547430425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3263305093172455031620283 4894957639758682547430425)
        ·
          refine ⟨3671218229819011910572819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4894957639758682547430425 3671218229819011910572819)
          ·
            refine ⟨5506827344728517865859229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3671218229819011910572819 5506827344728517865859229)
            ·
              refine ⟨2065060254273194199697211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5506827344728517865859229 2065060254273194199697211)
              ·
                refine ⟨3097590381409791299545817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065060254273194199697211 3097590381409791299545817)
                ·
                  refine ⟨2323192786057343474659363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3097590381409791299545817 2323192786057343474659363)
                  ·
                    refine ⟨3484789179086015211989045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2323192786057343474659363 3484789179086015211989045)
                    ·
                      refine ⟨326698985539313926123973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3484789179086015211989045 326698985539313926123973)
                      ·
                        rfl

theorem cell23_636244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_636244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636244 prefixEnd_636244 := by exact prefixLift 636244
  have htrace : WordTrace (prefixWord ++ tailWord_636244) baseStart_636244 baseEnd_636244 := by
    simpa [prefixWord, tailWord_636244, baseEnd_636244] using wordTrace_append hprefix tailTrace_636244
  have hstable : (prefixWord ++ tailWord_636244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636244).length < 2 ^ (prefixWord ++ tailWord_636244).sum := by decide
  have hdescent : baseEnd_636244 < baseStart_636244 := by decide
  rcases family_descends (prefixWord ++ tailWord_636244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636258 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_636258 : Nat := 118140960795 + 636258 * 2 ^ 59
def prefixEnd_636258 : Nat := 4983230072969 + 3 ^ 40 * 636258 * 2
def baseEnd_636258 : Nat := 326706174268476871348909

theorem tailTrace_636258 : CollatzResearch.WordTrace tailWord_636258 prefixEnd_636258 326706174268476871348909 := by
  unfold tailWord_636258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5801558932238351265077357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15470823819302270040206285 5801558932238351265077357)
  ·
    refine ⟨2175584599589381724404009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5801558932238351265077357 2175584599589381724404009)
    ·
      refine ⟨1631688449692036293303007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2175584599589381724404009 1631688449692036293303007)
      ·
        refine ⟨2447532674538054439954511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1631688449692036293303007 2447532674538054439954511)
        ·
          refine ⟨3671299011807081659931767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447532674538054439954511 3671299011807081659931767)
          ·
            refine ⟨5506948517710622489897651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3671299011807081659931767 5506948517710622489897651)
            ·
              refine ⟨8260422776565933734846477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5506948517710622489897651 8260422776565933734846477)
              ·
                refine ⟨3097658541212225150567429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8260422776565933734846477 3097658541212225150567429)
                ·
                  refine ⟨580810976477292215731393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3097658541212225150567429 580810976477292215731393)
                  ·
                    refine ⟨435608232357969161798545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 580810976477292215731393 435608232357969161798545)
                    ·
                      refine ⟨326706174268476871348909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 435608232357969161798545 326706174268476871348909)
                      ·
                        rfl

theorem cell23_636258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_636258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636258 prefixEnd_636258 := by exact prefixLift 636258
  have htrace : WordTrace (prefixWord ++ tailWord_636258) baseStart_636258 baseEnd_636258 := by
    simpa [prefixWord, tailWord_636258, baseEnd_636258] using wordTrace_append hprefix tailTrace_636258
  have hstable : (prefixWord ++ tailWord_636258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636258).length < 2 ^ (prefixWord ++ tailWord_636258).sum := by decide
  have hdescent : baseEnd_636258 < baseStart_636258 := by decide
  rcases family_descends (prefixWord ++ tailWord_636258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636274 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_636274 : Nat := 118140960795 + 636274 * 2 ^ 59
def prefixEnd_636274 : Nat := 4983230072969 + 3 ^ 40 * 636274 * 2
def baseEnd_636274 : Nat := 326714389958948808748835

theorem tailTrace_636274 : CollatzResearch.WordTrace tailWord_636274 prefixEnd_636274 326714389958948808748835 := by
  unfold tailWord_636274
  simp only [CollatzResearch.WordTrace]
  refine ⟨5801704824223859948222969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15471212864596959861927917 5801704824223859948222969)
  ·
    refine ⟨4351278618167894961167227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5801704824223859948222969 4351278618167894961167227)
    ·
      refine ⟨6526917927251842441750841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4351278618167894961167227 6526917927251842441750841)
      ·
        refine ⟨4895188445438881831313131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6526917927251842441750841 4895188445438881831313131)
        ·
          refine ⟨7342782668158322746969697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4895188445438881831313131 7342782668158322746969697)
          ·
            refine ⟨5507087001118742060227273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7342782668158322746969697 5507087001118742060227273)
            ·
              refine ⟨4130315250839056545170455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5507087001118742060227273 4130315250839056545170455)
              ·
                refine ⟨6195472876258584817755683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4130315250839056545170455 6195472876258584817755683)
                ·
                  refine ⟨9293209314387877226633525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6195472876258584817755683 9293209314387877226633525)
                  ·
                    refine ⟨871238373223863489996893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9293209314387877226633525 871238373223863489996893)
                    ·
                      refine ⟨326714389958948808748835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 871238373223863489996893 326714389958948808748835)
                      ·
                        rfl

theorem cell23_636274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_636274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636274 prefixEnd_636274 := by exact prefixLift 636274
  have htrace : WordTrace (prefixWord ++ tailWord_636274) baseStart_636274 baseEnd_636274 := by
    simpa [prefixWord, tailWord_636274, baseEnd_636274] using wordTrace_append hprefix tailTrace_636274
  have hstable : (prefixWord ++ tailWord_636274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636274).length < 2 ^ (prefixWord ++ tailWord_636274).sum := by decide
  have hdescent : baseEnd_636274 < baseStart_636274 := by decide
  rcases family_descends (prefixWord ++ tailWord_636274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636287 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 5]
def baseStart_636287 : Nat := 118140960795 + 636287 * 2 ^ 59
def prefixEnd_636287 : Nat := 4983230072969 + 3 ^ 40 * 636287 * 2
def baseEnd_636287 : Nat := 326721065207457257886275

theorem tailTrace_636287 : CollatzResearch.WordTrace tailWord_636287 prefixEnd_636287 326721065207457257886275 := by
  unfold tailWord_636287
  simp only [CollatzResearch.WordTrace]
  refine ⟨23207293445848343013115115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15471528963898895342076743 23207293445848343013115115)
  ·
    refine ⟨34810940168772514519672673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23207293445848343013115115 34810940168772514519672673)
    ·
      refine ⟨26108205126579385889754505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34810940168772514519672673 26108205126579385889754505)
      ·
        refine ⟨19581153844934539417315879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26108205126579385889754505 19581153844934539417315879)
        ·
          refine ⟨29371730767401809125973819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19581153844934539417315879 29371730767401809125973819)
          ·
            refine ⟨44057596151102713688960729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29371730767401809125973819 44057596151102713688960729)
            ·
              refine ⟨33043197113327035266720547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44057596151102713688960729 33043197113327035266720547)
              ·
                refine ⟨49564795669990552900080821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33043197113327035266720547 49564795669990552900080821)
                ·
                  refine ⟨4646699594061614334382577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49564795669990552900080821 4646699594061614334382577)
                  ·
                    refine ⟨3485024695546210750786933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4646699594061614334382577 3485024695546210750786933)
                    ·
                      refine ⟨326721065207457257886275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3485024695546210750786933 326721065207457257886275)
                      ·
                        rfl

theorem cell23_636287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_636287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636287 prefixEnd_636287 := by exact prefixLift 636287
  have htrace : WordTrace (prefixWord ++ tailWord_636287) baseStart_636287 baseEnd_636287 := by
    simpa [prefixWord, tailWord_636287, baseEnd_636287] using wordTrace_append hprefix tailTrace_636287
  have hstable : (prefixWord ++ tailWord_636287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636287).length < 2 ^ (prefixWord ++ tailWord_636287).sum := by decide
  have hdescent : baseEnd_636287 < baseStart_636287 := by decide
  rcases family_descends (prefixWord ++ tailWord_636287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636341 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 5, 4]
def baseStart_636341 : Nat := 118140960795 + 636341 * 2 ^ 59
def prefixEnd_636341 : Nat := 4983230072969 + 3 ^ 40 * 636341 * 2
def baseEnd_636341 : Nat := 108916264387600015537009

theorem tailTrace_636341 : CollatzResearch.WordTrace tailWord_636341 prefixEnd_636341 108916264387600015537009 := by
  unfold tailWord_636341
  simp only [CollatzResearch.WordTrace]
  refine ⟨23209262987652710235580877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15472841991768473490387251 23209262987652710235580877)
  ·
    refine ⟨8703473620369766338342829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23209262987652710235580877 8703473620369766338342829)
    ·
      refine ⟨3263802607638662376878561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8703473620369766338342829 3263802607638662376878561)
      ·
        refine ⟨2447851955728996782658921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3263802607638662376878561 2447851955728996782658921)
        ·
          refine ⟨1835888966796747586994191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2447851955728996782658921 1835888966796747586994191)
          ·
            refine ⟨2753833450195121380491287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835888966796747586994191 2753833450195121380491287)
            ·
              refine ⟨4130750175292682070736931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753833450195121380491287 4130750175292682070736931)
              ·
                refine ⟨6196125262939023106105397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4130750175292682070736931 6196125262939023106105397)
                ·
                  refine ⟨580886743400533416197381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6196125262939023106105397 580886743400533416197381)
                  ·
                    refine ⟨108916264387600015537009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 580886743400533416197381 108916264387600015537009)
                    ·
                      rfl

theorem cell23_636341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_636341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636341 prefixEnd_636341 := by exact prefixLift 636341
  have htrace : WordTrace (prefixWord ++ tailWord_636341) baseStart_636341 baseEnd_636341 := by
    simpa [prefixWord, tailWord_636341, baseEnd_636341] using wordTrace_append hprefix tailTrace_636341
  have hstable : (prefixWord ++ tailWord_636341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636341).length < 2 ^ (prefixWord ++ tailWord_636341).sum := by decide
  have hdescent : baseEnd_636341 < baseStart_636341 := by decide
  rcases family_descends (prefixWord ++ tailWord_636341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636347 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 9]
def baseStart_636347 : Nat := 118140960795 + 636347 * 2 ^ 59
def prefixEnd_636347 : Nat := 4983230072969 + 3 ^ 40 * 636347 * 2
def baseEnd_636347 : Nat := 326751874046727023135999

theorem tailTrace_636347 : CollatzResearch.WordTrace tailWord_636347 prefixEnd_636347 326751874046727023135999 := by
  unfold tailWord_636347
  simp only [CollatzResearch.WordTrace]
  refine ⟨23209481825630973260299295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15472987883753982173532863 23209481825630973260299295)
  ·
    refine ⟨34814222738446459890448943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23209481825630973260299295 34814222738446459890448943)
    ·
      refine ⟨52221334107669689835673415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34814222738446459890448943 52221334107669689835673415)
      ·
        refine ⟨78332001161504534753510123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52221334107669689835673415 78332001161504534753510123)
        ·
          refine ⟨117498001742256802130265185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78332001161504534753510123 117498001742256802130265185)
          ·
            refine ⟨88123501306692601597698889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117498001742256802130265185 88123501306692601597698889)
            ·
              refine ⟨66092625980019451198274167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88123501306692601597698889 66092625980019451198274167)
              ·
                refine ⟨99138938970029176797411251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66092625980019451198274167 99138938970029176797411251)
                ·
                  refine ⟨148708408455043765196116877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99138938970029176797411251 148708408455043765196116877)
                  ·
                    refine ⟨55765653170641411948543829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 148708408455043765196116877 55765653170641411948543829)
                    ·
                      refine ⟨326751874046727023135999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 55765653170641411948543829 326751874046727023135999)
                      ·
                        rfl

theorem cell23_636347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_636347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636347 prefixEnd_636347 := by exact prefixLift 636347
  have htrace : WordTrace (prefixWord ++ tailWord_636347) baseStart_636347 baseEnd_636347 := by
    simpa [prefixWord, tailWord_636347, baseEnd_636347] using wordTrace_append hprefix tailTrace_636347
  have hstable : (prefixWord ++ tailWord_636347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636347).length < 2 ^ (prefixWord ++ tailWord_636347).sum := by decide
  have hdescent : baseEnd_636347 < baseStart_636347 := by decide
  rcases family_descends (prefixWord ++ tailWord_636347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636384 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 3, 5]
def baseStart_636384 : Nat := 118140960795 + 636384 * 2 ^ 59
def prefixEnd_636384 : Nat := 4983230072969 + 3 ^ 40 * 636384 * 2
def baseEnd_636384 : Nat := 108923624276981126124443

theorem tailTrace_636384 : CollatzResearch.WordTrace tailWord_636384 prefixEnd_636384 108923624276981126124443 := by
  unfold tailWord_636384
  simp only [CollatzResearch.WordTrace]
  refine ⟨11605415663248464289698103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15473887550997952386264137 11605415663248464289698103)
  ·
    refine ⟨17408123494872696434547155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11605415663248464289698103 17408123494872696434547155)
    ·
      refine ⟨26112185242309044651820733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17408123494872696434547155 26112185242309044651820733)
      ·
        refine ⟨9792069465865891744432775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26112185242309044651820733 9792069465865891744432775)
        ·
          refine ⟨14688104198798837616649163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9792069465865891744432775 14688104198798837616649163)
          ·
            refine ⟨22032156298198256424973745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14688104198798837616649163 22032156298198256424973745)
            ·
              refine ⟨16524117223648692318730309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22032156298198256424973745 16524117223648692318730309)
              ·
                refine ⟨3098271979434129809761933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16524117223648692318730309 3098271979434129809761933)
                ·
                  refine ⟨1161851992287798678660725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3098271979434129809761933 1161851992287798678660725)
                  ·
                    refine ⟨108923624276981126124443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1161851992287798678660725 108923624276981126124443)
                    ·
                      rfl

theorem cell23_636384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 3, 5].length) (baseStart_636384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636384 prefixEnd_636384 := by exact prefixLift 636384
  have htrace : WordTrace (prefixWord ++ tailWord_636384) baseStart_636384 baseEnd_636384 := by
    simpa [prefixWord, tailWord_636384, baseEnd_636384] using wordTrace_append hprefix tailTrace_636384
  have hstable : (prefixWord ++ tailWord_636384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636384).length < 2 ^ (prefixWord ++ tailWord_636384).sum := by decide
  have hdescent : baseEnd_636384 < baseStart_636384 := by decide
  rcases family_descends (prefixWord ++ tailWord_636384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636398 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_636398 : Nat := 118140960795 + 636398 * 2 ^ 59
def prefixEnd_636398 : Nat := 4983230072969 + 3 ^ 40 * 636398 * 2
def baseEnd_636398 : Nat := 326778061560106323598265

theorem tailTrace_636398 : CollatzResearch.WordTrace tailWord_636398 prefixEnd_636398 326778061560106323598265 := by
  unfold tailWord_636398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2901417743555776121300731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15474227965630805980270565 2901417743555776121300731)
  ·
    refine ⟨4352126615333664181951097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2901417743555776121300731 4352126615333664181951097)
    ·
      refine ⟨3264094961500248136463323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4352126615333664181951097 3264094961500248136463323)
      ·
        refine ⟨4896142442250372204694985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3264094961500248136463323 4896142442250372204694985)
        ·
          refine ⟨3672106831687779153521239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4896142442250372204694985 3672106831687779153521239)
          ·
            refine ⟨5508160247531668730281859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3672106831687779153521239 5508160247531668730281859)
            ·
              refine ⟨8262240371297503095422789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5508160247531668730281859 8262240371297503095422789)
              ·
                refine ⟨1549170069618281830391773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8262240371297503095422789 1549170069618281830391773)
                ·
                  refine ⟨580938776106855686396915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1549170069618281830391773 580938776106855686396915)
                  ·
                    refine ⟨871408164160283529595373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 580938776106855686396915 871408164160283529595373)
                    ·
                      refine ⟨326778061560106323598265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 871408164160283529595373 326778061560106323598265)
                      ·
                        rfl

theorem cell23_636398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_636398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636398 prefixEnd_636398 := by exact prefixLift 636398
  have htrace : WordTrace (prefixWord ++ tailWord_636398) baseStart_636398 baseEnd_636398 := by
    simpa [prefixWord, tailWord_636398, baseEnd_636398] using wordTrace_append hprefix tailTrace_636398
  have hstable : (prefixWord ++ tailWord_636398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636398).length < 2 ^ (prefixWord ++ tailWord_636398).sum := by decide
  have hdescent : baseEnd_636398 < baseStart_636398 := by decide
  rcases family_descends (prefixWord ++ tailWord_636398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636401 : List Nat := [1, 2, 2, 2, 3, 2, 1, 4, 1, 5]
def baseStart_636401 : Nat := 118140960795 + 636401 * 2 ^ 59
def prefixEnd_636401 : Nat := 4983230072969 + 3 ^ 40 * 636401 * 2
def baseEnd_636401 : Nat := 108926534000689937286917

theorem tailTrace_636401 : CollatzResearch.WordTrace tailWord_636401 prefixEnd_636401 108926534000689937286917 := by
  unfold tailWord_636401
  simp only [CollatzResearch.WordTrace]
  refine ⟨23211451367435340482765057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15474300911623560321843371 23211451367435340482765057)
  ·
    refine ⟨17408588525576505362073793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23211451367435340482765057 17408588525576505362073793)
    ·
      refine ⟨13056441394182379021555345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17408588525576505362073793 13056441394182379021555345)
      ·
        refine ⟨9792331045636784266166509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13056441394182379021555345 9792331045636784266166509)
        ·
          refine ⟨3672124142113794099812441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9792331045636784266166509 3672124142113794099812441)
          ·
            refine ⟨2754093106585345574859331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3672124142113794099812441 2754093106585345574859331)
            ·
              refine ⟨4131139659878018362288997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754093106585345574859331 4131139659878018362288997)
              ·
                refine ⟨774588686227128442929187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4131139659878018362288997 774588686227128442929187)
                ·
                  refine ⟨1161883029340692664393781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 774588686227128442929187 1161883029340692664393781)
                  ·
                    refine ⟨108926534000689937286917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1161883029340692664393781 108926534000689937286917)
                    ·
                      rfl

theorem cell23_636401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_636401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636401 prefixEnd_636401 := by exact prefixLift 636401
  have htrace : WordTrace (prefixWord ++ tailWord_636401) baseStart_636401 baseEnd_636401 := by
    simpa [prefixWord, tailWord_636401, baseEnd_636401] using wordTrace_append hprefix tailTrace_636401
  have hstable : (prefixWord ++ tailWord_636401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636401).length < 2 ^ (prefixWord ++ tailWord_636401).sum := by decide
  have hdescent : baseEnd_636401 < baseStart_636401 := by decide
  rcases family_descends (prefixWord ++ tailWord_636401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636458 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_636458 : Nat := 118140960795 + 636458 * 2 ^ 59
def prefixEnd_636458 : Nat := 4983230072969 + 3 ^ 40 * 636458 * 2
def baseEnd_636458 : Nat := 326808870399376088847989

theorem tailTrace_636458 : CollatzResearch.WordTrace tailWord_636458 prefixEnd_636458 326808870399376088847989 := by
  unfold tailWord_636458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5803382582057209804397507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15475686885485892811726685 5803382582057209804397507)
  ·
    refine ⟨8705073873085814706596261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5803382582057209804397507 8705073873085814706596261)
    ·
      refine ⟨1632201351203590257486799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8705073873085814706596261 1632201351203590257486799)
      ·
        refine ⟨2448302026805385386230199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632201351203590257486799 2448302026805385386230199)
        ·
          refine ⟨3672453040208078079345299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2448302026805385386230199 3672453040208078079345299)
          ·
            refine ⟨5508679560312117119017949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3672453040208078079345299 5508679560312117119017949)
            ·
              refine ⟨2065754835117043919631731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5508679560312117119017949 2065754835117043919631731)
              ·
                refine ⟨3098632252675565879447597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065754835117043919631731 3098632252675565879447597)
                ·
                  refine ⟨1161987094753337204792849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3098632252675565879447597 1161987094753337204792849)
                  ·
                    refine ⟨871490321065002903594637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1161987094753337204792849 871490321065002903594637)
                    ·
                      refine ⟨326808870399376088847989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 871490321065002903594637 326808870399376088847989)
                      ·
                        rfl

theorem cell23_636458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_636458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636458 prefixEnd_636458 := by exact prefixLift 636458
  have htrace : WordTrace (prefixWord ++ tailWord_636458) baseStart_636458 baseEnd_636458 := by
    simpa [prefixWord, tailWord_636458, baseEnd_636458] using wordTrace_append hprefix tailTrace_636458
  have hstable : (prefixWord ++ tailWord_636458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636458).length < 2 ^ (prefixWord ++ tailWord_636458).sum := by decide
  have hdescent : baseEnd_636458 < baseStart_636458 := by decide
  rcases family_descends (prefixWord ++ tailWord_636458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636471 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 3]
def baseStart_636471 : Nat := 118140960795 + 636471 * 2 ^ 59
def prefixEnd_636471 : Nat := 4983230072969 + 3 ^ 40 * 636471 * 2
def baseEnd_636471 : Nat := 326815545647884537985429

theorem tailTrace_636471 : CollatzResearch.WordTrace tailWord_636471 prefixEnd_636471 326815545647884537985429 := by
  unfold tailWord_636471
  simp only [CollatzResearch.WordTrace]
  refine ⟨23214004477181742437813267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15476002984787828291875511 23214004477181742437813267)
  ·
    refine ⟨34821006715772613656719901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23214004477181742437813267 34821006715772613656719901)
    ·
      refine ⟨13057877518414730121269963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34821006715772613656719901 13057877518414730121269963)
      ·
        refine ⟨19586816277622095181904945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13057877518414730121269963 19586816277622095181904945)
        ·
          refine ⟨14690112208216571386428709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19586816277622095181904945 14690112208216571386428709)
          ·
            refine ⟨2754396039040607134955383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14690112208216571386428709 2754396039040607134955383)
            ·
              refine ⟨4131594058560910702433075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754396039040607134955383 4131594058560910702433075)
              ·
                refine ⟨6197391087841366053649613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4131594058560910702433075 6197391087841366053649613)
                ·
                  refine ⟨2324021657940512270118605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6197391087841366053649613 2324021657940512270118605)
                  ·
                    refine ⟨871508121727692101294477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2324021657940512270118605 871508121727692101294477)
                    ·
                      refine ⟨326815545647884537985429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 871508121727692101294477 326815545647884537985429)
                      ·
                        rfl

theorem cell23_636471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_636471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636471 prefixEnd_636471 := by exact prefixLift 636471
  have htrace : WordTrace (prefixWord ++ tailWord_636471) baseStart_636471 baseEnd_636471 := by
    simpa [prefixWord, tailWord_636471, baseEnd_636471] using wordTrace_append hprefix tailTrace_636471
  have hstable : (prefixWord ++ tailWord_636471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636471).length < 2 ^ (prefixWord ++ tailWord_636471).sum := by decide
  have hdescent : baseEnd_636471 < baseStart_636471 := by decide
  rcases family_descends (prefixWord ++ tailWord_636471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636551 : List Nat := [1, 1, 4, 2, 1, 3, 1, 3, 7]
def baseStart_636551 : Nat := 118140960795 + 636551 * 2 ^ 59
def prefixEnd_636551 : Nat := 4983230072969 + 3 ^ 40 * 636551 * 2
def baseEnd_636551 : Nat := 36317402677804913887229

theorem tailTrace_636551 : CollatzResearch.WordTrace tailWord_636551 prefixEnd_636551 36317402677804913887229 := by
  unfold tailWord_636551
  simp only [CollatzResearch.WordTrace]
  refine ⟨23216922316891916100725507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15477948211261277400483671 23216922316891916100725507)
  ·
    refine ⟨34825383475337874151088261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23216922316891916100725507 34825383475337874151088261)
    ·
      refine ⟨6529759401625851403329049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34825383475337874151088261 6529759401625851403329049)
      ·
        refine ⟨4897319551219388552496787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6529759401625851403329049 4897319551219388552496787)
        ·
          refine ⟨7345979326829082828745181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4897319551219388552496787 7345979326829082828745181)
          ·
            refine ⟨2754742247560906060779443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7345979326829082828745181 2754742247560906060779443)
            ·
              refine ⟨4132113371341359091169165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754742247560906060779443 4132113371341359091169165)
              ·
                refine ⟨1549542514253009659188437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4132113371341359091169165 1549542514253009659188437)
                ·
                  refine ⟨36317402677804913887229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1549542514253009659188437 36317402677804913887229)
                  ·
                    rfl

theorem cell23_636551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 7].length) (baseStart_636551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636551 prefixEnd_636551 := by exact prefixLift 636551
  have htrace : WordTrace (prefixWord ++ tailWord_636551) baseStart_636551 baseEnd_636551 := by
    simpa [prefixWord, tailWord_636551, baseEnd_636551] using wordTrace_append hprefix tailTrace_636551
  have hstable : (prefixWord ++ tailWord_636551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636551).length < 2 ^ (prefixWord ++ tailWord_636551).sum := by decide
  have hdescent : baseEnd_636551 < baseStart_636551 := by decide
  rcases family_descends (prefixWord ++ tailWord_636551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636558 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_636558 : Nat := 118140960795 + 636558 * 2 ^ 59
def prefixEnd_636558 : Nat := 4983230072969 + 3 ^ 40 * 636558 * 2
def baseEnd_636558 : Nat := 326860218464825697597529

theorem tailTrace_636558 : CollatzResearch.WordTrace tailWord_636558 prefixEnd_636558 326860218464825697597529 := by
  unfold tailWord_636558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2902147203483319537028791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15478118418577704197486885 2902147203483319537028791)
  ·
    refine ⟨4353220805224979305543187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2902147203483319537028791 4353220805224979305543187)
    ·
      refine ⟨6529831207837468958314781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4353220805224979305543187 6529831207837468958314781)
      ·
        refine ⟨2448686702939050859368043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6529831207837468958314781 2448686702939050859368043)
        ·
          refine ⟨3673030054408576289052065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2448686702939050859368043 3673030054408576289052065)
          ·
            refine ⟨2754772540806432216789049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3673030054408576289052065 2754772540806432216789049)
            ·
              refine ⟨2066079405604824162591787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2754772540806432216789049 2066079405604824162591787)
              ·
                refine ⟨3099119108407236243887681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066079405604824162591787 3099119108407236243887681)
                ·
                  refine ⟨2324339331305427182915761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3099119108407236243887681 2324339331305427182915761)
                  ·
                    refine ⟨1743254498479070387186821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2324339331305427182915761 1743254498479070387186821)
                    ·
                      refine ⟨326860218464825697597529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1743254498479070387186821 326860218464825697597529)
                      ·
                        rfl

theorem cell23_636558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_636558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636558 prefixEnd_636558 := by exact prefixLift 636558
  have htrace : WordTrace (prefixWord ++ tailWord_636558) baseStart_636558 baseEnd_636558 := by
    simpa [prefixWord, tailWord_636558, baseEnd_636558] using wordTrace_append hprefix tailTrace_636558
  have hstable : (prefixWord ++ tailWord_636558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636558).length < 2 ^ (prefixWord ++ tailWord_636558).sum := by decide
  have hdescent : baseEnd_636558 < baseStart_636558 := by decide
  rcases family_descends (prefixWord ++ tailWord_636558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636561 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 3]
def baseStart_636561 : Nat := 118140960795 + 636561 * 2 ^ 59
def prefixEnd_636561 : Nat := 4983230072969 + 3 ^ 40 * 636561 * 2
def baseEnd_636561 : Nat := 326861758906789185860015

theorem tailTrace_636561 : CollatzResearch.WordTrace tailWord_636561 prefixEnd_636561 326861758906789185860015 := by
  unfold tailWord_636561
  simp only [CollatzResearch.WordTrace]
  refine ⟨23217287046855687808589537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15478191364570458539059691 23217287046855687808589537)
  ·
    refine ⟨17412965285141765856442153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23217287046855687808589537 17412965285141765856442153)
    ·
      refine ⟨13059723963856324392331615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17412965285141765856442153 13059723963856324392331615)
      ·
        refine ⟨19589585945784486588497423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13059723963856324392331615 19589585945784486588497423)
        ·
          refine ⟨29384378918676729882746135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19589585945784486588497423 29384378918676729882746135)
          ·
            refine ⟨44076568378015094824119203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29384378918676729882746135 44076568378015094824119203)
            ·
              refine ⟨66114852567022642236178805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44076568378015094824119203 66114852567022642236178805)
              ·
                refine ⟨6198267428158372709641763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66114852567022642236178805 6198267428158372709641763)
                ·
                  refine ⟨9297401142237559064462645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6198267428158372709641763 9297401142237559064462645)
                  ·
                    refine ⟨871631357084771162293373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9297401142237559064462645 871631357084771162293373)
                    ·
                      refine ⟨326861758906789185860015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 871631357084771162293373 326861758906789185860015)
                      ·
                        rfl

theorem cell23_636561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_636561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636561 prefixEnd_636561 := by exact prefixLift 636561
  have htrace : WordTrace (prefixWord ++ tailWord_636561) baseStart_636561 baseEnd_636561 := by
    simpa [prefixWord, tailWord_636561, baseEnd_636561] using wordTrace_append hprefix tailTrace_636561
  have hstable : (prefixWord ++ tailWord_636561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636561).length < 2 ^ (prefixWord ++ tailWord_636561).sum := by decide
  have hdescent : baseEnd_636561 < baseStart_636561 := by decide
  rcases family_descends (prefixWord ++ tailWord_636561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636581 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 1, 7]
def baseStart_636581 : Nat := 118140960795 + 636581 * 2 ^ 59
def prefixEnd_636581 : Nat := 4983230072969 + 3 ^ 40 * 636581 * 2
def baseEnd_636581 : Nat := 108957342839959702536641

theorem tailTrace_636581 : CollatzResearch.WordTrace tailWord_636581 prefixEnd_636581 108957342839959702536641 := by
  unfold tailWord_636581
  simp only [CollatzResearch.WordTrace]
  refine ⟨23218016506783231224317597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15478677671188820816211731 23218016506783231224317597)
  ·
    refine ⟨8706756190043711709119099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23218016506783231224317597 8706756190043711709119099)
    ·
      refine ⟨13060134285065567563678649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8706756190043711709119099 13060134285065567563678649)
      ·
        refine ⟨9795100713799175672758987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13060134285065567563678649 9795100713799175672758987)
        ·
          refine ⟨14692651070698763509138481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9795100713799175672758987 14692651070698763509138481)
          ·
            refine ⟨11019488303024072631853861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14692651070698763509138481 11019488303024072631853861)
            ·
              refine ⟨2066154056817013618472599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11019488303024072631853861 2066154056817013618472599)
              ·
                refine ⟨3099231085225520427708899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066154056817013618472599 3099231085225520427708899)
                ·
                  refine ⟨4648846627838280641563349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099231085225520427708899 4648846627838280641563349)
                  ·
                    refine ⟨108957342839959702536641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4648846627838280641563349 108957342839959702536641)
                    ·
                      rfl

theorem cell23_636581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_636581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636581 prefixEnd_636581 := by exact prefixLift 636581
  have htrace : WordTrace (prefixWord ++ tailWord_636581) baseStart_636581 baseEnd_636581 := by
    simpa [prefixWord, tailWord_636581, baseEnd_636581] using wordTrace_append hprefix tailTrace_636581
  have hstable : (prefixWord ++ tailWord_636581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636581).length < 2 ^ (prefixWord ++ tailWord_636581).sum := by decide
  have hdescent : baseEnd_636581 < baseStart_636581 := by decide
  rcases family_descends (prefixWord ++ tailWord_636581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636591 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 5]
def baseStart_636591 : Nat := 118140960795 + 636591 * 2 ^ 59
def prefixEnd_636591 : Nat := 4983230072969 + 3 ^ 40 * 636591 * 2
def baseEnd_636591 : Nat := 326877163326424068484877

theorem tailTrace_636591 : CollatzResearch.WordTrace tailWord_636591 prefixEnd_636591 326877163326424068484877 := by
  unfold tailWord_636591
  simp only [CollatzResearch.WordTrace]
  refine ⟨23218381236747002932181627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15478920824498001954787751 23218381236747002932181627)
  ·
    refine ⟨34827571855120504398272441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23218381236747002932181627 34827571855120504398272441)
    ·
      refine ⟨26120678891340378298704331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34827571855120504398272441 26120678891340378298704331)
      ·
        refine ⟨39181018337010567448056497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26120678891340378298704331 39181018337010567448056497)
        ·
          refine ⟨29385763752757925586042373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39181018337010567448056497 29385763752757925586042373)
          ·
            refine ⟨5509830703642111047382945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29385763752757925586042373 5509830703642111047382945)
            ·
              refine ⟨4132373027731583285537209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5509830703642111047382945 4132373027731583285537209)
              ·
                refine ⟨3099279770798687464152907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4132373027731583285537209 3099279770798687464152907)
                ·
                  refine ⟨4648919656198031196229361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099279770798687464152907 4648919656198031196229361)
                  ·
                    refine ⟨3486689742148523397172021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4648919656198031196229361 3486689742148523397172021)
                    ·
                      refine ⟨326877163326424068484877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3486689742148523397172021 326877163326424068484877)
                      ·
                        rfl

theorem cell23_636591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_636591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636591 prefixEnd_636591 := by exact prefixLift 636591
  have htrace : WordTrace (prefixWord ++ tailWord_636591) baseStart_636591 baseEnd_636591 := by
    simpa [prefixWord, tailWord_636591, baseEnd_636591] using wordTrace_append hprefix tailTrace_636591
  have hstable : (prefixWord ++ tailWord_636591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636591).length < 2 ^ (prefixWord ++ tailWord_636591).sum := by decide
  have hdescent : baseEnd_636591 < baseStart_636591 := by decide
  rcases family_descends (prefixWord ++ tailWord_636591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636681 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 7]
def baseStart_636681 : Nat := 118140960795 + 636681 * 2 ^ 59
def prefixEnd_636681 : Nat := 4983230072969 + 3 ^ 40 * 636681 * 2
def baseEnd_636681 : Nat := 326923376585328716359463

theorem tailTrace_636681 : CollatzResearch.WordTrace tailWord_636681 prefixEnd_636681 326923376585328716359463 := by
  unfold tailWord_636681
  simp only [CollatzResearch.WordTrace]
  refine ⟨23221663806420948302957897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15481109204280632201971931 23221663806420948302957897)
  ·
    refine ⟨17416247854815711227218423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23221663806420948302957897 17416247854815711227218423)
    ·
      refine ⟨26124371782223566840827635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17416247854815711227218423 26124371782223566840827635)
      ·
        refine ⟨39186557673335350261241453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26124371782223566840827635 39186557673335350261241453)
        ·
          refine ⟨14694959127500756347965545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39186557673335350261241453 14694959127500756347965545)
          ·
            refine ⟨11021219345625567260974159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14694959127500756347965545 11021219345625567260974159)
            ·
              refine ⟨16531829018438350891461239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11021219345625567260974159 16531829018438350891461239)
              ·
                refine ⟨24797743527657526337191859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16531829018438350891461239 24797743527657526337191859)
                ·
                  refine ⟨37196615291486289505787789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24797743527657526337191859 37196615291486289505787789)
                  ·
                    refine ⟨13948730734307358564670421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37196615291486289505787789 13948730734307358564670421)
                    ·
                      refine ⟨326923376585328716359463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13948730734307358564670421 326923376585328716359463)
                      ·
                        rfl

theorem cell23_636681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_636681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636681 prefixEnd_636681 := by exact prefixLift 636681
  have htrace : WordTrace (prefixWord ++ tailWord_636681) baseStart_636681 baseEnd_636681 := by
    simpa [prefixWord, tailWord_636681, baseEnd_636681] using wordTrace_append hprefix tailTrace_636681
  have hstable : (prefixWord ++ tailWord_636681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636681).length < 2 ^ (prefixWord ++ tailWord_636681).sum := by decide
  have hdescent : baseEnd_636681 < baseStart_636681 := by decide
  rcases family_descends (prefixWord ++ tailWord_636681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636705 : List Nat := [1, 2, 3, 2, 1, 4, 1, 3, 1, 5]
def baseStart_636705 : Nat := 118140960795 + 636705 * 2 ^ 59
def prefixEnd_636705 : Nat := 4983230072969 + 3 ^ 40 * 636705 * 2
def baseEnd_636705 : Nat := 108978566707012207486451

theorem tailTrace_636705 : CollatzResearch.WordTrace tailWord_636705 prefixEnd_636705 108978566707012207486451 := by
  unfold tailWord_636705
  simp only [CollatzResearch.WordTrace]
  refine ⟨23222539158334000401831569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15481692772222666934554379 23222539158334000401831569)
  ·
    refine ⟨17416904368750500301373677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23222539158334000401831569 17416904368750500301373677)
    ·
      refine ⟨6531339138281437613015129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17416904368750500301373677 6531339138281437613015129)
      ·
        refine ⟨4898504353711078209761347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6531339138281437613015129 4898504353711078209761347)
        ·
          refine ⟨7347756530566617314642021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4898504353711078209761347 7347756530566617314642021)
          ·
            refine ⟨1377704349481240746495379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7347756530566617314642021 1377704349481240746495379)
            ·
              refine ⟨2066556524221861119743069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377704349481240746495379 2066556524221861119743069)
              ·
                refine ⟨774958696583197919903651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2066556524221861119743069 774958696583197919903651)
                ·
                  refine ⟨1162438044874796879855477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 774958696583197919903651 1162438044874796879855477)
                  ·
                    refine ⟨108978566707012207486451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1162438044874796879855477 108978566707012207486451)
                    ·
                      rfl

theorem cell23_636705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_636705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636705 prefixEnd_636705 := by exact prefixLift 636705
  have htrace : WordTrace (prefixWord ++ tailWord_636705) baseStart_636705 baseEnd_636705 := by
    simpa [prefixWord, tailWord_636705, baseEnd_636705] using wordTrace_append hprefix tailTrace_636705
  have hstable : (prefixWord ++ tailWord_636705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636705).length < 2 ^ (prefixWord ++ tailWord_636705).sum := by decide
  have hdescent : baseEnd_636705 < baseStart_636705 := by decide
  rcases family_descends (prefixWord ++ tailWord_636705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636728 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_636728 : Nat := 118140960795 + 636728 * 2 ^ 59
def prefixEnd_636728 : Nat := 4983230072969 + 3 ^ 40 * 636728 * 2
def baseEnd_636728 : Nat := 326947510176090032471747

theorem tailTrace_636728 : CollatzResearch.WordTrace tailWord_636728 prefixEnd_636728 326947510176090032471747 := by
  unfold tailWord_636728
  simp only [CollatzResearch.WordTrace]
  refine ⟨11611689018625337664959419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15482252024833783553279225 11611689018625337664959419)
  ·
    refine ⟨17417533527938006497439129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11611689018625337664959419 17417533527938006497439129)
    ·
      refine ⟨13063150145953504873079347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17417533527938006497439129 13063150145953504873079347)
      ·
        refine ⟨19594725218930257309619021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13063150145953504873079347 19594725218930257309619021)
        ·
          refine ⟨7348021957098846491107133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19594725218930257309619021 7348021957098846491107133)
          ·
            refine ⟨2755508233912067434165175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7348021957098846491107133 2755508233912067434165175)
            ·
              refine ⟨4133262350868101151247763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2755508233912067434165175 4133262350868101151247763)
              ·
                refine ⟨6199893526302151726871645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4133262350868101151247763 6199893526302151726871645)
                ·
                  refine ⟨2324960072363306897576867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6199893526302151726871645 2324960072363306897576867)
                  ·
                    refine ⟨3487440108544960346365301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2324960072363306897576867 3487440108544960346365301)
                    ·
                      refine ⟨326947510176090032471747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3487440108544960346365301 326947510176090032471747)
                      ·
                        rfl

theorem cell23_636728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_636728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636728 prefixEnd_636728 := by exact prefixLift 636728
  have htrace : WordTrace (prefixWord ++ tailWord_636728) baseStart_636728 baseEnd_636728 := by
    simpa [prefixWord, tailWord_636728, baseEnd_636728] using wordTrace_append hprefix tailTrace_636728
  have hstable : (prefixWord ++ tailWord_636728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636728).length < 2 ^ (prefixWord ++ tailWord_636728).sum := by decide
  have hdescent : baseEnd_636728 < baseStart_636728 := by decide
  rcases family_descends (prefixWord ++ tailWord_636728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636849 : List Nat := [1, 2, 2, 4, 2, 2, 2, 1, 1, 4, 2]
def baseStart_636849 : Nat := 118140960795 + 636849 * 2 ^ 59
def prefixEnd_636849 : Nat := 4983230072969 + 3 ^ 40 * 636849 * 2
def baseEnd_636849 : Nat := 327009641335284059058691

theorem tailTrace_636849 : CollatzResearch.WordTrace tailWord_636849 prefixEnd_636849 327009641335284059058691 := by
  unfold tailWord_636849
  simp only [CollatzResearch.WordTrace]
  refine ⟨23227791269812312995073601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15485194179874875330049067 23227791269812312995073601)
  ·
    refine ⟨17420843452359234746305201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23227791269812312995073601 17420843452359234746305201)
    ·
      refine ⟨13065632589269426059728901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17420843452359234746305201 13065632589269426059728901)
      ·
        refine ⟨2449806110488017386199169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13065632589269426059728901 2449806110488017386199169)
        ·
          refine ⟨1837354582866013039649377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2449806110488017386199169 1837354582866013039649377)
          ·
            refine ⟨1378015937149509779737033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1837354582866013039649377 1378015937149509779737033)
            ·
              refine ⟨1033511952862132334802775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1378015937149509779737033 1033511952862132334802775)
              ·
                refine ⟨1550267929293198502204163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1033511952862132334802775 1550267929293198502204163)
                ·
                  refine ⟨2325401893939797753306245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550267929293198502204163 2325401893939797753306245)
                  ·
                    refine ⟨436012855113712078744921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2325401893939797753306245 436012855113712078744921)
                    ·
                      refine ⟨327009641335284059058691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 436012855113712078744921 327009641335284059058691)
                      ·
                        rfl

theorem cell23_636849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_636849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636849 prefixEnd_636849 := by exact prefixLift 636849
  have htrace : WordTrace (prefixWord ++ tailWord_636849) baseStart_636849 baseEnd_636849 := by
    simpa [prefixWord, tailWord_636849, baseEnd_636849] using wordTrace_append hprefix tailTrace_636849
  have hstable : (prefixWord ++ tailWord_636849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636849).length < 2 ^ (prefixWord ++ tailWord_636849).sum := by decide
  have hdescent : baseEnd_636849 < baseStart_636849 := by decide
  rcases family_descends (prefixWord ++ tailWord_636849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636872 : List Nat := [2, 1, 3, 1, 4, 1, 1, 5, 5]
def baseStart_636872 : Nat := 118140960795 + 636872 * 2 ^ 59
def prefixEnd_636872 : Nat := 4983230072969 + 3 ^ 40 * 636872 * 2
def baseEnd_636872 : Nat := 36335716821148607674565

theorem tailTrace_636872 : CollatzResearch.WordTrace tailWord_636872 prefixEnd_636872 36335716821148607674565 := by
  unfold tailWord_636872
  simp only [CollatzResearch.WordTrace]
  refine ⟨11614315074364493961580435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15485753432485991948773913 11614315074364493961580435)
  ·
    refine ⟨17421472611546740942370653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11614315074364493961580435 17421472611546740942370653)
    ·
      refine ⟨6533052229330027853388995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17421472611546740942370653 6533052229330027853388995)
      ·
        refine ⟨9799578343995041780083493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6533052229330027853388995 9799578343995041780083493)
        ·
          refine ⟨1837420939499070333765655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9799578343995041780083493 1837420939499070333765655)
          ·
            refine ⟨2756131409248605500648483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837420939499070333765655 2756131409248605500648483)
            ·
              refine ⟨4134197113872908250972725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756131409248605500648483 4134197113872908250972725)
              ·
                refine ⟨387580979425585148528693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4134197113872908250972725 387580979425585148528693)
                ·
                  refine ⟨36335716821148607674565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 387580979425585148528693 36335716821148607674565)
                  ·
                    rfl

theorem cell23_636872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 5].length) (baseStart_636872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636872 prefixEnd_636872 := by exact prefixLift 636872
  have htrace : WordTrace (prefixWord ++ tailWord_636872) baseStart_636872 baseEnd_636872 := by
    simpa [prefixWord, tailWord_636872, baseEnd_636872] using wordTrace_append hprefix tailTrace_636872
  have hstable : (prefixWord ++ tailWord_636872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636872).length < 2 ^ (prefixWord ++ tailWord_636872).sum := by decide
  have hdescent : baseEnd_636872 < baseStart_636872 := by decide
  rcases family_descends (prefixWord ++ tailWord_636872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636955 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 3]
def baseStart_636955 : Nat := 118140960795 + 636955 * 2 ^ 59
def prefixEnd_636955 : Nat := 4983230072969 + 3 ^ 40 * 636955 * 2
def baseEnd_636955 : Nat := 327064070284660644333203

theorem tailTrace_636955 : CollatzResearch.WordTrace tailWord_636955 prefixEnd_636955 327064070284660644333203 := by
  unfold tailWord_636955
  simp only [CollatzResearch.WordTrace]
  refine ⟨23231657407428293098432319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15487771604952195398954879 23231657407428293098432319)
  ·
    refine ⟨34847486111142439647648479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23231657407428293098432319 34847486111142439647648479)
    ·
      refine ⟨52271229166713659471472719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34847486111142439647648479 52271229166713659471472719)
      ·
        refine ⟨78406843750070489207209079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52271229166713659471472719 78406843750070489207209079)
        ·
          refine ⟨117610265625105733810813619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78406843750070489207209079 117610265625105733810813619)
          ·
            refine ⟨176415398437658600716220429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117610265625105733810813619 176415398437658600716220429)
            ·
              refine ⟨66155774414121975268582661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176415398437658600716220429 66155774414121975268582661)
              ·
                refine ⟨12404207702647870362859249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66155774414121975268582661 12404207702647870362859249)
                ·
                  refine ⟨9303155776985902772144437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12404207702647870362859249 9303155776985902772144437)
                  ·
                    refine ⟨872170854092428384888541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9303155776985902772144437 872170854092428384888541)
                    ·
                      refine ⟨327064070284660644333203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 872170854092428384888541 327064070284660644333203)
                      ·
                        rfl

theorem cell23_636955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 3].length) (baseStart_636955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636955 prefixEnd_636955 := by exact prefixLift 636955
  have htrace : WordTrace (prefixWord ++ tailWord_636955) baseStart_636955 baseEnd_636955 := by
    simpa [prefixWord, tailWord_636955, baseEnd_636955] using wordTrace_append hprefix tailTrace_636955
  have hstable : (prefixWord ++ tailWord_636955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636955).length < 2 ^ (prefixWord ++ tailWord_636955).sum := by decide
  have hdescent : baseEnd_636955 < baseStart_636955 := by decide
  rcases family_descends (prefixWord ++ tailWord_636955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636962 : List Nat := [3, 3, 1, 1, 1, 2, 3, 3, 6]
def baseStart_636962 : Nat := 118140960795 + 636962 * 2 ^ 59
def prefixEnd_636962 : Nat := 4983230072969 + 3 ^ 40 * 636962 * 2
def baseEnd_636962 : Nat := 36340851627693568549519

theorem tailTrace_636962 : CollatzResearch.WordTrace tailWord_636962 prefixEnd_636962 36340851627693568549519 := by
  unfold tailWord_636962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5807978179600733323484285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15487941812268622195958093 5807978179600733323484285)
  ·
    refine ⟨2177991817350274996306607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5807978179600733323484285 2177991817350274996306607)
    ·
      refine ⟨3266987726025412494459911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2177991817350274996306607 3266987726025412494459911)
      ·
        refine ⟨4900481589038118741689867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3266987726025412494459911 4900481589038118741689867)
        ·
          refine ⟨7350722383557178112534801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4900481589038118741689867 7350722383557178112534801)
          ·
            refine ⟨5513041787667883584401101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7350722383557178112534801 5513041787667883584401101)
            ·
              refine ⟨2067390670375456344150413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5513041787667883584401101 2067390670375456344150413)
              ·
                refine ⟨775271501390796129056405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2067390670375456344150413 775271501390796129056405)
                ·
                  refine ⟨36340851627693568549519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 775271501390796129056405 36340851627693568549519)
                  ·
                    rfl

theorem cell23_636962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_636962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636962 prefixEnd_636962 := by exact prefixLift 636962
  have htrace : WordTrace (prefixWord ++ tailWord_636962) baseStart_636962 baseEnd_636962 := by
    simpa [prefixWord, tailWord_636962, baseEnd_636962] using wordTrace_append hprefix tailTrace_636962
  have hstable : (prefixWord ++ tailWord_636962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636962).length < 2 ^ (prefixWord ++ tailWord_636962).sum := by decide
  have hdescent : baseEnd_636962 < baseStart_636962 := by decide
  rcases family_descends (prefixWord ++ tailWord_636962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_636999 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 2, 3, 2]
def baseStart_636999 : Nat := 118140960795 + 636999 * 2 ^ 59
def prefixEnd_636999 : Nat := 4983230072969 + 3 ^ 40 * 636999 * 2
def baseEnd_636999 : Nat := 327086663433458472183001

theorem tailTrace_636999 : CollatzResearch.WordTrace tailWord_636999 prefixEnd_636999 327086663433458472183001 := by
  unfold tailWord_636999
  simp only [CollatzResearch.WordTrace]
  refine ⟨23233262219268888613034051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15488841479512592408689367 23233262219268888613034051)
  ·
    refine ⟨34849893328903332919551077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23233262219268888613034051 34849893328903332919551077)
    ·
      refine ⟨6534354999169374922415827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34849893328903332919551077 6534354999169374922415827)
      ·
        refine ⟨9801532498754062383623741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6534354999169374922415827 9801532498754062383623741)
        ·
          refine ⟨3675574687032773393858903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9801532498754062383623741 3675574687032773393858903)
          ·
            refine ⟨5513362030549160090788355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3675574687032773393858903 5513362030549160090788355)
            ·
              refine ⟨8270043045823740136182533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5513362030549160090788355 8270043045823740136182533)
              ·
                refine ⟨1550633071091951275534225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8270043045823740136182533 1550633071091951275534225)
                ·
                  refine ⟨1162974803318963456650669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1550633071091951275534225 1162974803318963456650669)
                  ·
                    refine ⟨436115551244611296244001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1162974803318963456650669 436115551244611296244001)
                    ·
                      refine ⟨327086663433458472183001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 436115551244611296244001 327086663433458472183001)
                      ·
                        rfl

theorem cell23_636999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_636999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_636999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_636999 prefixEnd_636999 := by exact prefixLift 636999
  have htrace : WordTrace (prefixWord ++ tailWord_636999) baseStart_636999 baseEnd_636999 := by
    simpa [prefixWord, tailWord_636999, baseEnd_636999] using wordTrace_append hprefix tailTrace_636999
  have hstable : (prefixWord ++ tailWord_636999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_636999).length < 2 ^ (prefixWord ++ tailWord_636999).sum := by decide
  have hdescent : baseEnd_636999 < baseStart_636999 := by decide
  rcases family_descends (prefixWord ++ tailWord_636999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637046 : List Nat := [5, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_637046 : Nat := 118140960795 + 637046 * 2 ^ 59
def prefixEnd_637046 : Nat := 4983230072969 + 3 ^ 40 * 637046 * 2
def baseEnd_637046 : Nat := 327110797024219788295285

theorem tailTrace_637046 : CollatzResearch.WordTrace tailWord_637046 prefixEnd_637046 327110797024219788295285 := by
  unfold tailWord_637046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1452186028131163477499687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15489984300065743759996661 1452186028131163477499687)
  ·
    refine ⟨2178279042196745216249531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1452186028131163477499687 2178279042196745216249531)
    ·
      refine ⟨3267418563295117824374297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2178279042196745216249531 3267418563295117824374297)
      ·
        refine ⟨2450563922471338368280723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3267418563295117824374297 2450563922471338368280723)
        ·
          refine ⟨3675845883707007552421085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2450563922471338368280723 3675845883707007552421085)
          ·
            refine ⟨1378442206390127832157907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3675845883707007552421085 1378442206390127832157907)
            ·
              refine ⟨2067663309585191748236861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378442206390127832157907 2067663309585191748236861)
              ·
                refine ⟨775373741094446905588823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2067663309585191748236861 775373741094446905588823)
                ·
                  refine ⟨1163060611641670358383235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 775373741094446905588823 1163060611641670358383235)
                  ·
                    refine ⟨1744590917462505537574853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1163060611641670358383235 1744590917462505537574853)
                    ·
                      refine ⟨327110797024219788295285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1744590917462505537574853 327110797024219788295285)
                      ·
                        rfl

theorem cell23_637046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_637046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637046 prefixEnd_637046 := by exact prefixLift 637046
  have htrace : WordTrace (prefixWord ++ tailWord_637046) baseStart_637046 baseEnd_637046 := by
    simpa [prefixWord, tailWord_637046, baseEnd_637046] using wordTrace_append hprefix tailTrace_637046
  have hstable : (prefixWord ++ tailWord_637046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637046).length < 2 ^ (prefixWord ++ tailWord_637046).sum := by decide
  have hdescent : baseEnd_637046 < baseStart_637046 := by decide
  rcases family_descends (prefixWord ++ tailWord_637046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637063 : List Nat := [1, 1, 4, 2, 1, 1, 4, 4, 1, 2, 2]
def baseStart_637063 : Nat := 118140960795 + 637063 * 2 ^ 59
def prefixEnd_637063 : Nat := 4983230072969 + 3 ^ 40 * 637063 * 2
def baseEnd_637063 : Nat := 327119526195346221782707

theorem tailTrace_637063 : CollatzResearch.WordTrace tailWord_637063 prefixEnd_637063 327119526195346221782707 := by
  unfold tailWord_637063
  simp only [CollatzResearch.WordTrace]
  refine ⟨23235596491037027543363843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15490397660691351695575895 23235596491037027543363843)
  ·
    refine ⟨34853394736555541315045765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23235596491037027543363843 34853394736555541315045765)
    ·
      refine ⟨6535011513104163996571081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34853394736555541315045765 6535011513104163996571081)
      ·
        refine ⟨4901258634828122997428311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6535011513104163996571081 4901258634828122997428311)
        ·
          refine ⟨7351887952242184496142467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4901258634828122997428311 7351887952242184496142467)
          ·
            refine ⟨11027831928363276744213701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7351887952242184496142467 11027831928363276744213701)
            ·
              refine ⟨2067718486568114389540069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11027831928363276744213701 2067718486568114389540069)
              ·
                refine ⟨387697216231521448038763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2067718486568114389540069 387697216231521448038763)
                ·
                  refine ⟨581545824347282172058145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 387697216231521448038763 581545824347282172058145)
                  ·
                    refine ⟨436159368260461629043609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 581545824347282172058145 436159368260461629043609)
                    ·
                      refine ⟨327119526195346221782707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 436159368260461629043609 327119526195346221782707)
                      ·
                        rfl

theorem cell23_637063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_637063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637063 prefixEnd_637063 := by exact prefixLift 637063
  have htrace : WordTrace (prefixWord ++ tailWord_637063) baseStart_637063 baseEnd_637063 := by
    simpa [prefixWord, tailWord_637063, baseEnd_637063] using wordTrace_append hprefix tailTrace_637063
  have hstable : (prefixWord ++ tailWord_637063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637063).length < 2 ^ (prefixWord ++ tailWord_637063).sum := by decide
  have hdescent : baseEnd_637063 < baseStart_637063 := by decide
  rcases family_descends (prefixWord ++ tailWord_637063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637076 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_637076 : Nat := 118140960795 + 637076 * 2 ^ 59
def prefixEnd_637076 : Nat := 4983230072969 + 3 ^ 40 * 637076 * 2
def baseEnd_637076 : Nat := 327126201443854670920147

theorem tailTrace_637076 : CollatzResearch.WordTrace tailWord_637076 prefixEnd_637076 327126201443854670920147 := by
  unfold tailWord_637076
  simp only [CollatzResearch.WordTrace]
  refine ⟨11618035319994965381793541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15490713759993287175724721 11618035319994965381793541)
  ·
    refine ⟨2178381622499056009086289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11618035319994965381793541 2178381622499056009086289)
    ·
      refine ⟨1633786216874292006814717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2178381622499056009086289 1633786216874292006814717)
      ·
        refine ⟨612669831327859502555519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1633786216874292006814717 612669831327859502555519)
        ·
          refine ⟨919004746991789253833279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612669831327859502555519 919004746991789253833279)
          ·
            refine ⟨1378507120487683880749919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919004746991789253833279 1378507120487683880749919)
            ·
              refine ⟨2067760680731525821124879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378507120487683880749919 2067760680731525821124879)
              ·
                refine ⟨3101641021097288731687319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2067760680731525821124879 3101641021097288731687319)
                ·
                  refine ⟨4652461531645933097530979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3101641021097288731687319 4652461531645933097530979)
                  ·
                    refine ⟨6978692297468899646296469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4652461531645933097530979 6978692297468899646296469)
                    ·
                      refine ⟨327126201443854670920147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6978692297468899646296469 327126201443854670920147)
                      ·
                        rfl

theorem cell23_637076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_637076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637076 prefixEnd_637076 := by exact prefixLift 637076
  have htrace : WordTrace (prefixWord ++ tailWord_637076) baseStart_637076 baseEnd_637076 := by
    simpa [prefixWord, tailWord_637076, baseEnd_637076] using wordTrace_append hprefix tailTrace_637076
  have hstable : (prefixWord ++ tailWord_637076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637076).length < 2 ^ (prefixWord ++ tailWord_637076).sum := by decide
  have hdescent : baseEnd_637076 < baseStart_637076 := by decide
  rcases family_descends (prefixWord ++ tailWord_637076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637106 : List Nat := [3, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2]
def baseStart_637106 : Nat := 118140960795 + 637106 * 2 ^ 59
def prefixEnd_637106 : Nat := 4983230072969 + 3 ^ 40 * 637106 * 2
def baseEnd_637106 : Nat := 327141605863489553545009

theorem tailTrace_637106 : CollatzResearch.WordTrace tailWord_637106 prefixEnd_637106 327141605863489553545009 := by
  unfold tailWord_637106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5809291207470311471794793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15491443219920830591452781 5809291207470311471794793)
  ·
    refine ⟨4356968405602733603846095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5809291207470311471794793 4356968405602733603846095)
    ·
      refine ⟨6535452608404100405769143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4356968405602733603846095 6535452608404100405769143)
      ·
        refine ⟨9803178912606150608653715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6535452608404100405769143 9803178912606150608653715)
        ·
          refine ⟨14704768368909225912980573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9803178912606150608653715 14704768368909225912980573)
          ·
            refine ⟨5514288138340959717367715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14704768368909225912980573 5514288138340959717367715)
            ·
              refine ⟨8271432207511439576051573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5514288138340959717367715 8271432207511439576051573)
              ·
                refine ⟨775446769454197460254835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8271432207511439576051573 775446769454197460254835)
                ·
                  refine ⟨1163170154181296190382253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 775446769454197460254835 1163170154181296190382253)
                  ·
                    refine ⟨436188807817986071393345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1163170154181296190382253 436188807817986071393345)
                    ·
                      refine ⟨327141605863489553545009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 436188807817986071393345 327141605863489553545009)
                      ·
                        rfl

theorem cell23_637106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_637106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637106 prefixEnd_637106 := by exact prefixLift 637106
  have htrace : WordTrace (prefixWord ++ tailWord_637106) baseStart_637106 baseEnd_637106 := by
    simpa [prefixWord, tailWord_637106, baseEnd_637106] using wordTrace_append hprefix tailTrace_637106
  have hstable : (prefixWord ++ tailWord_637106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637106).length < 2 ^ (prefixWord ++ tailWord_637106).sum := by decide
  have hdescent : baseEnd_637106 < baseStart_637106 := by decide
  rcases family_descends (prefixWord ++ tailWord_637106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637170 : List Nat := [3, 2, 1, 3, 2, 2, 2, 2, 2, 2, 2]
def baseStart_637170 : Nat := 118140960795 + 637170 * 2 ^ 59
def prefixEnd_637170 : Nat := 4983230072969 + 3 ^ 40 * 637170 * 2
def baseEnd_637170 : Nat := 327174468625377303144715

theorem tailTrace_637170 : CollatzResearch.WordTrace tailWord_637170 prefixEnd_637170 327174468625377303144715 := by
  unfold tailWord_637170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5809874775412346204377241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15492999401099589878339309 5809874775412346204377241)
  ·
    refine ⟨4357406081559259653282931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5809874775412346204377241 4357406081559259653282931)
    ·
      refine ⟨6536109122338889479924397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4357406081559259653282931 6536109122338889479924397)
      ·
        refine ⟨2451040920877083554971649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6536109122338889479924397 2451040920877083554971649)
        ·
          refine ⟨1838280690657812666228737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2451040920877083554971649 1838280690657812666228737)
          ·
            refine ⟨1378710517993359499671553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1838280690657812666228737 1378710517993359499671553)
            ·
              refine ⟨1034032888495019624753665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1378710517993359499671553 1034032888495019624753665)
              ·
                refine ⟨775524666371264718565249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1034032888495019624753665 775524666371264718565249)
                ·
                  refine ⟨581643499778448538923937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 775524666371264718565249 581643499778448538923937)
                  ·
                    refine ⟨436232624833836404192953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 581643499778448538923937 436232624833836404192953)
                    ·
                      refine ⟨327174468625377303144715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 436232624833836404192953 327174468625377303144715)
                      ·
                        rfl

theorem cell23_637170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_637170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637170 prefixEnd_637170 := by exact prefixLift 637170
  have htrace : WordTrace (prefixWord ++ tailWord_637170) baseStart_637170 baseEnd_637170 := by
    simpa [prefixWord, tailWord_637170, baseEnd_637170] using wordTrace_append hprefix tailTrace_637170
  have hstable : (prefixWord ++ tailWord_637170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637170).length < 2 ^ (prefixWord ++ tailWord_637170).sum := by decide
  have hdescent : baseEnd_637170 < baseStart_637170 := by decide
  rcases family_descends (prefixWord ++ tailWord_637170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637186 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_637186 : Nat := 118140960795 + 637186 * 2 ^ 59
def prefixEnd_637186 : Nat := 4983230072969 + 3 ^ 40 * 637186 * 2
def baseEnd_637186 : Nat := 327182684315849240544641

theorem tailTrace_637186 : CollatzResearch.WordTrace tailWord_637186 prefixEnd_637186 327182684315849240544641 := by
  unfold tailWord_637186
  simp only [CollatzResearch.WordTrace]
  refine ⟨5810020667397854887522853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15493388446394279700060941 5810020667397854887522853)
  ·
    refine ⟨1089378875137097791410535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5810020667397854887522853 1089378875137097791410535)
    ·
      refine ⟨1634068312705646687115803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1089378875137097791410535 1634068312705646687115803)
      ·
        refine ⟨2451102469058470030673705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1634068312705646687115803 2451102469058470030673705)
        ·
          refine ⟨1838326851793852523005279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2451102469058470030673705 1838326851793852523005279)
          ·
            refine ⟨2757490277690778784507919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838326851793852523005279 2757490277690778784507919)
            ·
              refine ⟨4136235416536168176761879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2757490277690778784507919 4136235416536168176761879)
              ·
                refine ⟨6204353124804252265142819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4136235416536168176761879 6204353124804252265142819)
                ·
                  refine ⟨9306529687206378397714229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6204353124804252265142819 9306529687206378397714229)
                  ·
                    refine ⟨872487158175597974785709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9306529687206378397714229 872487158175597974785709)
                    ·
                      refine ⟨327182684315849240544641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 872487158175597974785709 327182684315849240544641)
                      ·
                        rfl

theorem cell23_637186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_637186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637186 prefixEnd_637186 := by exact prefixLift 637186
  have htrace : WordTrace (prefixWord ++ tailWord_637186) baseStart_637186 baseEnd_637186 := by
    simpa [prefixWord, tailWord_637186, baseEnd_637186] using wordTrace_append hprefix tailTrace_637186
  have hstable : (prefixWord ++ tailWord_637186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637186).length < 2 ^ (prefixWord ++ tailWord_637186).sum := by decide
  have hdescent : baseEnd_637186 < baseStart_637186 := by decide
  rcases family_descends (prefixWord ++ tailWord_637186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637219 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 5, 4]
def baseStart_637219 : Nat := 118140960795 + 637219 * 2 ^ 59
def prefixEnd_637219 : Nat := 4983230072969 + 3 ^ 40 * 637219 * 2
def baseEnd_637219 : Nat := 109066543059149203810663

theorem tailTrace_637219 : CollatzResearch.WordTrace tailWord_637219 prefixEnd_637219 109066543059149203810663 := by
  unfold tailWord_637219
  simp only [CollatzResearch.WordTrace]
  refine ⟨23241286278471866186042711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15494190852314577457361807 23241286278471866186042711)
  ·
    refine ⟨34861929417707799279064067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23241286278471866186042711 34861929417707799279064067)
    ·
      refine ⟨52292894126561698918596101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34861929417707799279064067 52292894126561698918596101)
      ·
        refine ⟨9804917648730318547236769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52292894126561698918596101 9804917648730318547236769)
        ·
          refine ⟨7353688236547738910427577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9804917648730318547236769 7353688236547738910427577)
          ·
            refine ⟨5515266177410804182820683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7353688236547738910427577 5515266177410804182820683)
            ·
              refine ⟨8272899266116206274231025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5515266177410804182820683 8272899266116206274231025)
              ·
                refine ⟨6204674449587154705673269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8272899266116206274231025 6204674449587154705673269)
                ·
                  refine ⟨581688229648795753656869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6204674449587154705673269 581688229648795753656869)
                  ·
                    refine ⟨109066543059149203810663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 581688229648795753656869 109066543059149203810663)
                    ·
                      rfl

theorem cell23_637219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 5, 4].length) (baseStart_637219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637219 prefixEnd_637219 := by exact prefixLift 637219
  have htrace : WordTrace (prefixWord ++ tailWord_637219) baseStart_637219 baseEnd_637219 := by
    simpa [prefixWord, tailWord_637219, baseEnd_637219] using wordTrace_append hprefix tailTrace_637219
  have hstable : (prefixWord ++ tailWord_637219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637219).length < 2 ^ (prefixWord ++ tailWord_637219).sum := by decide
  have hdescent : baseEnd_637219 < baseStart_637219 := by decide
  rcases family_descends (prefixWord ++ tailWord_637219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637246 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_637246 : Nat := 118140960795 + 637246 * 2 ^ 59
def prefixEnd_637246 : Nat := 4983230072969 + 3 ^ 40 * 637246 * 2
def baseEnd_637246 : Nat := 327213493155119005794365

theorem tailTrace_637246 : CollatzResearch.WordTrace tailWord_637246 prefixEnd_637246 327213493155119005794365 := by
  unfold tailWord_637246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2905283881171756224659449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15494847366249366531517061 2905283881171756224659449)
  ·
    refine ⟨2178962910878817168494587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2905283881171756224659449 2178962910878817168494587)
    ·
      refine ⟨3268444366318225752741881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2178962910878817168494587 3268444366318225752741881)
      ·
        refine ⟨2451333274738669314556411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3268444366318225752741881 2451333274738669314556411)
        ·
          refine ⟨3676999912108003971834617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451333274738669314556411 3676999912108003971834617)
          ·
            refine ⟨2757749934081002978875963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3676999912108003971834617 2757749934081002978875963)
            ·
              refine ⟨4136624901121504468313945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2757749934081002978875963 4136624901121504468313945)
              ·
                refine ⟨3102468675841128351235459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4136624901121504468313945 3102468675841128351235459)
                ·
                  refine ⟨4653703013761692526853189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3102468675841128351235459 4653703013761692526853189)
                  ·
                    refine ⟨872569315080317348784973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4653703013761692526853189 872569315080317348784973)
                    ·
                      refine ⟨327213493155119005794365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 872569315080317348784973 327213493155119005794365)
                      ·
                        rfl

theorem cell23_637246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_637246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637246 prefixEnd_637246 := by exact prefixLift 637246
  have htrace : WordTrace (prefixWord ++ tailWord_637246) baseStart_637246 baseEnd_637246 := by
    simpa [prefixWord, tailWord_637246, baseEnd_637246] using wordTrace_append hprefix tailTrace_637246
  have hstable : (prefixWord ++ tailWord_637246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637246).length < 2 ^ (prefixWord ++ tailWord_637246).sum := by decide
  have hdescent : baseEnd_637246 < baseStart_637246 := by decide
  rcases family_descends (prefixWord ++ tailWord_637246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637299 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 4]
def baseStart_637299 : Nat := 118140960795 + 637299 * 2 ^ 59
def prefixEnd_637299 : Nat := 4983230072969 + 3 ^ 40 * 637299 * 2
def baseEnd_637299 : Nat := 327240707629807298431621

theorem tailTrace_637299 : CollatzResearch.WordTrace tailWord_637299 prefixEnd_637299 327240707629807298431621 := by
  unfold tailWord_637299
  simp only [CollatzResearch.WordTrace]
  refine ⟨23244204118182039848954951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15496136078788026565969967 23244204118182039848954951)
  ·
    refine ⟨34866306177273059773432427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23244204118182039848954951 34866306177273059773432427)
    ·
      refine ⟨52299459265909589660148641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34866306177273059773432427 52299459265909589660148641)
      ·
        refine ⟨39224594449432192245111481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52299459265909589660148641 39224594449432192245111481)
        ·
          refine ⟨29418445837074144183833611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39224594449432192245111481 29418445837074144183833611)
          ·
            refine ⟨44127668755611216275750417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29418445837074144183833611 44127668755611216275750417)
            ·
              refine ⟨33095751566708412206812813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44127668755611216275750417 33095751566708412206812813)
              ·
                refine ⟨12410906837515654577554805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33095751566708412206812813 12410906837515654577554805)
                ·
                  refine ⟨1163522516017092616645763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12410906837515654577554805 1163522516017092616645763)
                  ·
                    refine ⟨1745283774025638924968645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1163522516017092616645763 1745283774025638924968645)
                    ·
                      refine ⟨327240707629807298431621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1745283774025638924968645 327240707629807298431621)
                      ·
                        rfl

theorem cell23_637299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_637299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637299 prefixEnd_637299 := by exact prefixLift 637299
  have htrace : WordTrace (prefixWord ++ tailWord_637299) baseStart_637299 baseEnd_637299 := by
    simpa [prefixWord, tailWord_637299, baseEnd_637299] using wordTrace_append hprefix tailTrace_637299
  have hstable : (prefixWord ++ tailWord_637299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637299).length < 2 ^ (prefixWord ++ tailWord_637299).sum := by decide
  have hdescent : baseEnd_637299 < baseStart_637299 := by decide
  rcases family_descends (prefixWord ++ tailWord_637299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637313 : List Nat := [1, 2, 4, 3, 1, 1, 3, 2, 1, 5]
def baseStart_637313 : Nat := 118140960795 + 637313 * 2 ^ 59
def prefixEnd_637313 : Nat := 4983230072969 + 3 ^ 40 * 637313 * 2
def baseEnd_637313 : Nat := 109082632119656747885519

theorem tailTrace_637313 : CollatzResearch.WordTrace tailWord_637313 prefixEnd_637313 109082632119656747885519 := by
  unfold tailWord_637313
  simp only [CollatzResearch.WordTrace]
  refine ⟨23244714740131320239964593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15496476493420880159976395 23244714740131320239964593)
  ·
    refine ⟨17433536055098490179973445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23244714740131320239964593 17433536055098490179973445)
    ·
      refine ⟨3268788010330966908745021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17433536055098490179973445 3268788010330966908745021)
      ·
        refine ⟨1225795503874112590779383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3268788010330966908745021 1225795503874112590779383)
        ·
          refine ⟨1838693255811168886169075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225795503874112590779383 1838693255811168886169075)
          ·
            refine ⟨2758039883716753329253613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838693255811168886169075 2758039883716753329253613)
            ·
              refine ⟨1034264956393782498470105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2758039883716753329253613 1034264956393782498470105)
              ·
                refine ⟨775698717295336873852579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1034264956393782498470105 775698717295336873852579)
                ·
                  refine ⟨1163548075943005310778869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 775698717295336873852579 1163548075943005310778869)
                  ·
                    refine ⟨109082632119656747885519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1163548075943005310778869 109082632119656747885519)
                    ·
                      rfl

theorem cell23_637313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_637313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637313 prefixEnd_637313 := by exact prefixLift 637313
  have htrace : WordTrace (prefixWord ++ tailWord_637313) baseStart_637313 baseEnd_637313 := by
    simpa [prefixWord, tailWord_637313, baseEnd_637313] using wordTrace_append hprefix tailTrace_637313
  have hstable : (prefixWord ++ tailWord_637313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637313).length < 2 ^ (prefixWord ++ tailWord_637313).sum := by decide
  have hdescent : baseEnd_637313 < baseStart_637313 := by decide
  rcases family_descends (prefixWord ++ tailWord_637313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637316 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_637316 : Nat := 118140960795 + 637316 * 2 ^ 59
def prefixEnd_637316 : Nat := 4983230072969 + 3 ^ 40 * 637316 * 2
def baseEnd_637316 : Nat := 327249436800933731919043

theorem tailTrace_637316 : CollatzResearch.WordTrace tailWord_637316 prefixEnd_637316 327249436800933731919043 := by
  unfold tailWord_637316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11622412079560225876161901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15496549439413634501549201 11622412079560225876161901)
  ·
    refine ⟨4358404529835084703560713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11622412079560225876161901 4358404529835084703560713)
    ·
      refine ⟨3268803397376313527670535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4358404529835084703560713 3268803397376313527670535)
      ·
        refine ⟨4903205096064470291505803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3268803397376313527670535 4903205096064470291505803)
        ·
          refine ⟨7354807644096705437258705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4903205096064470291505803 7354807644096705437258705)
          ·
            refine ⟨5516105733072529077944029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7354807644096705437258705 5516105733072529077944029)
            ·
              refine ⟨2068539649902198404229011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5516105733072529077944029 2068539649902198404229011)
              ·
                refine ⟨3102809474853297606343517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068539649902198404229011 3102809474853297606343517)
                ·
                  refine ⟨1163553553069986602378819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3102809474853297606343517 1163553553069986602378819)
                  ·
                    refine ⟨1745330329604979903568229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1163553553069986602378819 1745330329604979903568229)
                    ·
                      refine ⟨327249436800933731919043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1745330329604979903568229 327249436800933731919043)
                      ·
                        rfl

theorem cell23_637316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_637316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637316 prefixEnd_637316 := by exact prefixLift 637316
  have htrace : WordTrace (prefixWord ++ tailWord_637316) baseStart_637316 baseEnd_637316 := by
    simpa [prefixWord, tailWord_637316, baseEnd_637316] using wordTrace_append hprefix tailTrace_637316
  have hstable : (prefixWord ++ tailWord_637316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637316).length < 2 ^ (prefixWord ++ tailWord_637316).sum := by decide
  have hdescent : baseEnd_637316 < baseStart_637316 := by decide
  rcases family_descends (prefixWord ++ tailWord_637316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637326 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_637326 : Nat := 118140960795 + 637326 * 2 ^ 59
def prefixEnd_637326 : Nat := 4983230072969 + 3 ^ 40 * 637326 * 2
def baseEnd_637326 : Nat := 109084857202492897597999

theorem tailTrace_637326 : CollatzResearch.WordTrace tailWord_637326 prefixEnd_637326 109084857202492897597999 := by
  unfold tailWord_637326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2905648611135527932523479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15496792592722815640125221 2905648611135527932523479)
  ·
    refine ⟨4358472916703291898785219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2905648611135527932523479 4358472916703291898785219)
    ·
      refine ⟨6537709375054937848177829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4358472916703291898785219 6537709375054937848177829)
      ·
        refine ⟨1225820507822800846533343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6537709375054937848177829 1225820507822800846533343)
        ·
          refine ⟨1838730761734201269800015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225820507822800846533343 1838730761734201269800015)
          ·
            refine ⟨2758096142601301904700023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838730761734201269800015 2758096142601301904700023)
            ·
              refine ⟨4137144213901952857050035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2758096142601301904700023 4137144213901952857050035)
              ·
                refine ⟨6205716320852929285575053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4137144213901952857050035 6205716320852929285575053)
                ·
                  refine ⟨2327143620319848482090645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6205716320852929285575053 2327143620319848482090645)
                  ·
                    refine ⟨109084857202492897597999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2327143620319848482090645 109084857202492897597999)
                    ·
                      rfl

theorem cell23_637326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_637326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637326 prefixEnd_637326 := by exact prefixLift 637326
  have htrace : WordTrace (prefixWord ++ tailWord_637326) baseStart_637326 baseEnd_637326 := by
    simpa [prefixWord, tailWord_637326, baseEnd_637326] using wordTrace_append hprefix tailTrace_637326
  have hstable : (prefixWord ++ tailWord_637326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637326).length < 2 ^ (prefixWord ++ tailWord_637326).sum := by decide
  have hdescent : baseEnd_637326 < baseStart_637326 := by decide
  rcases family_descends (prefixWord ++ tailWord_637326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637343 : List Nat := [1, 1, 2, 5, 1, 1, 4, 2, 2, 4]
def baseStart_637343 : Nat := 118140960795 + 637343 * 2 ^ 59
def prefixEnd_637343 : Nat := 4983230072969 + 3 ^ 40 * 637343 * 2
def baseEnd_637343 : Nat := 109087766926201708760473

theorem tailTrace_637343 : CollatzResearch.WordTrace tailWord_637343 prefixEnd_637343 109087766926201708760473 := by
  unfold tailWord_637343
  simp only [CollatzResearch.WordTrace]
  refine ⟨23245808930022635363556683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15497205953348423575704455 23245808930022635363556683)
  ·
    refine ⟨34868713395033953045335025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23245808930022635363556683 34868713395033953045335025)
    ·
      refine ⟨26151535046275464784001269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34868713395033953045335025 26151535046275464784001269)
      ·
        refine ⟨2451706410588324823500119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26151535046275464784001269 2451706410588324823500119)
        ·
          refine ⟨3677559615882487235250179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451706410588324823500119 3677559615882487235250179)
          ·
            refine ⟨5516339423823730852875269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677559615882487235250179 5516339423823730852875269)
            ·
              refine ⟨1034313641966949534914113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5516339423823730852875269 1034313641966949534914113)
              ·
                refine ⟨775735231475212151185585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1034313641966949534914113 775735231475212151185585)
                ·
                  refine ⟨581801423606409113389189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 775735231475212151185585 581801423606409113389189)
                  ·
                    refine ⟨109087766926201708760473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 581801423606409113389189 109087766926201708760473)
                    ·
                      rfl

theorem cell23_637343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 2, 4].length) (baseStart_637343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637343 prefixEnd_637343 := by exact prefixLift 637343
  have htrace : WordTrace (prefixWord ++ tailWord_637343) baseStart_637343 baseEnd_637343 := by
    simpa [prefixWord, tailWord_637343, baseEnd_637343] using wordTrace_append hprefix tailTrace_637343
  have hstable : (prefixWord ++ tailWord_637343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637343).length < 2 ^ (prefixWord ++ tailWord_637343).sum := by decide
  have hdescent : baseEnd_637343 < baseStart_637343 := by decide
  rcases family_descends (prefixWord ++ tailWord_637343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637346 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_637346 : Nat := 118140960795 + 637346 * 2 ^ 59
def prefixEnd_637346 : Nat := 4983230072969 + 3 ^ 40 * 637346 * 2
def baseEnd_637346 : Nat := 327264841220568614543905

theorem tailTrace_637346 : CollatzResearch.WordTrace tailWord_637346 prefixEnd_637346 327264841220568614543905 := by
  unfold tailWord_637346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5811479587252941718978973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15497278899341177917277261 5811479587252941718978973)
  ·
    refine ⟨2179304845219853144617115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5811479587252941718978973 2179304845219853144617115)
    ·
      refine ⟨3268957267829779716925673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2179304845219853144617115 3268957267829779716925673)
      ·
        refine ⟨2451717950872334787694255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3268957267829779716925673 2451717950872334787694255)
        ·
          refine ⟨3677576926308502181541383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2451717950872334787694255 3677576926308502181541383)
          ·
            refine ⟨5516365389462753272312075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3677576926308502181541383 5516365389462753272312075)
            ·
              refine ⟨8274548084194129908468113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5516365389462753272312075 8274548084194129908468113)
              ·
                refine ⟨6205911063145597431351085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8274548084194129908468113 6205911063145597431351085)
                ·
                  refine ⟨2327216648679599036756657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6205911063145597431351085 2327216648679599036756657)
                  ·
                    refine ⟨1745412486509699277567493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2327216648679599036756657 1745412486509699277567493)
                    ·
                      refine ⟨327264841220568614543905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1745412486509699277567493 327264841220568614543905)
                      ·
                        rfl

theorem cell23_637346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_637346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637346 prefixEnd_637346 := by exact prefixLift 637346
  have htrace : WordTrace (prefixWord ++ tailWord_637346) baseStart_637346 baseEnd_637346 := by
    simpa [prefixWord, tailWord_637346, baseEnd_637346] using wordTrace_append hprefix tailTrace_637346
  have hstable : (prefixWord ++ tailWord_637346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637346).length < 2 ^ (prefixWord ++ tailWord_637346).sum := by decide
  have hdescent : baseEnd_637346 < baseStart_637346 := by decide
  rcases family_descends (prefixWord ++ tailWord_637346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637379 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 5]
def baseStart_637379 : Nat := 118140960795 + 637379 * 2 ^ 59
def prefixEnd_637379 : Nat := 4983230072969 + 3 ^ 40 * 637379 * 2
def baseEnd_637379 : Nat := 327281786082166985431253

theorem tailTrace_637379 : CollatzResearch.WordTrace tailWord_637379 prefixEnd_637379 327281786082166985431253 := by
  unfold tailWord_637379
  simp only [CollatzResearch.WordTrace]
  refine ⟨23247121957892213511867191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15498081305261475674578127 23247121957892213511867191)
  ·
    refine ⟨34870682936838320267800787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23247121957892213511867191 34870682936838320267800787)
    ·
      refine ⟨52306024405257480401701181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34870682936838320267800787 52306024405257480401701181)
      ·
        refine ⟨19614759151971555150637943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52306024405257480401701181 19614759151971555150637943)
        ·
          refine ⟨29422138727957332725956915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19614759151971555150637943 29422138727957332725956915)
          ·
            refine ⟨44133208091935999088935373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29422138727957332725956915 44133208091935999088935373)
            ·
              refine ⟨16549953034475999658350765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44133208091935999088935373 16549953034475999658350765)
              ·
                refine ⟨6206232387928499871881537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16549953034475999658350765 6206232387928499871881537)
                ·
                  refine ⟨4654674290946374903911153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6206232387928499871881537 4654674290946374903911153)
                  ·
                    refine ⟨3491005718209781177933365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4654674290946374903911153 3491005718209781177933365)
                    ·
                      refine ⟨327281786082166985431253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3491005718209781177933365 327281786082166985431253)
                      ·
                        rfl

theorem cell23_637379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_637379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637379 prefixEnd_637379 := by exact prefixLift 637379
  have htrace : WordTrace (prefixWord ++ tailWord_637379) baseStart_637379 baseEnd_637379 := by
    simpa [prefixWord, tailWord_637379, baseEnd_637379] using wordTrace_append hprefix tailTrace_637379
  have hstable : (prefixWord ++ tailWord_637379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637379).length < 2 ^ (prefixWord ++ tailWord_637379).sum := by decide
  have hdescent : baseEnd_637379 < baseStart_637379 := by decide
  rcases family_descends (prefixWord ++ tailWord_637379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637394 : List Nat := [3, 2, 2, 4, 2, 1, 1, 2, 2, 4]
def baseStart_637394 : Nat := 118140960795 + 637394 * 2 ^ 59
def prefixEnd_637394 : Nat := 4983230072969 + 3 ^ 40 * 637394 * 2
def baseEnd_637394 : Nat := 109096496097328142247895

theorem tailTrace_637394 : CollatzResearch.WordTrace tailWord_637394 prefixEnd_637394 109096496097328142247895 := by
  unfold tailWord_637394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5811917263209467768415809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15498446035225247382442157 5811917263209467768415809)
  ·
    refine ⟨4358937947407100826311857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5811917263209467768415809 4358937947407100826311857)
    ·
      refine ⟨3269203460555325619733893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4358937947407100826311857 3269203460555325619733893)
      ·
        refine ⟨612975648854123553700105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3269203460555325619733893 612975648854123553700105)
        ·
          refine ⟨459731736640592665275079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612975648854123553700105 459731736640592665275079)
          ·
            refine ⟨689597604960888997912619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459731736640592665275079 689597604960888997912619)
            ·
              refine ⟨1034396407441333496868929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689597604960888997912619 1034396407441333496868929)
              ·
                refine ⟨775797305581000122651697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1034396407441333496868929 775797305581000122651697)
                ·
                  refine ⟨581847979185750091988773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 775797305581000122651697 581847979185750091988773)
                  ·
                    refine ⟨109096496097328142247895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 581847979185750091988773 109096496097328142247895)
                    ·
                      rfl

theorem cell23_637394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_637394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637394 prefixEnd_637394 := by exact prefixLift 637394
  have htrace : WordTrace (prefixWord ++ tailWord_637394) baseStart_637394 baseEnd_637394 := by
    simpa [prefixWord, tailWord_637394, baseEnd_637394] using wordTrace_append hprefix tailTrace_637394
  have hstable : (prefixWord ++ tailWord_637394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637394).length < 2 ^ (prefixWord ++ tailWord_637394).sum := by decide
  have hdescent : baseEnd_637394 < baseStart_637394 := by decide
  rcases family_descends (prefixWord ++ tailWord_637394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637416 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 2, 6]
def baseStart_637416 : Nat := 118140960795 + 637416 * 2 ^ 59
def prefixEnd_637416 : Nat := 4983230072969 + 3 ^ 40 * 637416 * 2
def baseEnd_637416 : Nat := 109100261622127780222861

theorem tailTrace_637416 : CollatzResearch.WordTrace tailWord_637416 prefixEnd_637416 109100261622127780222861 := by
  unfold tailWord_637416
  simp only [CollatzResearch.WordTrace]
  refine ⟨11624235729379084415482051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15498980972505445887309401 11624235729379084415482051)
  ·
    refine ⟨17436353594068626623223077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11624235729379084415482051 17436353594068626623223077)
    ·
      refine ⟨3269316298887867491854327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17436353594068626623223077 3269316298887867491854327)
      ·
        refine ⟨4903974448331801237781491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3269316298887867491854327 4903974448331801237781491)
        ·
          refine ⟨7355961672497701856672237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4903974448331801237781491 7355961672497701856672237)
          ·
            refine ⟨2758485627186638196252089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7355961672497701856672237 2758485627186638196252089)
            ·
              refine ⟨2068864220389978647189067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2758485627186638196252089 2068864220389978647189067)
              ·
                refine ⟨3103296330584967970783601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2068864220389978647189067 3103296330584967970783601)
                ·
                  refine ⟨2327472247938725978087701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3103296330584967970783601 2327472247938725978087701)
                  ·
                    refine ⟨109100261622127780222861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2327472247938725978087701 109100261622127780222861)
                    ·
                      rfl

theorem cell23_637416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_637416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637416 prefixEnd_637416 := by exact prefixLift 637416
  have htrace : WordTrace (prefixWord ++ tailWord_637416) baseStart_637416 baseEnd_637416 := by
    simpa [prefixWord, tailWord_637416, baseEnd_637416] using wordTrace_append hprefix tailTrace_637416
  have hstable : (prefixWord ++ tailWord_637416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637416).length < 2 ^ (prefixWord ++ tailWord_637416).sum := by decide
  have hdescent : baseEnd_637416 < baseStart_637416 := by decide
  rcases family_descends (prefixWord ++ tailWord_637416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637493 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 2, 5]
def baseStart_637493 : Nat := 118140960795 + 637493 * 2 ^ 59
def prefixEnd_637493 : Nat := 4983230072969 + 3 ^ 40 * 637493 * 2
def baseEnd_637493 : Nat := 109113440958926513135243

theorem tailTrace_637493 : CollatzResearch.WordTrace tailWord_637493 prefixEnd_637493 109113440958926513135243 := by
  unfold tailWord_637493
  simp only [CollatzResearch.WordTrace]
  refine ⟨23251279879479210981517133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15500853252986140654344755 23251279879479210981517133)
  ·
    refine ⟨8719229954804704118068925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23251279879479210981517133 8719229954804704118068925)
    ·
      refine ⟨3269711233051764044275847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8719229954804704118068925 3269711233051764044275847)
      ·
        refine ⟨4904566849577646066413771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3269711233051764044275847 4904566849577646066413771)
        ·
          refine ⟨7356850274366469099620657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4904566849577646066413771 7356850274366469099620657)
          ·
            refine ⟨5517637705774851824715493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7356850274366469099620657 5517637705774851824715493)
            ·
              refine ⟨1034557069832784717134155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5517637705774851824715493 1034557069832784717134155)
              ·
                refine ⟨1551835604749177075701233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034557069832784717134155 1551835604749177075701233)
                ·
                  refine ⟨1163876703561882806775925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1551835604749177075701233 1163876703561882806775925)
                  ·
                    refine ⟨109113440958926513135243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1163876703561882806775925 109113440958926513135243)
                    ·
                      rfl

theorem cell23_637493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_637493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637493 prefixEnd_637493 := by exact prefixLift 637493
  have htrace : WordTrace (prefixWord ++ tailWord_637493) baseStart_637493 baseEnd_637493 := by
    simpa [prefixWord, tailWord_637493, baseEnd_637493] using wordTrace_append hprefix tailTrace_637493
  have hstable : (prefixWord ++ tailWord_637493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637493).length < 2 ^ (prefixWord ++ tailWord_637493).sum := by decide
  have hdescent : baseEnd_637493 < baseStart_637493 := by decide
  rcases family_descends (prefixWord ++ tailWord_637493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637508 : List Nat := [2, 3, 5, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_637508 : Nat := 118140960795 + 637508 * 2 ^ 59
def prefixEnd_637508 : Nat := 4983230072969 + 3 ^ 40 * 637508 * 2
def baseEnd_637508 : Nat := 327348025086596980718161

theorem tailTrace_637508 : CollatzResearch.WordTrace tailWord_637508 prefixEnd_637508 327348025086596980718161 := by
  unfold tailWord_637508
  simp only [CollatzResearch.WordTrace]
  refine ⟨11625913487212434271656589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15501217982949912362208785 11625913487212434271656589)
  ·
    refine ⟨4359717557704662851871221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11625913487212434271656589 4359717557704662851871221)
    ·
      refine ⟨408723521034812142362927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4359717557704662851871221 408723521034812142362927)
      ·
        refine ⟨613085281552218213544391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408723521034812142362927 613085281552218213544391)
        ·
          refine ⟨919627922328327320316587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613085281552218213544391 919627922328327320316587)
          ·
            refine ⟨1379441883492490980474881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919627922328327320316587 1379441883492490980474881)
            ·
              refine ⟨1034581412619368235356161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1379441883492490980474881 1034581412619368235356161)
              ·
                refine ⟨775936059464526176517121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1034581412619368235356161 775936059464526176517121)
                ·
                  refine ⟨581952044598394632387841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 775936059464526176517121 581952044598394632387841)
                  ·
                    refine ⟨436464033448795974290881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 581952044598394632387841 436464033448795974290881)
                    ·
                      refine ⟨327348025086596980718161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 436464033448795974290881 327348025086596980718161)
                      ·
                        rfl

theorem cell23_637508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_637508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637508 prefixEnd_637508 := by exact prefixLift 637508
  have htrace : WordTrace (prefixWord ++ tailWord_637508) baseStart_637508 baseEnd_637508 := by
    simpa [prefixWord, tailWord_637508, baseEnd_637508] using wordTrace_append hprefix tailTrace_637508
  have hstable : (prefixWord ++ tailWord_637508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637508).length < 2 ^ (prefixWord ++ tailWord_637508).sum := by decide
  have hdescent : baseEnd_637508 < baseStart_637508 := by decide
  rcases family_descends (prefixWord ++ tailWord_637508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637516 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_637516 : Nat := 118140960795 + 637516 * 2 ^ 59
def prefixEnd_637516 : Nat := 4983230072969 + 3 ^ 40 * 637516 * 2
def baseEnd_637516 : Nat := 327352132931832949418123

theorem tailTrace_637516 : CollatzResearch.WordTrace tailWord_637516 prefixEnd_637516 327352132931832949418123 := by
  unfold tailWord_637516
  simp only [CollatzResearch.WordTrace]
  refine ⟨11626059379197942954802201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15501412505597257273069601 11626059379197942954802201)
  ·
    refine ⟨8719544534398457216101651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11626059379197942954802201 8719544534398457216101651)
    ·
      refine ⟨13079316801597685824152477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8719544534398457216101651 13079316801597685824152477)
      ·
        refine ⟨4904743800599132184057179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13079316801597685824152477 4904743800599132184057179)
        ·
          refine ⟨7357115700898698276085769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4904743800599132184057179 7357115700898698276085769)
          ·
            refine ⟨5517836775674023707064327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7357115700898698276085769 5517836775674023707064327)
            ·
              refine ⟨8276755163511035560596491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5517836775674023707064327 8276755163511035560596491)
              ·
                refine ⟨12415132745266553340894737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8276755163511035560596491 12415132745266553340894737)
                ·
                  refine ⟨9311349558949915005671053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12415132745266553340894737 9311349558949915005671053)
                  ·
                    refine ⟨3491756084606218127126645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9311349558949915005671053 3491756084606218127126645)
                    ·
                      refine ⟨327352132931832949418123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3491756084606218127126645 327352132931832949418123)
                      ·
                        rfl

theorem cell23_637516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_637516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637516 prefixEnd_637516 := by exact prefixLift 637516
  have htrace : WordTrace (prefixWord ++ tailWord_637516) baseStart_637516 baseEnd_637516 := by
    simpa [prefixWord, tailWord_637516, baseEnd_637516] using wordTrace_append hprefix tailTrace_637516
  have hstable : (prefixWord ++ tailWord_637516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637516).length < 2 ^ (prefixWord ++ tailWord_637516).sum := by decide
  have hdescent : baseEnd_637516 < baseStart_637516 := by decide
  rcases family_descends (prefixWord ++ tailWord_637516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637550 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_637550 : Nat := 118140960795 + 637550 * 2 ^ 59
def prefixEnd_637550 : Nat := 4983230072969 + 3 ^ 40 * 637550 * 2
def baseEnd_637550 : Nat := 327369591274085816392967

theorem tailTrace_637550 : CollatzResearch.WordTrace tailWord_637550 prefixEnd_637550 327369591274085816392967 := by
  unfold tailWord_637550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2906669855034088714542763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15502239226848473144228069 2906669855034088714542763)
  ·
    refine ⟨4360004782551133071814145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2906669855034088714542763 4360004782551133071814145)
    ·
      refine ⟨3270003586913349803860609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4360004782551133071814145 3270003586913349803860609)
      ·
        refine ⟨2452502690185012352895457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3270003586913349803860609 2452502690185012352895457)
        ·
          refine ⟨1839377017638759264671593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2452502690185012352895457 1839377017638759264671593)
          ·
            refine ⟨1379532763229069448503695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1839377017638759264671593 1379532763229069448503695)
            ·
              refine ⟨2069299144843604172755543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1379532763229069448503695 2069299144843604172755543)
              ·
                refine ⟨3103948717265406259133315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2069299144843604172755543 3103948717265406259133315)
                ·
                  refine ⟨4655923075898109388699973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3103948717265406259133315 4655923075898109388699973)
                  ·
                    refine ⟨872985576730895510381245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4655923075898109388699973 872985576730895510381245)
                    ·
                      refine ⟨327369591274085816392967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 872985576730895510381245 327369591274085816392967)
                      ·
                        rfl

theorem cell23_637550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_637550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637550 prefixEnd_637550 := by exact prefixLift 637550
  have htrace : WordTrace (prefixWord ++ tailWord_637550) baseStart_637550 baseEnd_637550 := by
    simpa [prefixWord, tailWord_637550, baseEnd_637550] using wordTrace_append hprefix tailTrace_637550
  have hstable : (prefixWord ++ tailWord_637550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637550).length < 2 ^ (prefixWord ++ tailWord_637550).sum := by decide
  have hdescent : baseEnd_637550 < baseStart_637550 := by decide
  rcases family_descends (prefixWord ++ tailWord_637550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637630 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_637630 : Nat := 118140960795 + 637630 * 2 ^ 59
def prefixEnd_637630 : Nat := 4983230072969 + 3 ^ 40 * 637630 * 2
def baseEnd_637630 : Nat := 109136889908815167797533

theorem tailTrace_637630 : CollatzResearch.WordTrace tailWord_637630 prefixEnd_637630 109136889908815167797533 := by
  unfold tailWord_637630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2907034584997860422406793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15504184453321922252836229 2907034584997860422406793)
  ·
    refine ⟨2180275938748395316805095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2907034584997860422406793 2180275938748395316805095)
    ·
      refine ⟨3270413908122592975207643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2180275938748395316805095 3270413908122592975207643)
      ·
        refine ⟨4905620862183889462811465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270413908122592975207643 4905620862183889462811465)
        ·
          refine ⟨3679215646637917097108599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4905620862183889462811465 3679215646637917097108599)
          ·
            refine ⟨5518823469956875645662899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3679215646637917097108599 5518823469956875645662899)
            ·
              refine ⟨8278235204935313468494349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5518823469956875645662899 8278235204935313468494349)
              ·
                refine ⟨3104338201850742550685381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8278235204935313468494349 3104338201850742550685381)
                ·
                  refine ⟨582063412847014228253509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3104338201850742550685381 582063412847014228253509)
                  ·
                    refine ⟨109136889908815167797533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 582063412847014228253509 109136889908815167797533)
                    ·
                      rfl

theorem cell23_637630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_637630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637630 prefixEnd_637630 := by exact prefixLift 637630
  have htrace : WordTrace (prefixWord ++ tailWord_637630) baseStart_637630 baseEnd_637630 := by
    simpa [prefixWord, tailWord_637630, baseEnd_637630] using wordTrace_append hprefix tailTrace_637630
  have hstable : (prefixWord ++ tailWord_637630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637630).length < 2 ^ (prefixWord ++ tailWord_637630).sum := by decide
  have hdescent : baseEnd_637630 < baseStart_637630 := by decide
  rcases family_descends (prefixWord ++ tailWord_637630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637638 : List Nat := [6, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_637638 : Nat := 118140960795 + 637638 * 2 ^ 59
def prefixEnd_637638 : Nat := 4983230072969 + 3 ^ 40 * 637638 * 2
def baseEnd_637638 : Nat := 36379419730186830232507

theorem tailTrace_637638 : CollatzResearch.WordTrace tailWord_637638 prefixEnd_637638 36379419730186830232507 := by
  unfold tailWord_637638
  simp only [CollatzResearch.WordTrace]
  refine ⟨726767764498559398298299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15504378975969267163697045 726767764498559398298299)
  ·
    refine ⟨1090151646747839097447449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 726767764498559398298299 1090151646747839097447449)
    ·
      refine ⟨817613735060879323085587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1090151646747839097447449 817613735060879323085587)
      ·
        refine ⟨1226420602591318984628381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 817613735060879323085587 1226420602591318984628381)
        ·
          refine ⟨459907725971744619235643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1226420602591318984628381 459907725971744619235643)
          ·
            refine ⟨689861588957616928853465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459907725971744619235643 689861588957616928853465)
            ·
              refine ⟨517396191718212696640099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 689861588957616928853465 517396191718212696640099)
              ·
                refine ⟨776094287577319044960149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517396191718212696640099 776094287577319044960149)
                ·
                  refine ⟨36379419730186830232507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 776094287577319044960149 36379419730186830232507)
                  ·
                    rfl

theorem cell23_637638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_637638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637638 prefixEnd_637638 := by exact prefixLift 637638
  have htrace : WordTrace (prefixWord ++ tailWord_637638) baseStart_637638 baseEnd_637638 := by
    simpa [prefixWord, tailWord_637638, baseEnd_637638] using wordTrace_append hprefix tailTrace_637638
  have hstable : (prefixWord ++ tailWord_637638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637638).length < 2 ^ (prefixWord ++ tailWord_637638).sum := by decide
  have hdescent : baseEnd_637638 < baseStart_637638 := by decide
  rcases family_descends (prefixWord ++ tailWord_637638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637660 : List Nat := [2, 2, 5, 1, 1, 1, 2, 9]
def baseStart_637660 : Nat := 118140960795 + 637660 * 2 ^ 59
def prefixEnd_637660 : Nat := 4983230072969 + 3 ^ 40 * 637660 * 2
def baseEnd_637660 : Nat := 12126891635040014296943

theorem tailTrace_637660 : CollatzResearch.WordTrace tailWord_637660 prefixEnd_637660 12126891635040014296943 := by
  unfold tailWord_637660
  simp only [CollatzResearch.WordTrace]
  refine ⟨11628685434937099251423217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15504913913249465668564289 11628685434937099251423217)
  ·
    refine ⟨8721514076202824438567413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11628685434937099251423217 8721514076202824438567413)
    ·
      refine ⟨817641944644014791115695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8721514076202824438567413 817641944644014791115695)
      ·
        refine ⟨1226462916966022186673543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 817641944644014791115695 1226462916966022186673543)
        ·
          refine ⟨1839694375449033280010315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1226462916966022186673543 1839694375449033280010315)
          ·
            refine ⟨2759541563173549920015473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1839694375449033280010315 2759541563173549920015473)
            ·
              refine ⟨2069656172380162440011605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2759541563173549920015473 2069656172380162440011605)
              ·
                refine ⟨12126891635040014296943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2069656172380162440011605 12126891635040014296943)
                ·
                  rfl

theorem cell23_637660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 9].length) (baseStart_637660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637660 prefixEnd_637660 := by exact prefixLift 637660
  have htrace : WordTrace (prefixWord ++ tailWord_637660) baseStart_637660 baseEnd_637660 := by
    simpa [prefixWord, tailWord_637660, baseEnd_637660] using wordTrace_append hprefix tailTrace_637660
  have hstable : (prefixWord ++ tailWord_637660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637660).length < 2 ^ (prefixWord ++ tailWord_637660).sum := by decide
  have hdescent : baseEnd_637660 < baseStart_637660 := by decide
  rcases family_descends (prefixWord ++ tailWord_637660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637693 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_637693 : Nat := 118140960795 + 637693 * 2 ^ 59
def prefixEnd_637693 : Nat := 4983230072969 + 3 ^ 40 * 637693 * 2
def baseEnd_637693 : Nat := 327443019007678756904809

theorem tailTrace_637693 : CollatzResearch.WordTrace tailWord_637693 prefixEnd_637693 327443019007678756904809 := by
  unfold tailWord_637693
  simp only [CollatzResearch.WordTrace]
  refine ⟨23258574478754645138797733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15505716319169763425865155 23258574478754645138797733)
  ·
    refine ⟨4360982714766495963524575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23258574478754645138797733 4360982714766495963524575)
    ·
      refine ⟨6541474072149743945286863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4360982714766495963524575 6541474072149743945286863)
      ·
        refine ⟨9812211108224615917930295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6541474072149743945286863 9812211108224615917930295)
        ·
          refine ⟨14718316662336923876895443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9812211108224615917930295 14718316662336923876895443)
          ·
            refine ⟨22077474993505385815343165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14718316662336923876895443 22077474993505385815343165)
            ·
              refine ⟨8279053122564519680753687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22077474993505385815343165 8279053122564519680753687)
              ·
                refine ⟨12418579683846779521130531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8279053122564519680753687 12418579683846779521130531)
                ·
                  refine ⟨18627869525770169281695797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12418579683846779521130531 18627869525770169281695797)
                  ·
                    refine ⟨1746362768040953370158981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18627869525770169281695797 1746362768040953370158981)
                    ·
                      refine ⟨327443019007678756904809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1746362768040953370158981 327443019007678756904809)
                      ·
                        rfl

theorem cell23_637693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_637693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637693 prefixEnd_637693 := by exact prefixLift 637693
  have htrace : WordTrace (prefixWord ++ tailWord_637693) baseStart_637693 baseEnd_637693 := by
    simpa [prefixWord, tailWord_637693, baseEnd_637693] using wordTrace_append hprefix tailTrace_637693
  have hstable : (prefixWord ++ tailWord_637693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637693).length < 2 ^ (prefixWord ++ tailWord_637693).sum := by decide
  have hdescent : baseEnd_637693 < baseStart_637693 := by decide
  rcases family_descends (prefixWord ++ tailWord_637693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637713 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_637713 : Nat := 118140960795 + 637713 * 2 ^ 59
def prefixEnd_637713 : Nat := 4983230072969 + 3 ^ 40 * 637713 * 2
def baseEnd_637713 : Nat := 327453288620768678654717

theorem tailTrace_637713 : CollatzResearch.WordTrace tailWord_637713 prefixEnd_637713 327453288620768678654717 := by
  unfold tailWord_637713
  simp only [CollatzResearch.WordTrace]
  refine ⟨23259303938682188554525793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15506202625788125703017195 23259303938682188554525793)
  ·
    refine ⟨17444477954011641415894345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23259303938682188554525793 17444477954011641415894345)
    ·
      refine ⟨13083358465508731061920759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17444477954011641415894345 13083358465508731061920759)
      ·
        refine ⟨19625037698263096592881139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13083358465508731061920759 19625037698263096592881139)
        ·
          refine ⟨29437556547394644889321709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19625037698263096592881139 29437556547394644889321709)
          ·
            refine ⟨11039083705272991833495641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29437556547394644889321709 11039083705272991833495641)
            ·
              refine ⟨8279312778954743875121731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11039083705272991833495641 8279312778954743875121731)
              ·
                refine ⟨12418969168432115812682597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8279312778954743875121731 12418969168432115812682597)
                ·
                  refine ⟨2328556719081021714877987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12418969168432115812682597 2328556719081021714877987)
                  ·
                    refine ⟨3492835078621532572316981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2328556719081021714877987 3492835078621532572316981)
                    ·
                      refine ⟨327453288620768678654717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3492835078621532572316981 327453288620768678654717)
                      ·
                        rfl

theorem cell23_637713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_637713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637713 prefixEnd_637713 := by exact prefixLift 637713
  have htrace : WordTrace (prefixWord ++ tailWord_637713) baseStart_637713 baseEnd_637713 := by
    simpa [prefixWord, tailWord_637713, baseEnd_637713] using wordTrace_append hprefix tailTrace_637713
  have hstable : (prefixWord ++ tailWord_637713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637713).length < 2 ^ (prefixWord ++ tailWord_637713).sum := by decide
  have hdescent : baseEnd_637713 < baseStart_637713 := by decide
  rcases family_descends (prefixWord ++ tailWord_637713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637723 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 4]
def baseStart_637723 : Nat := 118140960795 + 637723 * 2 ^ 59
def prefixEnd_637723 : Nat := 4983230072969 + 3 ^ 40 * 637723 * 2
def baseEnd_637723 : Nat := 327458423427313639529671

theorem tailTrace_637723 : CollatzResearch.WordTrace tailWord_637723 prefixEnd_637723 327458423427313639529671 := by
  unfold tailWord_637723
  simp only [CollatzResearch.WordTrace]
  refine ⟨23259668668645960262389823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15506445779097306841593215 23259668668645960262389823)
  ·
    refine ⟨34889503002968940393584735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23259668668645960262389823 34889503002968940393584735)
    ·
      refine ⟨52334254504453410590377103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34889503002968940393584735 52334254504453410590377103)
      ·
        refine ⟨78501381756680115885565655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52334254504453410590377103 78501381756680115885565655)
        ·
          refine ⟨117752072635020173828348483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78501381756680115885565655 117752072635020173828348483)
          ·
            refine ⟨176628108952530260742522725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117752072635020173828348483 176628108952530260742522725)
            ·
              refine ⟨33117770428599423889223011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176628108952530260742522725 33117770428599423889223011)
              ·
                refine ⟨49676655642899135833834517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33117770428599423889223011 49676655642899135833834517)
                ·
                  refine ⟨2328593233260896992210993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49676655642899135833834517 2328593233260896992210993)
                  ·
                    refine ⟨1746444924945672744158245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2328593233260896992210993 1746444924945672744158245)
                    ·
                      refine ⟨327458423427313639529671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1746444924945672744158245 327458423427313639529671)
                      ·
                        rfl

theorem cell23_637723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 4].length) (baseStart_637723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637723 prefixEnd_637723 := by exact prefixLift 637723
  have htrace : WordTrace (prefixWord ++ tailWord_637723) baseStart_637723 baseEnd_637723 := by
    simpa [prefixWord, tailWord_637723, baseEnd_637723] using wordTrace_append hprefix tailTrace_637723
  have hstable : (prefixWord ++ tailWord_637723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637723).length < 2 ^ (prefixWord ++ tailWord_637723).sum := by decide
  have hdescent : baseEnd_637723 < baseStart_637723 := by decide
  rcases family_descends (prefixWord ++ tailWord_637723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637727 : List Nat := [1, 1, 2, 4, 2, 2, 2, 2, 1, 4, 2]
def baseStart_637727 : Nat := 118140960795 + 637727 * 2 ^ 59
def prefixEnd_637727 : Nat := 4983230072969 + 3 ^ 40 * 637727 * 2
def baseEnd_637727 : Nat := 327460477349931623879653

theorem tailTrace_637727 : CollatzResearch.WordTrace tailWord_637727 prefixEnd_637727 327460477349931623879653 := by
  unfold tailWord_637727
  simp only [CollatzResearch.WordTrace]
  refine ⟨23259814560631468945535435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15506543040420979297023623 23259814560631468945535435)
  ·
    refine ⟨34889721840947203418303153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23259814560631468945535435 34889721840947203418303153)
    ·
      refine ⟨26167291380710402563727365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34889721840947203418303153 26167291380710402563727365)
      ·
        refine ⟨4906367133883200480698881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26167291380710402563727365 4906367133883200480698881)
        ·
          refine ⟨3679775350412400360524161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4906367133883200480698881 3679775350412400360524161)
          ·
            refine ⟨2759831512809300270393121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3679775350412400360524161 2759831512809300270393121)
            ·
              refine ⟨2069873634606975202794841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2759831512809300270393121 2069873634606975202794841)
              ·
                refine ⟨1552405225955231402096131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2069873634606975202794841 1552405225955231402096131)
                ·
                  refine ⟨2328607838932847103144197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1552405225955231402096131 2328607838932847103144197)
                  ·
                    refine ⟨436613969799908831839537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2328607838932847103144197 436613969799908831839537)
                    ·
                      refine ⟨327460477349931623879653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 436613969799908831839537 327460477349931623879653)
                      ·
                        rfl

theorem cell23_637727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_637727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637727 prefixEnd_637727 := by exact prefixLift 637727
  have htrace : WordTrace (prefixWord ++ tailWord_637727) baseStart_637727 baseEnd_637727 := by
    simpa [prefixWord, tailWord_637727, baseEnd_637727] using wordTrace_append hprefix tailTrace_637727
  have hstable : (prefixWord ++ tailWord_637727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637727).length < 2 ^ (prefixWord ++ tailWord_637727).sum := by decide
  have hdescent : baseEnd_637727 < baseStart_637727 := by decide
  rcases family_descends (prefixWord ++ tailWord_637727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637733 : List Nat := [1, 3, 1, 2, 3, 1, 1, 2, 9]
def baseStart_637733 : Nat := 118140960795 + 637733 * 2 ^ 59
def prefixEnd_637733 : Nat := 4983230072969 + 3 ^ 40 * 637733 * 2
def baseEnd_637733 : Nat := 36384839803762066711625

theorem tailTrace_637733 : CollatzResearch.WordTrace tailWord_637733 prefixEnd_637733 36384839803762066711625 := by
  unfold tailWord_637733
  simp only [CollatzResearch.WordTrace]
  refine ⟨23260033398609731970253853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15506688932406487980169235 23260033398609731970253853)
  ·
    refine ⟨8722512524478649488845195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23260033398609731970253853 8722512524478649488845195)
    ·
      refine ⟨13083768786717974233267793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8722512524478649488845195 13083768786717974233267793)
      ·
        refine ⟨9812826590038480674950845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13083768786717974233267793 9812826590038480674950845)
        ·
          refine ⟨3679809971264430253106567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9812826590038480674950845 3679809971264430253106567)
          ·
            refine ⟨5519714956896645379659851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3679809971264430253106567 5519714956896645379659851)
            ·
              refine ⟨8279572435344968069489777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5519714956896645379659851 8279572435344968069489777)
              ·
                refine ⟨6209679326508726052117333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8279572435344968069489777 6209679326508726052117333)
                ·
                  refine ⟨36384839803762066711625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6209679326508726052117333 36384839803762066711625)
                  ·
                    rfl

theorem cell23_637733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_637733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637733 prefixEnd_637733 := by exact prefixLift 637733
  have htrace : WordTrace (prefixWord ++ tailWord_637733) baseStart_637733 baseEnd_637733 := by
    simpa [prefixWord, tailWord_637733, baseEnd_637733] using wordTrace_append hprefix tailTrace_637733
  have hstable : (prefixWord ++ tailWord_637733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637733).length < 2 ^ (prefixWord ++ tailWord_637733).sum := by decide
  have hdescent : baseEnd_637733 < baseStart_637733 := by decide
  rcases family_descends (prefixWord ++ tailWord_637733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637738 : List Nat := [3, 1, 4, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_637738 : Nat := 118140960795 + 637738 * 2 ^ 59
def prefixEnd_637738 : Nat := 4983230072969 + 3 ^ 40 * 637738 * 2
def baseEnd_637738 : Nat := 327466125637131080842103

theorem tailTrace_637738 : CollatzResearch.WordTrace tailWord_637738 prefixEnd_637738 327466125637131080842103 := by
  unfold tailWord_637738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5815053940897904456046467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15506810509061078549457245 5815053940897904456046467)
  ·
    refine ⟨8722580911346856684069701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5815053940897904456046467 8722580911346856684069701)
    ·
      refine ⟨1635483920877535628263069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8722580911346856684069701 1635483920877535628263069)
      ·
        refine ⟨613306470329075860598651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1635483920877535628263069 613306470329075860598651)
        ·
          refine ⟨919959705493613790897977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613306470329075860598651 919959705493613790897977)
          ·
            refine ⟨689969779120210343173483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 919959705493613790897977 689969779120210343173483)
            ·
              refine ⟨1034954668680315514760225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689969779120210343173483 1034954668680315514760225)
              ·
                refine ⟨776216001510236636070169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1034954668680315514760225 776216001510236636070169)
                ·
                  refine ⟨582162001132677477052627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 776216001510236636070169 582162001132677477052627)
                  ·
                    refine ⟨873243001699016215578941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 582162001132677477052627 873243001699016215578941)
                    ·
                      refine ⟨327466125637131080842103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 873243001699016215578941 327466125637131080842103)
                      ·
                        rfl

theorem cell23_637738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_637738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637738 prefixEnd_637738 := by exact prefixLift 637738
  have htrace : WordTrace (prefixWord ++ tailWord_637738) baseStart_637738 baseEnd_637738 := by
    simpa [prefixWord, tailWord_637738, baseEnd_637738] using wordTrace_append hprefix tailTrace_637738
  have hstable : (prefixWord ++ tailWord_637738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637738).length < 2 ^ (prefixWord ++ tailWord_637738).sum := by decide
  have hdescent : baseEnd_637738 < baseStart_637738 := by decide
  rcases family_descends (prefixWord ++ tailWord_637738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637763 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 3, 7]
def baseStart_637763 : Nat := 118140960795 + 637763 * 2 ^ 59
def prefixEnd_637763 : Nat := 4983230072969 + 3 ^ 40 * 637763 * 2
def baseEnd_637763 : Nat := 109159654217831161009829

theorem tailTrace_637763 : CollatzResearch.WordTrace tailWord_637763 prefixEnd_637763 109159654217831161009829 := by
  unfold tailWord_637763
  simp only [CollatzResearch.WordTrace]
  refine ⟨23261127588501047093845943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15507418392334031395897295 23261127588501047093845943)
  ·
    refine ⟨34891691382751570640768915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23261127588501047093845943 34891691382751570640768915)
    ·
      refine ⟨52337537074127355961153373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34891691382751570640768915 52337537074127355961153373)
      ·
        refine ⟨19626576402797758485432515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52337537074127355961153373 19626576402797758485432515)
        ·
          refine ⟨29439864604196637728148773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19626576402797758485432515 29439864604196637728148773)
          ·
            refine ⟨5519974613286869574027895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29439864604196637728148773 5519974613286869574027895)
            ·
              refine ⟨8279961919930304361041843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5519974613286869574027895 8279961919930304361041843)
              ·
                refine ⟨12419942879895456541562765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8279961919930304361041843 12419942879895456541562765)
                ·
                  refine ⟨4657478579960796203086037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12419942879895456541562765 4657478579960796203086037)
                  ·
                    refine ⟨109159654217831161009829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4657478579960796203086037 109159654217831161009829)
                    ·
                      rfl

theorem cell23_637763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 7].length) (baseStart_637763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637763 prefixEnd_637763 := by exact prefixLift 637763
  have htrace : WordTrace (prefixWord ++ tailWord_637763) baseStart_637763 baseEnd_637763 := by
    simpa [prefixWord, tailWord_637763, baseEnd_637763] using wordTrace_append hprefix tailTrace_637763
  have hstable : (prefixWord ++ tailWord_637763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637763).length < 2 ^ (prefixWord ++ tailWord_637763).sum := by decide
  have hdescent : baseEnd_637763 < baseStart_637763 := by decide
  rcases family_descends (prefixWord ++ tailWord_637763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637820 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_637820 : Nat := 118140960795 + 637820 * 2 ^ 59
def prefixEnd_637820 : Nat := 4983230072969 + 3 ^ 40 * 637820 * 2
def baseEnd_637820 : Nat := 327508231050799760016725

theorem tailTrace_637820 : CollatzResearch.WordTrace tailWord_637820 prefixEnd_637820 327508231050799760016725 := by
  unfold tailWord_637820
  simp only [CollatzResearch.WordTrace]
  refine ⟨11631603274647272914335457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15508804366196363885780609 11631603274647272914335457)
  ·
    refine ⟨8723702455985454685751593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11631603274647272914335457 8723702455985454685751593)
    ·
      refine ⟨6542776841989091014313695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8723702455985454685751593 6542776841989091014313695)
      ·
        refine ⟨9814165262983636521470543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6542776841989091014313695 9814165262983636521470543)
        ·
          refine ⟨14721247894475454782205815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9814165262983636521470543 14721247894475454782205815)
          ·
            refine ⟨22081871841713182173308723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14721247894475454782205815 22081871841713182173308723)
            ·
              refine ⟨33122807762569773259963085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22081871841713182173308723 33122807762569773259963085)
              ·
                refine ⟨12421052910963664972486157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33122807762569773259963085 12421052910963664972486157)
                ·
                  refine ⟨4657894841611374364682309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12421052910963664972486157 4657894841611374364682309)
                  ·
                    refine ⟨873355282802132693377933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4657894841611374364682309 873355282802132693377933)
                    ·
                      refine ⟨327508231050799760016725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 873355282802132693377933 327508231050799760016725)
                      ·
                        rfl

theorem cell23_637820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_637820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637820 prefixEnd_637820 := by exact prefixLift 637820
  have htrace : WordTrace (prefixWord ++ tailWord_637820) baseStart_637820 baseEnd_637820 := by
    simpa [prefixWord, tailWord_637820, baseEnd_637820] using wordTrace_append hprefix tailTrace_637820
  have hstable : (prefixWord ++ tailWord_637820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637820).length < 2 ^ (prefixWord ++ tailWord_637820).sum := by decide
  have hdescent : baseEnd_637820 < baseStart_637820 := by decide
  rcases family_descends (prefixWord ++ tailWord_637820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637834 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_637834 : Nat := 118140960795 + 637834 * 2 ^ 59
def prefixEnd_637834 : Nat := 4983230072969 + 3 ^ 40 * 637834 * 2
def baseEnd_637834 : Nat := 327515419779962705241661

theorem tailTrace_637834 : CollatzResearch.WordTrace tailWord_637834 prefixEnd_637834 327515419779962705241661 := by
  unfold tailWord_637834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5815929292810956554920139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15509144780829217479787037 5815929292810956554920139)
  ·
    refine ⟨8723893939216434832380209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5815929292810956554920139 8723893939216434832380209)
    ·
      refine ⟨6542920454412326124285157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8723893939216434832380209 6542920454412326124285157)
      ·
        refine ⟨1226797585202311148303467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6542920454412326124285157 1226797585202311148303467)
        ·
          refine ⟨1840196377803466722455201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1226797585202311148303467 1840196377803466722455201)
          ·
            refine ⟨1380147283352600041841401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1840196377803466722455201 1380147283352600041841401)
            ·
              refine ⟨1035110462514450031381051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1380147283352600041841401 1035110462514450031381051)
              ·
                refine ⟨1552665693771675047071577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1035110462514450031381051 1552665693771675047071577)
                ·
                  refine ⟨1164499270328756285303683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1552665693771675047071577 1164499270328756285303683)
                  ·
                    refine ⟨1746748905493134427955525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1164499270328756285303683 1746748905493134427955525)
                    ·
                      refine ⟨327515419779962705241661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1746748905493134427955525 327515419779962705241661)
                      ·
                        rfl

theorem cell23_637834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_637834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637834 prefixEnd_637834 := by exact prefixLift 637834
  have htrace : WordTrace (prefixWord ++ tailWord_637834) baseStart_637834 baseEnd_637834 := by
    simpa [prefixWord, tailWord_637834, baseEnd_637834] using wordTrace_append hprefix tailTrace_637834
  have hstable : (prefixWord ++ tailWord_637834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637834).length < 2 ^ (prefixWord ++ tailWord_637834).sum := by decide
  have hdescent : baseEnd_637834 < baseStart_637834 := by decide
  rcases family_descends (prefixWord ++ tailWord_637834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637857 : List Nat := [1, 2, 3, 4, 1, 1, 1, 4, 6]
def baseStart_637857 : Nat := 118140960795 + 637857 * 2 ^ 59
def prefixEnd_637857 : Nat := 4983230072969 + 3 ^ 40 * 637857 * 2
def baseEnd_637857 : Nat := 36391914426112901694895

theorem tailTrace_637857 : CollatzResearch.WordTrace tailWord_637857 prefixEnd_637857 36391914426112901694895 := by
  unfold tailWord_637857
  simp only [CollatzResearch.WordTrace]
  refine ⟨23264556050160501147767825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15509704033440334098511883 23264556050160501147767825)
  ·
    refine ⟨17448417037620375860825869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23264556050160501147767825 17448417037620375860825869)
    ·
      refine ⟨6543156389107640947809701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17448417037620375860825869 6543156389107640947809701)
      ·
        refine ⟨1226841822957682677714319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6543156389107640947809701 1226841822957682677714319)
        ·
          refine ⟨1840262734436524016571479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1226841822957682677714319 1840262734436524016571479)
          ·
            refine ⟨2760394101654786024857219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840262734436524016571479 2760394101654786024857219)
            ·
              refine ⟨4140591152482179037285829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2760394101654786024857219 4140591152482179037285829)
              ·
                refine ⟨776360841090408569491093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4140591152482179037285829 776360841090408569491093)
                ·
                  refine ⟨36391914426112901694895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 776360841090408569491093 36391914426112901694895)
                  ·
                    rfl

theorem cell23_637857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4, 6].length) (baseStart_637857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637857 prefixEnd_637857 := by exact prefixLift 637857
  have htrace : WordTrace (prefixWord ++ tailWord_637857) baseStart_637857 baseEnd_637857 := by
    simpa [prefixWord, tailWord_637857, baseEnd_637857] using wordTrace_append hprefix tailTrace_637857
  have hstable : (prefixWord ++ tailWord_637857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637857).length < 2 ^ (prefixWord ++ tailWord_637857).sum := by decide
  have hdescent : baseEnd_637857 < baseStart_637857 := by decide
  rcases family_descends (prefixWord ++ tailWord_637857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637860 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_637860 : Nat := 118140960795 + 637860 * 2 ^ 59
def prefixEnd_637860 : Nat := 4983230072969 + 3 ^ 40 * 637860 * 2
def baseEnd_637860 : Nat := 327528770276979603516541

theorem tailTrace_637860 : CollatzResearch.WordTrace tailWord_637860 prefixEnd_637860 327528770276979603516541 := by
  unfold tailWord_637860
  simp only [CollatzResearch.WordTrace]
  refine ⟨11632332734574816330063517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15509776979433088440084689 11632332734574816330063517)
  ·
    refine ⟨4362124775465556123773819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11632332734574816330063517 4362124775465556123773819)
    ·
      refine ⟨6543187163198334185660729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4362124775465556123773819 6543187163198334185660729)
      ·
        refine ⟨4907390372398750639245547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6543187163198334185660729 4907390372398750639245547)
        ·
          refine ⟨7361085558598125958868321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4907390372398750639245547 7361085558598125958868321)
          ·
            refine ⟨5520814168948594469151241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7361085558598125958868321 5520814168948594469151241)
            ·
              refine ⟨4140610626711445851863431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5520814168948594469151241 4140610626711445851863431)
              ·
                refine ⟨6210915940067168777795147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4140610626711445851863431 6210915940067168777795147)
                ·
                  refine ⟨9316373910100753166692721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6210915940067168777795147 9316373910100753166692721)
                  ·
                    refine ⟨6987280432575564875019541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9316373910100753166692721 6987280432575564875019541)
                    ·
                      refine ⟨327528770276979603516541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6987280432575564875019541 327528770276979603516541)
                      ·
                        rfl

theorem cell23_637860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_637860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637860 prefixEnd_637860 := by exact prefixLift 637860
  have htrace : WordTrace (prefixWord ++ tailWord_637860) baseStart_637860 baseEnd_637860 := by
    simpa [prefixWord, tailWord_637860, baseEnd_637860] using wordTrace_append hprefix tailTrace_637860
  have hstable : (prefixWord ++ tailWord_637860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637860).length < 2 ^ (prefixWord ++ tailWord_637860).sum := by decide
  have hdescent : baseEnd_637860 < baseStart_637860 := by decide
  rcases family_descends (prefixWord ++ tailWord_637860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637920 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 4]
def baseStart_637920 : Nat := 118140960795 + 637920 * 2 ^ 59
def prefixEnd_637920 : Nat := 4983230072969 + 3 ^ 40 * 637920 * 2
def baseEnd_637920 : Nat := 327559579116249368766265

theorem tailTrace_637920 : CollatzResearch.WordTrace tailWord_637920 prefixEnd_637920 327559579116249368766265 := by
  unfold tailWord_637920
  simp only [CollatzResearch.WordTrace]
  refine ⟨11633426924466131453655607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15511235899288175271540809 11633426924466131453655607)
  ·
    refine ⟨17450140386699197180483411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11633426924466131453655607 17450140386699197180483411)
    ·
      refine ⟨26175210580048795770725117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17450140386699197180483411 26175210580048795770725117)
      ·
        refine ⟨9815703967518298414021919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26175210580048795770725117 9815703967518298414021919)
        ·
          refine ⟨14723555951277447621032879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9815703967518298414021919 14723555951277447621032879)
          ·
            refine ⟨22085333926916171431549319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14723555951277447621032879 22085333926916171431549319)
            ·
              refine ⟨33128000890374257147323979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22085333926916171431549319 33128000890374257147323979)
              ·
                refine ⟨49692001335561385720985969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33128000890374257147323979 49692001335561385720985969)
                ·
                  refine ⟨37269001001671039290739477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49692001335561385720985969 37269001001671039290739477)
                  ·
                    refine ⟨1746984421953329966753413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37269001001671039290739477 1746984421953329966753413)
                    ·
                      refine ⟨327559579116249368766265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1746984421953329966753413 327559579116249368766265)
                      ·
                        rfl

theorem cell23_637920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_637920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637920 prefixEnd_637920 := by exact prefixLift 637920
  have htrace : WordTrace (prefixWord ++ tailWord_637920) baseStart_637920 baseEnd_637920 := by
    simpa [prefixWord, tailWord_637920, baseEnd_637920] using wordTrace_append hprefix tailTrace_637920
  have hstable : (prefixWord ++ tailWord_637920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637920).length < 2 ^ (prefixWord ++ tailWord_637920).sum := by decide
  have hdescent : baseEnd_637920 < baseStart_637920 := by decide
  rcases family_descends (prefixWord ++ tailWord_637920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637927 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_637927 : Nat := 118140960795 + 637927 * 2 ^ 59
def prefixEnd_637927 : Nat := 4983230072969 + 3 ^ 40 * 637927 * 2
def baseEnd_637927 : Nat := 327563173480830841378733

theorem tailTrace_637927 : CollatzResearch.WordTrace tailWord_637927 prefixEnd_637927 327563173480830841378733 := by
  unfold tailWord_637927
  simp only [CollatzResearch.WordTrace]
  refine ⟨23267109159906903102816035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15511406106604602068544023 23267109159906903102816035)
  ·
    refine ⟨34900663739860354654224053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23267109159906903102816035 34900663739860354654224053)
    ·
      refine ⟨3271937225611908248833505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34900663739860354654224053 3271937225611908248833505)
      ·
        refine ⟨2453952919208931186625129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3271937225611908248833505 2453952919208931186625129)
        ·
          refine ⟨1840464689406698389968847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2453952919208931186625129 1840464689406698389968847)
          ·
            refine ⟨2760697034110047584953271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840464689406698389968847 2760697034110047584953271)
            ·
              refine ⟨4141045551165071377429907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2760697034110047584953271 4141045551165071377429907)
              ·
                refine ⟨6211568326747607066144861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4141045551165071377429907 6211568326747607066144861)
                ·
                  refine ⟨2329338122530352649804323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6211568326747607066144861 2329338122530352649804323)
                  ·
                    refine ⟨3494007183795528974706485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2329338122530352649804323 3494007183795528974706485)
                    ·
                      refine ⟨327563173480830841378733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3494007183795528974706485 327563173480830841378733)
                      ·
                        rfl

theorem cell23_637927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_637927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637927 prefixEnd_637927 := by exact prefixLift 637927
  have htrace : WordTrace (prefixWord ++ tailWord_637927) baseStart_637927 baseEnd_637927 := by
    simpa [prefixWord, tailWord_637927, baseEnd_637927] using wordTrace_append hprefix tailTrace_637927
  have hstable : (prefixWord ++ tailWord_637927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637927).length < 2 ^ (prefixWord ++ tailWord_637927).sum := by decide
  have hdescent : baseEnd_637927 < baseStart_637927 := by decide
  rcases family_descends (prefixWord ++ tailWord_637927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637937 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 6]
def baseStart_637937 : Nat := 118140960795 + 637937 * 2 ^ 59
def prefixEnd_637937 : Nat := 4983230072969 + 3 ^ 40 * 637937 * 2
def baseEnd_637937 : Nat := 327568308287375802253687

theorem tailTrace_637937 : CollatzResearch.WordTrace tailWord_637937 prefixEnd_637937 327568308287375802253687 := by
  unfold tailWord_637937
  simp only [CollatzResearch.WordTrace]
  refine ⟨23267473889870674810680065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15511649259913783207120043 23267473889870674810680065)
  ·
    refine ⟨17450605417403006108010049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23267473889870674810680065 17450605417403006108010049)
    ·
      refine ⟨13087954063052254581007537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17450605417403006108010049 13087954063052254581007537)
      ·
        refine ⟨9815965547289190935755653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13087954063052254581007537 9815965547289190935755653)
        ·
          refine ⟨1840493540116723300454185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9815965547289190935755653 1840493540116723300454185)
          ·
            refine ⟨1380370155087542475340639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1840493540116723300454185 1380370155087542475340639)
            ·
              refine ⟨2070555232631313713010959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380370155087542475340639 2070555232631313713010959)
              ·
                refine ⟨3105832848946970569516439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2070555232631313713010959 3105832848946970569516439)
                ·
                  refine ⟨4658749273420455854274659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3105832848946970569516439 4658749273420455854274659)
                  ·
                    refine ⟨6988123910130683781411989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4658749273420455854274659 6988123910130683781411989)
                    ·
                      refine ⟨327568308287375802253687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6988123910130683781411989 327568308287375802253687)
                      ·
                        rfl

theorem cell23_637937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_637937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637937 prefixEnd_637937 := by exact prefixLift 637937
  have htrace : WordTrace (prefixWord ++ tailWord_637937) baseStart_637937 baseEnd_637937 := by
    simpa [prefixWord, tailWord_637937, baseEnd_637937] using wordTrace_append hprefix tailTrace_637937
  have hstable : (prefixWord ++ tailWord_637937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637937).length < 2 ^ (prefixWord ++ tailWord_637937).sum := by decide
  have hdescent : baseEnd_637937 < baseStart_637937 := by decide
  rcases family_descends (prefixWord ++ tailWord_637937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_637957 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 3, 3, 3]
def baseStart_637957 : Nat := 118140960795 + 637957 * 2 ^ 59
def prefixEnd_637957 : Nat := 4983230072969 + 3 ^ 40 * 637957 * 2
def baseEnd_637957 : Nat := 327578577900465724003595

theorem tailTrace_637957 : CollatzResearch.WordTrace tailWord_637957 prefixEnd_637957 327578577900465724003595 := by
  unfold tailWord_637957
  simp only [CollatzResearch.WordTrace]
  refine ⟨23268203349798218226408125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15512135566532145484272083 23268203349798218226408125)
  ·
    refine ⟨8725576256174331834903047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23268203349798218226408125 8725576256174331834903047)
    ·
      refine ⟨13088364384261497752354571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8725576256174331834903047 13088364384261497752354571)
      ·
        refine ⟨19632546576392246628531857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13088364384261497752354571 19632546576392246628531857)
        ·
          refine ⟨14724409932294184971398893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19632546576392246628531857 14724409932294184971398893)
          ·
            refine ⟨5521653724610319364274585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14724409932294184971398893 5521653724610319364274585)
            ·
              refine ⟨4141240293457739523205939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5521653724610319364274585 4141240293457739523205939)
              ·
                refine ⟨6211860440186609284808909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4141240293457739523205939 6211860440186609284808909)
                ·
                  refine ⟨2329447665069978481803341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6211860440186609284808909 2329447665069978481803341)
                  ·
                    refine ⟨873542874401241930676253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2329447665069978481803341 873542874401241930676253)
                    ·
                      refine ⟨327578577900465724003595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 873542874401241930676253 327578577900465724003595)
                      ·
                        rfl

theorem cell23_637957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_637957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_637957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_637957 prefixEnd_637957 := by exact prefixLift 637957
  have htrace : WordTrace (prefixWord ++ tailWord_637957) baseStart_637957 baseEnd_637957 := by
    simpa [prefixWord, tailWord_637957, baseEnd_637957] using wordTrace_append hprefix tailTrace_637957
  have hstable : (prefixWord ++ tailWord_637957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_637957).length < 2 ^ (prefixWord ++ tailWord_637957).sum := by decide
  have hdescent : baseEnd_637957 < baseStart_637957 := by decide
  rcases family_descends (prefixWord ++ tailWord_637957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638034 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_638034 : Nat := 118140960795 + 638034 * 2 ^ 59
def prefixEnd_638034 : Nat := 4983230072969 + 3 ^ 40 * 638034 * 2
def baseEnd_638034 : Nat := 327618115910861922740741

theorem tailTrace_638034 : CollatzResearch.WordTrace tailWord_638034 prefixEnd_638034 327618115910861922740741 := by
  unfold tailWord_638034
  simp only [CollatzResearch.WordTrace]
  refine ⟨5817752942629815094240289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15514007847012840251307437 5817752942629815094240289)
  ·
    refine ⟨4363314706972361320680217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5817752942629815094240289 4363314706972361320680217)
    ·
      refine ⟨3272486030229270990510163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4363314706972361320680217 3272486030229270990510163)
      ·
        refine ⟨4908729045343906485765245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3272486030229270990510163 4908729045343906485765245)
        ·
          refine ⟨1840773392003964932161967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4908729045343906485765245 1840773392003964932161967)
          ·
            refine ⟨2761160088005947398242951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840773392003964932161967 2761160088005947398242951)
            ·
              refine ⟨4141740132008921097364427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2761160088005947398242951 4141740132008921097364427)
              ·
                refine ⟨6212610198013381646046641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4141740132008921097364427 6212610198013381646046641)
                ·
                  refine ⟨4659457648510036234534981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6212610198013381646046641 4659457648510036234534981)
                  ·
                    refine ⟨873648309095631793975309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4659457648510036234534981 873648309095631793975309)
                    ·
                      refine ⟨327618115910861922740741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 873648309095631793975309 327618115910861922740741)
                      ·
                        rfl

theorem cell23_638034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_638034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638034 prefixEnd_638034 := by exact prefixLift 638034
  have htrace : WordTrace (prefixWord ++ tailWord_638034) baseStart_638034 baseEnd_638034 := by
    simpa [prefixWord, tailWord_638034, baseEnd_638034] using wordTrace_append hprefix tailTrace_638034
  have hstable : (prefixWord ++ tailWord_638034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638034).length < 2 ^ (prefixWord ++ tailWord_638034).sum := by decide
  have hdescent : baseEnd_638034 < baseStart_638034 := by decide
  rcases family_descends (prefixWord ++ tailWord_638034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638037 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 7]
def baseStart_638037 : Nat := 118140960795 + 638037 * 2 ^ 59
def prefixEnd_638037 : Nat := 4983230072969 + 3 ^ 40 * 638037 * 2
def baseEnd_638037 : Nat := 36402184039202823444803

theorem tailTrace_638037 : CollatzResearch.WordTrace tailWord_638037 prefixEnd_638037 36402184039202823444803 := by
  unfold tailWord_638037
  simp only [CollatzResearch.WordTrace]
  refine ⟨23271121189508391889320365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15514080793005594592880243 23271121189508391889320365)
  ·
    refine ⟨8726670446065646958495137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23271121189508391889320365 8726670446065646958495137)
    ·
      refine ⟨6545002834549235218871353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8726670446065646958495137 6545002834549235218871353)
      ·
        refine ⟨4908752125911926414153515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6545002834549235218871353 4908752125911926414153515)
        ·
          refine ⟨7363128188867889621230273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4908752125911926414153515 7363128188867889621230273)
          ·
            refine ⟨5522346141650917215922705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7363128188867889621230273 5522346141650917215922705)
            ·
              refine ⟨4141759606238187911942029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5522346141650917215922705 4141759606238187911942029)
              ·
                refine ⟨1553159852339320466978261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4141759606238187911942029 1553159852339320466978261)
                ·
                  refine ⟨36402184039202823444803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1553159852339320466978261 36402184039202823444803)
                  ·
                    rfl

theorem cell23_638037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_638037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638037 prefixEnd_638037 := by exact prefixLift 638037
  have htrace : WordTrace (prefixWord ++ tailWord_638037) baseStart_638037 baseEnd_638037 := by
    simpa [prefixWord, tailWord_638037, baseEnd_638037] using wordTrace_append hprefix tailTrace_638037
  have hstable : (prefixWord ++ tailWord_638037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638037).length < 2 ^ (prefixWord ++ tailWord_638037).sum := by decide
  have hdescent : baseEnd_638037 < baseStart_638037 := by decide
  rcases family_descends (prefixWord ++ tailWord_638037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638044 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_638044 : Nat := 118140960795 + 638044 * 2 ^ 59
def prefixEnd_638044 : Nat := 4983230072969 + 3 ^ 40 * 638044 * 2
def baseEnd_638044 : Nat := 327623250717406883615695

theorem tailTrace_638044 : CollatzResearch.WordTrace tailWord_638044 prefixEnd_638044 327623250717406883615695 := by
  unfold tailWord_638044
  simp only [CollatzResearch.WordTrace]
  refine ⟨11635688250241516042412593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15514251000322021389883457 11635688250241516042412593)
  ·
    refine ⟨8726766187681137031809445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11635688250241516042412593 8726766187681137031809445)
    ·
      refine ⟨1636268660190213193464271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8726766187681137031809445 1636268660190213193464271)
      ·
        refine ⟨2454402990285319790196407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1636268660190213193464271 2454402990285319790196407)
        ·
          refine ⟨3681604485427979685294611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454402990285319790196407 3681604485427979685294611)
          ·
            refine ⟨5522406728141969527941917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3681604485427979685294611 5522406728141969527941917)
            ·
              refine ⟨2070902523053238572978219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5522406728141969527941917 2070902523053238572978219)
              ·
                refine ⟨3106353784579857859467329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2070902523053238572978219 3106353784579857859467329)
                ·
                  refine ⟨2329765338434893394600497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3106353784579857859467329 2329765338434893394600497)
                  ·
                    refine ⟨1747324003826170045950373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2329765338434893394600497 1747324003826170045950373)
                    ·
                      refine ⟨327623250717406883615695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1747324003826170045950373 327623250717406883615695)
                      ·
                        rfl

theorem cell23_638044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_638044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638044 prefixEnd_638044 := by exact prefixLift 638044
  have htrace : WordTrace (prefixWord ++ tailWord_638044) baseStart_638044 baseEnd_638044 := by
    simpa [prefixWord, tailWord_638044, baseEnd_638044] using wordTrace_append hprefix tailTrace_638044
  have hstable : (prefixWord ++ tailWord_638044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638044).length < 2 ^ (prefixWord ++ tailWord_638044).sum := by decide
  have hdescent : baseEnd_638044 < baseStart_638044 := by decide
  rcases family_descends (prefixWord ++ tailWord_638044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638069 : List Nat := [1, 3, 4, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_638069 : Nat := 118140960795 + 638069 * 2 ^ 59
def prefixEnd_638069 : Nat := 4983230072969 + 3 ^ 40 * 638069 * 2
def baseEnd_638069 : Nat := 327636087733769285803081

theorem tailTrace_638069 : CollatzResearch.WordTrace tailWord_638069 prefixEnd_638069 327636087733769285803081 := by
  unfold tailWord_638069
  simp only [CollatzResearch.WordTrace]
  refine ⟨23272288325392461354485261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15514858883594974236323507 23272288325392461354485261)
  ·
    refine ⟨8727108122022173007931973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23272288325392461354485261 8727108122022173007931973)
    ·
      refine ⟨1636332772879157438987245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8727108122022173007931973 1636332772879157438987245)
      ·
        refine ⟨613624789829684039620217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1636332772879157438987245 613624789829684039620217)
        ·
          refine ⟨460218592372263029715163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 613624789829684039620217 460218592372263029715163)
          ·
            refine ⟨690327888558394544572745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460218592372263029715163 690327888558394544572745)
            ·
              refine ⟨517745916418795908429559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690327888558394544572745 517745916418795908429559)
              ·
                refine ⟨776618874628193862644339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517745916418795908429559 776618874628193862644339)
                ·
                  refine ⟨1164928311942290793966509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776618874628193862644339 1164928311942290793966509)
                  ·
                    refine ⟨436848116978359047737441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1164928311942290793966509 436848116978359047737441)
                    ·
                      refine ⟨327636087733769285803081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 436848116978359047737441 327636087733769285803081)
                      ·
                        rfl

theorem cell23_638069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_638069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638069 prefixEnd_638069 := by exact prefixLift 638069
  have htrace : WordTrace (prefixWord ++ tailWord_638069) baseStart_638069 baseEnd_638069 := by
    simpa [prefixWord, tailWord_638069, baseEnd_638069] using wordTrace_append hprefix tailTrace_638069
  have hstable : (prefixWord ++ tailWord_638069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638069).length < 2 ^ (prefixWord ++ tailWord_638069).sum := by decide
  have hdescent : baseEnd_638069 < baseStart_638069 := by decide
  rcases family_descends (prefixWord ++ tailWord_638069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638104 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_638104 : Nat := 118140960795 + 638104 * 2 ^ 59
def prefixEnd_638104 : Nat := 4983230072969 + 3 ^ 40 * 638104 * 2
def baseEnd_638104 : Nat := 327654059556676648865419

theorem tailTrace_638104 : CollatzResearch.WordTrace tailWord_638104 prefixEnd_638104 327654059556676648865419 := by
  unfold tailWord_638104
  simp only [CollatzResearch.WordTrace]
  refine ⟨11636782440132831166004683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15515709920177108221339577 11636782440132831166004683)
  ·
    refine ⟨17455173660199246749007025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11636782440132831166004683 17455173660199246749007025)
    ·
      refine ⟨13091380245149435061755269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17455173660199246749007025 13091380245149435061755269)
      ·
        refine ⟨2454633795965519074079113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13091380245149435061755269 2454633795965519074079113)
        ·
          refine ⟨1840975346974139305559335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2454633795965519074079113 1840975346974139305559335)
          ·
            refine ⟨2761463020461208958339003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1840975346974139305559335 2761463020461208958339003)
            ·
              refine ⟨4142194530691813437508505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2761463020461208958339003 4142194530691813437508505)
              ·
                refine ⟨3106645898018860078131379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4142194530691813437508505 3106645898018860078131379)
                ·
                  refine ⟨4659968847028290117197069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3106645898018860078131379 4659968847028290117197069)
                  ·
                    refine ⟨1747488317635608793948901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4659968847028290117197069 1747488317635608793948901)
                    ·
                      refine ⟨327654059556676648865419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1747488317635608793948901 327654059556676648865419)
                      ·
                        rfl

theorem cell23_638104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_638104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638104 prefixEnd_638104 := by exact prefixLift 638104
  have htrace : WordTrace (prefixWord ++ tailWord_638104) baseStart_638104 baseEnd_638104 := by
    simpa [prefixWord, tailWord_638104, baseEnd_638104] using wordTrace_append hprefix tailTrace_638104
  have hstable : (prefixWord ++ tailWord_638104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638104).length < 2 ^ (prefixWord ++ tailWord_638104).sum := by decide
  have hdescent : baseEnd_638104 < baseStart_638104 := by decide
  rcases family_descends (prefixWord ++ tailWord_638104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638127 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 8]
def baseStart_638127 : Nat := 118140960795 + 638127 * 2 ^ 59
def prefixEnd_638127 : Nat := 4983230072969 + 3 ^ 40 * 638127 * 2
def baseEnd_638127 : Nat := 36407318845747784319757

theorem tailTrace_638127 : CollatzResearch.WordTrace tailWord_638127 prefixEnd_638127 36407318845747784319757 := by
  unfold tailWord_638127
  simp only [CollatzResearch.WordTrace]
  refine ⟨23274403759182337260096635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15516269172788224840064423 23274403759182337260096635)
  ·
    refine ⟨34911605638773505890144953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23274403759182337260096635 34911605638773505890144953)
    ·
      refine ⟨26183704229080129417608715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34911605638773505890144953 26183704229080129417608715)
      ·
        refine ⟨39275556343620194126413073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26183704229080129417608715 39275556343620194126413073)
        ·
          refine ⟨29456667257715145594809805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39275556343620194126413073 29456667257715145594809805)
          ·
            refine ⟨11046250221643179598053677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29456667257715145594809805 11046250221643179598053677)
            ·
              refine ⟨4142343833116192349270129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11046250221643179598053677 4142343833116192349270129)
              ·
                refine ⟨3106757874837144261952597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4142343833116192349270129 3106757874837144261952597)
                ·
                  refine ⟨36407318845747784319757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3106757874837144261952597 36407318845747784319757)
                  ·
                    rfl

theorem cell23_638127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 8].length) (baseStart_638127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638127 prefixEnd_638127 := by exact prefixLift 638127
  have htrace : WordTrace (prefixWord ++ tailWord_638127) baseStart_638127 baseEnd_638127 := by
    simpa [prefixWord, tailWord_638127, baseEnd_638127] using wordTrace_append hprefix tailTrace_638127
  have hstable : (prefixWord ++ tailWord_638127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638127).length < 2 ^ (prefixWord ++ tailWord_638127).sum := by decide
  have hdescent : baseEnd_638127 < baseStart_638127 := by decide
  rcases family_descends (prefixWord ++ tailWord_638127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638147 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 6]
def baseStart_638147 : Nat := 118140960795 + 638147 * 2 ^ 59
def prefixEnd_638147 : Nat := 4983230072969 + 3 ^ 40 * 638147 * 2
def baseEnd_638147 : Nat := 327676139224819980627721

theorem tailTrace_638147 : CollatzResearch.WordTrace tailWord_638147 prefixEnd_638147 327676139224819980627721 := by
  unfold tailWord_638147
  simp only [CollatzResearch.WordTrace]
  refine ⟨23275133219109880675824695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15516755479406587117216463 23275133219109880675824695)
  ·
    refine ⟨34912699828664821013737043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23275133219109880675824695 34912699828664821013737043)
    ·
      refine ⟨52369049742997231520605565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34912699828664821013737043 52369049742997231520605565)
      ·
        refine ⟨19638393653623961820227087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52369049742997231520605565 19638393653623961820227087)
        ·
          refine ⟨29457590480435942730340631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19638393653623961820227087 29457590480435942730340631)
          ·
            refine ⟨44186385720653914095510947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29457590480435942730340631 44186385720653914095510947)
            ·
              refine ⟨66279578580980871143266421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44186385720653914095510947 66279578580980871143266421)
              ·
                refine ⟨6213710491966956669681227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66279578580980871143266421 6213710491966956669681227)
                ·
                  refine ⟨9320565737950435004521841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6213710491966956669681227 9320565737950435004521841)
                  ·
                    refine ⟨6990424303462826253391381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9320565737950435004521841 6990424303462826253391381)
                    ·
                      refine ⟨327676139224819980627721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6990424303462826253391381 327676139224819980627721)
                      ·
                        rfl

theorem cell23_638147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_638147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638147 prefixEnd_638147 := by exact prefixLift 638147
  have htrace : WordTrace (prefixWord ++ tailWord_638147) baseStart_638147 baseEnd_638147 := by
    simpa [prefixWord, tailWord_638147, baseEnd_638147] using wordTrace_append hprefix tailTrace_638147
  have hstable : (prefixWord ++ tailWord_638147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638147).length < 2 ^ (prefixWord ++ tailWord_638147).sum := by decide
  have hdescent : baseEnd_638147 < baseStart_638147 := by decide
  rcases family_descends (prefixWord ++ tailWord_638147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638231 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 3]
def baseStart_638231 : Nat := 118140960795 + 638231 * 2 ^ 59
def prefixEnd_638231 : Nat := 4983230072969 + 3 ^ 40 * 638231 * 2
def baseEnd_638231 : Nat := 327719271599797651977335

theorem tailTrace_638231 : CollatzResearch.WordTrace tailWord_638231 prefixEnd_638231 327719271599797651977335 := by
  unfold tailWord_638231
  simp only [CollatzResearch.WordTrace]
  refine ⟨23278196950805563021882547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15518797967203708681255031 23278196950805563021882547)
  ·
    refine ⟨34917295426208344532823821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23278196950805563021882547 34917295426208344532823821)
    ·
      refine ⟨13093985784828129199808933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34917295426208344532823821 13093985784828129199808933)
      ·
        refine ⟨2455122334655274224964175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13093985784828129199808933 2455122334655274224964175)
        ·
          refine ⟨3682683501982911337446263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455122334655274224964175 3682683501982911337446263)
          ·
            refine ⟨5524025252974367006169395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3682683501982911337446263 5524025252974367006169395)
            ·
              refine ⟨8286037879461550509254093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5524025252974367006169395 8286037879461550509254093)
              ·
                refine ⟨3107264204798081440970285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8286037879461550509254093 3107264204798081440970285)
                ·
                  refine ⟨1165224076799280540363857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3107264204798081440970285 1165224076799280540363857)
                  ·
                    refine ⟨873918057599460405272893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1165224076799280540363857 873918057599460405272893)
                    ·
                      refine ⟨327719271599797651977335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 873918057599460405272893 327719271599797651977335)
                      ·
                        rfl

theorem cell23_638231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_638231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638231 prefixEnd_638231 := by exact prefixLift 638231
  have htrace : WordTrace (prefixWord ++ tailWord_638231) baseStart_638231 baseEnd_638231 := by
    simpa [prefixWord, tailWord_638231, baseEnd_638231] using wordTrace_append hprefix tailTrace_638231
  have hstable : (prefixWord ++ tailWord_638231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638231).length < 2 ^ (prefixWord ++ tailWord_638231).sum := by decide
  have hdescent : baseEnd_638231 < baseStart_638231 := by decide
  rcases family_descends (prefixWord ++ tailWord_638231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638242 : List Nat := [3, 3, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_638242 : Nat := 118140960795 + 638242 * 2 ^ 59
def prefixEnd_638242 : Nat := 4983230072969 + 3 ^ 40 * 638242 * 2
def baseEnd_638242 : Nat := 109241639962332369646595

theorem tailTrace_638242 : CollatzResearch.WordTrace tailWord_638242 prefixEnd_638242 109241639962332369646595 := by
  unfold tailWord_638242
  simp only [CollatzResearch.WordTrace]
  refine ⟨5819649538441427975133245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15519065435843807933688653 5819649538441427975133245)
  ·
    refine ⟨2182368576915535490674967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5819649538441427975133245 2182368576915535490674967)
    ·
      refine ⟨3273552865373303236012451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2182368576915535490674967 3273552865373303236012451)
      ·
        refine ⟨4910329298059954854018677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3273552865373303236012451 4910329298059954854018677)
        ·
          refine ⟨460343371693120767564251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4910329298059954854018677 460343371693120767564251)
          ·
            refine ⟨690515057539681151346377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460343371693120767564251 690515057539681151346377)
            ·
              refine ⟨517886293154760863509783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690515057539681151346377 517886293154760863509783)
              ·
                refine ⟨776829439732141295264675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517886293154760863509783 776829439732141295264675)
                ·
                  refine ⟨1165244159598211942897013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776829439732141295264675 1165244159598211942897013)
                  ·
                    refine ⟨109241639962332369646595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1165244159598211942897013 109241639962332369646595)
                    ·
                      rfl

theorem cell23_638242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_638242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638242 prefixEnd_638242 := by exact prefixLift 638242
  have htrace : WordTrace (prefixWord ++ tailWord_638242) baseStart_638242 baseEnd_638242 := by
    simpa [prefixWord, tailWord_638242, baseEnd_638242] using wordTrace_append hprefix tailTrace_638242
  have hstable : (prefixWord ++ tailWord_638242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638242).length < 2 ^ (prefixWord ++ tailWord_638242).sum := by decide
  have hdescent : baseEnd_638242 < baseStart_638242 := by decide
  rcases family_descends (prefixWord ++ tailWord_638242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638245 : List Nat := [1, 3, 1, 2, 4, 3, 2, 1, 1, 1, 4]
def baseStart_638245 : Nat := 118140960795 + 638245 * 2 ^ 59
def prefixEnd_638245 : Nat := 4983230072969 + 3 ^ 40 * 638245 * 2
def baseEnd_638245 : Nat := 327726460328960597202271

theorem tailTrace_638245 : CollatzResearch.WordTrace tailWord_638245 prefixEnd_638245 327726460328960597202271 := by
  unfold tailWord_638245
  simp only [CollatzResearch.WordTrace]
  refine ⟨23278707572754843412892189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15519138381836562275261459 23278707572754843412892189)
  ·
    refine ⟨8729515339783066279834571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23278707572754843412892189 8729515339783066279834571)
    ·
      refine ⟨13094273009674599419751857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8729515339783066279834571 13094273009674599419751857)
      ·
        refine ⟨9820704757255949564813893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13094273009674599419751857 9820704757255949564813893)
        ·
          refine ⟨1841382141985490543402605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9820704757255949564813893 1841382141985490543402605)
          ·
            refine ⟨690518303244558953775977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1841382141985490543402605 690518303244558953775977)
            ·
              refine ⟨517888727433419215331983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690518303244558953775977 517888727433419215331983)
              ·
                refine ⟨776833091150128822997975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517888727433419215331983 776833091150128822997975)
                ·
                  refine ⟨1165249636725193234496963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776833091150128822997975 1165249636725193234496963)
                  ·
                    refine ⟨1747874455087789851745445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1165249636725193234496963 1747874455087789851745445)
                    ·
                      refine ⟨327726460328960597202271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1747874455087789851745445 327726460328960597202271)
                      ·
                        rfl

theorem cell23_638245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_638245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638245 prefixEnd_638245 := by exact prefixLift 638245
  have htrace : WordTrace (prefixWord ++ tailWord_638245) baseStart_638245 baseEnd_638245 := by
    simpa [prefixWord, tailWord_638245, baseEnd_638245] using wordTrace_append hprefix tailTrace_638245
  have hstable : (prefixWord ++ tailWord_638245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638245).length < 2 ^ (prefixWord ++ tailWord_638245).sum := by decide
  have hdescent : baseEnd_638245 < baseStart_638245 := by decide
  rcases family_descends (prefixWord ++ tailWord_638245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_638371 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 2, 5]
def baseStart_638371 : Nat := 118140960795 + 638371 * 2 ^ 59
def prefixEnd_638371 : Nat := 4983230072969 + 3 ^ 40 * 638371 * 2
def baseEnd_638371 : Nat := 109263719630475701408897

theorem tailTrace_638371 : CollatzResearch.WordTrace tailWord_638371 prefixEnd_638371 109263719630475701408897 := by
  unfold tailWord_638371
  simp only [CollatzResearch.WordTrace]
  refine ⟨23283303170298366931978967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15522202113532244621319311 23283303170298366931978967)
  ·
    refine ⟨34924954755447550397968451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23283303170298366931978967 34924954755447550397968451)
    ·
      refine ⟨52387432133171325596952677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34924954755447550397968451 52387432133171325596952677)
      ·
        refine ⟨9822643524969623549428627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52387432133171325596952677 9822643524969623549428627)
        ·
          refine ⟨14733965287454435324142941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9822643524969623549428627 14733965287454435324142941)
          ·
            refine ⟨5525236982795413246553603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14733965287454435324142941 5525236982795413246553603)
            ·
              refine ⟨8287855474193119869830405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5525236982795413246553603 8287855474193119869830405)
              ·
                refine ⟨1553972901411209975593201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8287855474193119869830405 1553972901411209975593201)
                ·
                  refine ⟨1165479676058407481694901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1553972901411209975593201 1165479676058407481694901)
                  ·
                    refine ⟨109263719630475701408897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1165479676058407481694901 109263719630475701408897)
                    ·
                      rfl

theorem cell23_638371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 5].length) (baseStart_638371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_638371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_638371 prefixEnd_638371 := by exact prefixLift 638371
  have htrace : WordTrace (prefixWord ++ tailWord_638371) baseStart_638371 baseEnd_638371 := by
    simpa [prefixWord, tailWord_638371, baseEnd_638371] using wordTrace_append hprefix tailTrace_638371
  have hstable : (prefixWord ++ tailWord_638371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_638371).length < 2 ^ (prefixWord ++ tailWord_638371).sum := by decide
  have hdescent : baseEnd_638371 < baseStart_638371 := by decide
  rcases family_descends (prefixWord ++ tailWord_638371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
