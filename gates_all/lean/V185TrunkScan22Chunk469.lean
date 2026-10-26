import V185TrunkScan22Chunk468

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4180194 : List Nat := [3, 3, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_4180194 : Nat := 118140960795 + 4180194 * 2 ^ 59
def prefixEnd_4180194 : Nat := 4983230072969 + 3 ^ 40 * 4180194 * 2
def baseEnd_4180194 : Nat := 1430965834027148803633763

theorem tailTrace_4180194 : CollatzResearch.WordTrace tailWord_4180194 prefixEnd_4180194 1430965834027148803633763 := by
  unfold tailWord_4180194
  simp only [CollatzResearch.WordTrace]
  refine ⟨38116050154469633285552909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101642800411919022094807757 38116050154469633285552909)
  ·
    refine ⟨14293518807926112482082341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38116050154469633285552909 14293518807926112482082341)
    ·
      refine ⟨2680034776486146090390439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14293518807926112482082341 2680034776486146090390439)
      ·
        refine ⟨4020052164729219135585659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2680034776486146090390439 4020052164729219135585659)
        ·
          refine ⟨6030078247093828703378489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4020052164729219135585659 6030078247093828703378489)
          ·
            refine ⟨4522558685320371527533867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6030078247093828703378489 4522558685320371527533867)
            ·
              refine ⟨6783838027980557291300801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4522558685320371527533867 6783838027980557291300801)
              ·
                refine ⟨5087878520985417968475601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6783838027980557291300801 5087878520985417968475601)
                ·
                  refine ⟨3815908890739063476356701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5087878520985417968475601 3815908890739063476356701)
                  ·
                    refine ⟨1430965834027148803633763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3815908890739063476356701 1430965834027148803633763)
                    ·
                      rfl

theorem cell22_4180194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_4180194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180194 prefixEnd_4180194 := by exact prefixLift 4180194
  have htrace : WordTrace (prefixWord ++ tailWord_4180194) baseStart_4180194 baseEnd_4180194 := by
    simpa [prefixWord, tailWord_4180194, baseEnd_4180194] using wordTrace_append hprefix tailTrace_4180194
  have hstable : (prefixWord ++ tailWord_4180194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180194).length < 2 ^ (prefixWord ++ tailWord_4180194).sum := by decide
  have hdescent : baseEnd_4180194 < baseStart_4180194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180319 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 7]
def baseStart_4180319 : Nat := 118140960795 + 4180319 * 2 ^ 59
def prefixEnd_4180319 : Nat := 4983230072969 + 3 ^ 40 * 4180319 * 2
def baseEnd_4180319 : Nat := 477002874693896714752793

theorem tailTrace_4180319 : CollatzResearch.WordTrace tailWord_4180319 prefixEnd_4180319 477002874693896714752793 := by
  unfold tailWord_4180319
  simp only [CollatzResearch.WordTrace]
  refine ⟨152468759742425679490512011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101645839828283786327008007 152468759742425679490512011)
  ·
    refine ⟨228703139613638519235768017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152468759742425679490512011 228703139613638519235768017)
    ·
      refine ⟨171527354710228889426826013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228703139613638519235768017 171527354710228889426826013)
      ·
        refine ⟨64322758016335833535059755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171527354710228889426826013 64322758016335833535059755)
        ·
          refine ⟨96484137024503750302589633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64322758016335833535059755 96484137024503750302589633)
          ·
            refine ⟨72363102768377812726942225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96484137024503750302589633 72363102768377812726942225)
            ·
              refine ⟨54272327076283359545206669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72363102768377812726942225 54272327076283359545206669)
              ·
                refine ⟨20352122653606259829452501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54272327076283359545206669 20352122653606259829452501)
                ·
                  refine ⟨477002874693896714752793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20352122653606259829452501 477002874693896714752793)
                  ·
                    rfl

theorem cell22_4180319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 7].length) (baseStart_4180319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180319 prefixEnd_4180319 := by exact prefixLift 4180319
  have htrace : WordTrace (prefixWord ++ tailWord_4180319) baseStart_4180319 baseEnd_4180319 := by
    simpa [prefixWord, tailWord_4180319, baseEnd_4180319] using wordTrace_append hprefix tailTrace_4180319
  have hstable : (prefixWord ++ tailWord_4180319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180319).length < 2 ^ (prefixWord ++ tailWord_4180319).sum := by decide
  have hdescent : baseEnd_4180319 < baseStart_4180319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180336 : List Nat := [2, 1, 1, 1, 4, 3, 2, 3, 5]
def baseStart_4180336 : Nat := 118140960795 + 4180336 * 2 ^ 59
def prefixEnd_4180336 : Nat := 4983230072969 + 3 ^ 40 * 4180336 * 2
def baseEnd_4180336 : Nat := 477004814509702588861109

theorem tailTrace_4180336 : CollatzResearch.WordTrace tailWord_4180336 prefixEnd_4180336 477004814509702588861109 := by
  unfold tailWord_4180336
  simp only [CollatzResearch.WordTrace]
  refine ⟨76234689891682045696940431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101646253188909394262587241 76234689891682045696940431)
  ·
    refine ⟨114352034837523068545410647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76234689891682045696940431 114352034837523068545410647)
    ·
      refine ⟨171528052256284602818115971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114352034837523068545410647 171528052256284602818115971)
      ·
        refine ⟨257292078384426904227173957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171528052256284602818115971 257292078384426904227173957)
        ·
          refine ⟨48242264697080044542595117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257292078384426904227173957 48242264697080044542595117)
          ·
            refine ⟨18090849261405016703473169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48242264697080044542595117 18090849261405016703473169)
            ·
              refine ⟨13568136946053762527604877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18090849261405016703473169 13568136946053762527604877)
              ·
                refine ⟨5088051354770160947851829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13568136946053762527604877 5088051354770160947851829)
                ·
                  refine ⟨477004814509702588861109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5088051354770160947851829 477004814509702588861109)
                  ·
                    rfl

theorem cell22_4180336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 5].length) (baseStart_4180336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180336 prefixEnd_4180336 := by exact prefixLift 4180336
  have htrace : WordTrace (prefixWord ++ tailWord_4180336) baseStart_4180336 baseEnd_4180336 := by
    simpa [prefixWord, tailWord_4180336, baseEnd_4180336] using wordTrace_append hprefix tailTrace_4180336
  have hstable : (prefixWord ++ tailWord_4180336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180336).length < 2 ^ (prefixWord ++ tailWord_4180336).sum := by decide
  have hdescent : baseEnd_4180336 < baseStart_4180336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180413 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_4180413 : Nat := 118140960795 + 4180413 * 2 ^ 59
def prefixEnd_4180413 : Nat := 4983230072969 + 3 ^ 40 * 4180413 * 2
def baseEnd_4180413 : Nat := 1431040802202705232408091

theorem tailTrace_4180413 : CollatzResearch.WordTrace tailWord_4180413 prefixEnd_4180413 1431040802202705232408091 := by
  unfold tailWord_4180413
  simp only [CollatzResearch.WordTrace]
  refine ⟨152472188204085133544433893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101648125469390089029622595 152472188204085133544433893)
  ·
    refine ⟨28588535288265962539581355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152472188204085133544433893 28588535288265962539581355)
    ·
      refine ⟨42882802932398943809372033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28588535288265962539581355 42882802932398943809372033)
      ·
        refine ⟨32162102199299207857029025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42882802932398943809372033 32162102199299207857029025)
        ·
          refine ⟨24121576649474405892771769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32162102199299207857029025 24121576649474405892771769)
          ·
            refine ⟨18091182487105804419578827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24121576649474405892771769 18091182487105804419578827)
            ·
              refine ⟨27136773730658706629368241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18091182487105804419578827 27136773730658706629368241)
              ·
                refine ⟨20352580297994029972026181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27136773730658706629368241 20352580297994029972026181)
                ·
                  refine ⟨3816108805873880619754909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20352580297994029972026181 3816108805873880619754909)
                  ·
                    refine ⟨1431040802202705232408091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3816108805873880619754909 1431040802202705232408091)
                    ·
                      rfl

theorem cell22_4180413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_4180413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180413 prefixEnd_4180413 := by exact prefixLift 4180413
  have htrace : WordTrace (prefixWord ++ tailWord_4180413) baseStart_4180413 baseEnd_4180413 := by
    simpa [prefixWord, tailWord_4180413, baseEnd_4180413] using wordTrace_append hprefix tailTrace_4180413
  have hstable : (prefixWord ++ tailWord_4180413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180413).length < 2 ^ (prefixWord ++ tailWord_4180413).sum := by decide
  have hdescent : baseEnd_4180413 < baseStart_4180413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180447 : List Nat := [1, 1, 2, 3, 3, 4, 2, 1, 2, 3]
def baseStart_4180447 : Nat := 118140960795 + 4180447 * 2 ^ 59
def prefixEnd_4180447 : Nat := 4983230072969 + 3 ^ 40 * 4180447 * 2
def baseEnd_4180447 : Nat := 1431052441097540477057987

theorem tailTrace_4180447 : CollatzResearch.WordTrace tailWord_4180447 prefixEnd_4180447 1431052441097540477057987 := by
  unfold tailWord_4180447
  simp only [CollatzResearch.WordTrace]
  refine ⟨152473428285961957351171595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101648952190641304900781063 152473428285961957351171595)
  ·
    refine ⟨228710142428942936026757393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152473428285961957351171595 228710142428942936026757393)
    ·
      refine ⟨171532606821707202020068045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228710142428942936026757393 171532606821707202020068045)
      ·
        refine ⟨64324727558140200757525517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171532606821707202020068045 64324727558140200757525517)
        ·
          refine ⟨24121772834302575284072069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64324727558140200757525517 24121772834302575284072069)
          ·
            refine ⟨4522832406431732865763513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24121772834302575284072069 4522832406431732865763513)
            ·
              refine ⟨3392124304823799649322635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4522832406431732865763513 3392124304823799649322635)
              ·
                refine ⟨5088186457235699473983953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3392124304823799649322635 5088186457235699473983953)
                ·
                  refine ⟨3816139842926774605487965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5088186457235699473983953 3816139842926774605487965)
                  ·
                    refine ⟨1431052441097540477057987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3816139842926774605487965 1431052441097540477057987)
                    ·
                      rfl

theorem cell22_4180447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 2, 3].length) (baseStart_4180447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180447 prefixEnd_4180447 := by exact prefixLift 4180447
  have htrace : WordTrace (prefixWord ++ tailWord_4180447) baseStart_4180447 baseEnd_4180447 := by
    simpa [prefixWord, tailWord_4180447, baseEnd_4180447] using wordTrace_append hprefix tailTrace_4180447
  have hstable : (prefixWord ++ tailWord_4180447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180447).length < 2 ^ (prefixWord ++ tailWord_4180447).sum := by decide
  have hdescent : baseEnd_4180447 < baseStart_4180447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180492 : List Nat := [2, 2, 1, 2, 4, 2, 1, 4, 1, 3]
def baseStart_4180492 : Nat := 118140960795 + 4180492 * 2 ^ 59
def prefixEnd_4180492 : Nat := 4983230072969 + 3 ^ 40 * 4180492 * 2
def baseEnd_4180492 : Nat := 1431067845517175359682849

theorem tailTrace_4180492 : CollatzResearch.WordTrace tailWord_4180492 prefixEnd_4180492 1431067845517175359682849 := by
  unfold tailWord_4180492
  simp only [CollatzResearch.WordTrace]
  refine ⟨76237534785399465018279865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101650046380532620024373153 76237534785399465018279865)
  ·
    refine ⟨57178151089049598763709899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76237534785399465018279865 57178151089049598763709899)
    ·
      refine ⟨85767226633574398145564849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57178151089049598763709899 85767226633574398145564849)
      ·
        refine ⟨64325419975180798609173637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85767226633574398145564849 64325419975180798609173637)
        ·
          refine ⟨12061016245346399739220057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64325419975180798609173637 12061016245346399739220057)
          ·
            refine ⟨9045762184009799804415043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12061016245346399739220057 9045762184009799804415043)
            ·
              refine ⟨13568643276014699706622565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9045762184009799804415043 13568643276014699706622565)
              ·
                refine ⟨2544120614252756194991731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13568643276014699706622565 2544120614252756194991731)
                ·
                  refine ⟨3816180921379134292487597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544120614252756194991731 3816180921379134292487597)
                  ·
                    refine ⟨1431067845517175359682849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3816180921379134292487597 1431067845517175359682849)
                    ·
                      rfl

theorem cell22_4180492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_4180492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180492 prefixEnd_4180492 := by exact prefixLift 4180492
  have htrace : WordTrace (prefixWord ++ tailWord_4180492) baseStart_4180492 baseEnd_4180492 := by
    simpa [prefixWord, tailWord_4180492, baseEnd_4180492] using wordTrace_append hprefix tailTrace_4180492
  have hstable : (prefixWord ++ tailWord_4180492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180492).length < 2 ^ (prefixWord ++ tailWord_4180492).sum := by decide
  have hdescent : baseEnd_4180492 < baseStart_4180492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180565 : List Nat := [1, 3, 2, 2, 1, 1, 2, 5, 2, 3]
def baseStart_4180565 : Nat := 118140960795 + 4180565 * 2 ^ 59
def prefixEnd_4180565 : Nat := 4983230072969 + 3 ^ 40 * 4180565 * 2
def baseEnd_4180565 : Nat := 1431092834909027502607625

theorem tailTrace_4180565 : CollatzResearch.WordTrace tailWord_4180565 prefixEnd_4180565 1431092834909027502607625 := by
  unfold tailWord_4180565
  simp only [CollatzResearch.WordTrace]
  refine ⟨152477732099534463503967149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101651821399689642335978099 152477732099534463503967149)
  ·
    refine ⟨57179149537325423813987681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152477732099534463503967149 57179149537325423813987681)
    ·
      refine ⟨42884362152994067860490761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57179149537325423813987681 42884362152994067860490761)
      ·
        refine ⟨32163271614745550895368071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42884362152994067860490761 32163271614745550895368071)
        ·
          refine ⟨48244907422118326343052107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32163271614745550895368071 48244907422118326343052107)
          ·
            refine ⟨72367361133177489514578161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48244907422118326343052107 72367361133177489514578161)
            ·
              refine ⟨54275520849883117135933621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72367361133177489514578161 54275520849883117135933621)
              ·
                refine ⟨5088330079676542231493777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54275520849883117135933621 5088330079676542231493777)
                ·
                  refine ⟨3816247559757406673620333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5088330079676542231493777 3816247559757406673620333)
                  ·
                    refine ⟨1431092834909027502607625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3816247559757406673620333 1431092834909027502607625)
                    ·
                      rfl

theorem cell22_4180565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_4180565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180565 prefixEnd_4180565 := by exact prefixLift 4180565
  have htrace : WordTrace (prefixWord ++ tailWord_4180565) baseStart_4180565 baseEnd_4180565 := by
    simpa [prefixWord, tailWord_4180565, baseEnd_4180565] using wordTrace_append hprefix tailTrace_4180565
  have hstable : (prefixWord ++ tailWord_4180565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180565).length < 2 ^ (prefixWord ++ tailWord_4180565).sum := by decide
  have hdescent : baseEnd_4180565 < baseStart_4180565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180584 : List Nat := [2, 1, 4, 3, 2, 2, 1, 3, 4]
def baseStart_4180584 : Nat := 118140960795 + 4180584 * 2 ^ 59
def prefixEnd_4180584 : Nat := 4983230072969 + 3 ^ 40 * 4180584 * 2
def baseEnd_4180584 : Nat := 477033112999105928794189

theorem tailTrace_4180584 : CollatzResearch.WordTrace tailWord_4180584 prefixEnd_4180584 477033112999105928794189 := by
  unfold tailWord_4180584
  simp only [CollatzResearch.WordTrace]
  refine ⟨76239212543232814874454403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101652283390977086499272537 76239212543232814874454403)
  ·
    refine ⟨114358818814849222311681605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76239212543232814874454403 114358818814849222311681605)
    ·
      refine ⟨21442278527784229183440301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114358818814849222311681605 21442278527784229183440301)
      ·
        refine ⟨8040854447919085943790113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21442278527784229183440301 8040854447919085943790113)
        ·
          refine ⟨6030640835939314457842585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8040854447919085943790113 6030640835939314457842585)
          ·
            refine ⟨4522980626954485843381939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6030640835939314457842585 4522980626954485843381939)
            ·
              refine ⟨6784470940431728765072909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4522980626954485843381939 6784470940431728765072909)
              ·
                refine ⟨2544176602661898286902341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6784470940431728765072909 2544176602661898286902341)
                ·
                  refine ⟨477033112999105928794189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2544176602661898286902341 477033112999105928794189)
                  ·
                    rfl

theorem cell22_4180584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 4].length) (baseStart_4180584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180584 prefixEnd_4180584 := by exact prefixLift 4180584
  have htrace : WordTrace (prefixWord ++ tailWord_4180584) baseStart_4180584 baseEnd_4180584 := by
    simpa [prefixWord, tailWord_4180584, baseEnd_4180584] using wordTrace_append hprefix tailTrace_4180584
  have hstable : (prefixWord ++ tailWord_4180584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180584).length < 2 ^ (prefixWord ++ tailWord_4180584).sum := by decide
  have hdescent : baseEnd_4180584 < baseStart_4180584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180597 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 2, 4]
def baseStart_4180597 : Nat := 118140960795 + 4180597 * 2 ^ 59
def prefixEnd_4180597 : Nat := 4983230072969 + 3 ^ 40 * 4180597 * 2
def baseEnd_4180597 : Nat := 1431103789162990085807527

theorem tailTrace_4180597 : CollatzResearch.WordTrace tailWord_4180597 prefixEnd_4180597 1431103789162990085807527 := by
  unfold tailWord_4180597
  simp only [CollatzResearch.WordTrace]
  refine ⟨152478899235418532969132045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101652599490279021979421363 152478899235418532969132045)
  ·
    refine ⟨57179587213281949863424517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152478899235418532969132045 57179587213281949863424517)
    ·
      refine ⟨10721172602490365599392097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57179587213281949863424517 10721172602490365599392097)
      ·
        refine ⟨8040879451867774199544073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10721172602490365599392097 8040879451867774199544073)
        ·
          refine ⟨6030659588900830649658055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8040879451867774199544073 6030659588900830649658055)
          ·
            refine ⟨9045989383351245974487083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6030659588900830649658055 9045989383351245974487083)
            ·
              refine ⟨13568984075026868961730625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9045989383351245974487083 13568984075026868961730625)
              ·
                refine ⟨10176738056270151721297969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13568984075026868961730625 10176738056270151721297969)
                ·
                  refine ⟨7632553542202613790973477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10176738056270151721297969 7632553542202613790973477)
                  ·
                    refine ⟨1431103789162990085807527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7632553542202613790973477 1431103789162990085807527)
                    ·
                      rfl

theorem cell22_4180597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_4180597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180597 prefixEnd_4180597 := by exact prefixLift 4180597
  have htrace : WordTrace (prefixWord ++ tailWord_4180597) baseStart_4180597 baseEnd_4180597 := by
    simpa [prefixWord, tailWord_4180597, baseEnd_4180597] using wordTrace_append hprefix tailTrace_4180597
  have hstable : (prefixWord ++ tailWord_4180597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180597).length < 2 ^ (prefixWord ++ tailWord_4180597).sum := by decide
  have hdescent : baseEnd_4180597 < baseStart_4180597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180623 : List Nat := [1, 1, 2, 1, 1, 1, 1, 9, 5]
def baseStart_4180623 : Nat := 118140960795 + 4180623 * 2 ^ 59
def prefixEnd_4180623 : Nat := 4983230072969 + 3 ^ 40 * 4180623 * 2
def baseEnd_4180623 : Nat := 477037563164778228219149

theorem tailTrace_4180623 : CollatzResearch.WordTrace tailWord_4180623 prefixEnd_4180623 477037563164778228219149 := by
  unfold tailWord_4180623
  simp only [CollatzResearch.WordTrace]
  refine ⟨152479847533324339409578523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101653231688882892939719015 152479847533324339409578523)
  ·
    refine ⟨228719771299986509114367785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152479847533324339409578523 228719771299986509114367785)
    ·
      refine ⟨171539828474989881835775839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228719771299986509114367785 171539828474989881835775839)
      ·
        refine ⟨257309742712484822753663759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171539828474989881835775839 257309742712484822753663759)
        ·
          refine ⟨385964614068727234130495639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257309742712484822753663759 385964614068727234130495639)
          ·
            refine ⟨578946921103090851195743459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385964614068727234130495639 578946921103090851195743459)
            ·
              refine ⟨868420381654636276793615189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578946921103090851195743459 868420381654636276793615189)
              ·
                refine ⟨5088400673757634434337589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 868420381654636276793615189 5088400673757634434337589)
                ·
                  refine ⟨477037563164778228219149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5088400673757634434337589 477037563164778228219149)
                  ·
                    rfl

theorem cell22_4180623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 5].length) (baseStart_4180623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180623 prefixEnd_4180623 := by exact prefixLift 4180623
  have htrace : WordTrace (prefixWord ++ tailWord_4180623) baseStart_4180623 baseEnd_4180623 := by
    simpa [prefixWord, tailWord_4180623, baseEnd_4180623] using wordTrace_append hprefix tailTrace_4180623
  have hstable : (prefixWord ++ tailWord_4180623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180623).length < 2 ^ (prefixWord ++ tailWord_4180623).sum := by decide
  have hdescent : baseEnd_4180623 < baseStart_4180623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180661 : List Nat := [1, 3, 3, 3, 1, 1, 4, 2, 1, 3]
def baseStart_4180661 : Nat := 118140960795 + 4180661 * 2 ^ 59
def prefixEnd_4180661 : Nat := 4983230072969 + 3 ^ 40 * 4180661 * 2
def baseEnd_4180661 : Nat := 1431125697670915252207331

theorem tailTrace_4180661 : CollatzResearch.WordTrace tailWord_4180661 prefixEnd_4180661 1431125697670915252207331 := by
  unfold tailWord_4180661
  simp only [CollatzResearch.WordTrace]
  refine ⟨152481233507186671899461837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101654155671457781266307891 152481233507186671899461837)
  ·
    refine ⟨57180462565195001962298189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152481233507186671899461837 57180462565195001962298189)
    ·
      refine ⟨21442673461948125735861821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57180462565195001962298189 21442673461948125735861821)
      ·
        refine ⟨8041002548230547150948183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21442673461948125735861821 8041002548230547150948183)
        ·
          refine ⟨12061503822345820726422275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8041002548230547150948183 12061503822345820726422275)
          ·
            refine ⟨18092255733518731089633413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12061503822345820726422275 18092255733518731089633413)
            ·
              refine ⟨3392297950034762079306265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18092255733518731089633413 3392297950034762079306265)
              ·
                refine ⟨2544223462526071559479699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3392297950034762079306265 2544223462526071559479699)
                ·
                  refine ⟨3816335193789107339219549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544223462526071559479699 3816335193789107339219549)
                  ·
                    refine ⟨1431125697670915252207331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3816335193789107339219549 1431125697670915252207331)
                    ·
                      rfl

theorem cell22_4180661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_4180661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180661 prefixEnd_4180661 := by exact prefixLift 4180661
  have htrace : WordTrace (prefixWord ++ tailWord_4180661) baseStart_4180661 baseEnd_4180661 := by
    simpa [prefixWord, tailWord_4180661, baseEnd_4180661] using wordTrace_append hprefix tailTrace_4180661
  have hstable : (prefixWord ++ tailWord_4180661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180661).length < 2 ^ (prefixWord ++ tailWord_4180661).sum := by decide
  have hdescent : baseEnd_4180661 < baseStart_4180661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180670 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_4180670 : Nat := 118140960795 + 4180670 * 2 ^ 59
def prefixEnd_4180670 : Nat := 4983230072969 + 3 ^ 40 * 4180670 * 2
def baseEnd_4180670 : Nat := 1431128778554842228732303

theorem tailTrace_4180670 : CollatzResearch.WordTrace tailWord_4180670 prefixEnd_4180670 1431128778554842228732303 := by
  unfold tailWord_4180670
  simp only [CollatzResearch.WordTrace]
  refine ⟨19060195220519258304567433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101654374509436044291026309 19060195220519258304567433)
  ·
    refine ⟨14295146415389443728425575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19060195220519258304567433 14295146415389443728425575)
    ·
      refine ⟨21442719623084165592638363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14295146415389443728425575 21442719623084165592638363)
      ·
        refine ⟨32164079434626248388957545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21442719623084165592638363 32164079434626248388957545)
        ·
          refine ⟨24123059575969686291718159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32164079434626248388957545 24123059575969686291718159)
          ·
            refine ⟨36184589363954529437577239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24123059575969686291718159 36184589363954529437577239)
            ·
              refine ⟨54276884045931794156365859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36184589363954529437577239 54276884045931794156365859)
              ·
                refine ⟨81415326068897691234548789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54276884045931794156365859 81415326068897691234548789)
                ·
                  refine ⟨7632686818959158553238949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81415326068897691234548789 7632686818959158553238949)
                  ·
                    refine ⟨1431128778554842228732303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7632686818959158553238949 1431128778554842228732303)
                    ·
                      rfl

theorem cell22_4180670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_4180670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180670 prefixEnd_4180670 := by exact prefixLift 4180670
  have htrace : WordTrace (prefixWord ++ tailWord_4180670) baseStart_4180670 baseEnd_4180670 := by
    simpa [prefixWord, tailWord_4180670, baseEnd_4180670] using wordTrace_append hprefix tailTrace_4180670
  have hstable : (prefixWord ++ tailWord_4180670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180670).length < 2 ^ (prefixWord ++ tailWord_4180670).sum := by decide
  have hdescent : baseEnd_4180670 < baseStart_4180670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180717 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_4180717 : Nat := 118140960795 + 4180717 * 2 ^ 59
def prefixEnd_4180717 : Nat := 4983230072969 + 3 ^ 40 * 4180717 * 2
def baseEnd_4180717 : Nat := 1431144867615349772807159

theorem tailTrace_4180717 : CollatzResearch.WordTrace tailWord_4180717 prefixEnd_4180717 1431144867615349772807159 := by
  unfold tailWord_4180717
  simp only [CollatzResearch.WordTrace]
  refine ⟨152483275994983793463500405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101655517329989195642333603 152483275994983793463500405)
  ·
    refine ⟨14295307124529730637203163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152483275994983793463500405 14295307124529730637203163)
    ·
      refine ⟨21442960686794595955804745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14295307124529730637203163 21442960686794595955804745)
      ·
        refine ⟨16082220515095946966853559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21442960686794595955804745 16082220515095946966853559)
        ·
          refine ⟨24123330772643920450280339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16082220515095946966853559 24123330772643920450280339)
          ·
            refine ⟨36184996158965880675420509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24123330772643920450280339 36184996158965880675420509)
            ·
              refine ⟨13569373559612205253282691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36184996158965880675420509 13569373559612205253282691)
              ·
                refine ⟨20354060339418307879924037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13569373559612205253282691 20354060339418307879924037)
                ·
                  refine ⟨3816386313640932727485757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20354060339418307879924037 3816386313640932727485757)
                  ·
                    refine ⟨1431144867615349772807159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3816386313640932727485757 1431144867615349772807159)
                    ·
                      rfl

theorem cell22_4180717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_4180717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180717 prefixEnd_4180717 := by exact prefixLift 4180717
  have htrace : WordTrace (prefixWord ++ tailWord_4180717) baseStart_4180717 baseEnd_4180717 := by
    simpa [prefixWord, tailWord_4180717, baseEnd_4180717] using wordTrace_append hprefix tailTrace_4180717
  have hstable : (prefixWord ++ tailWord_4180717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180717).length < 2 ^ (prefixWord ++ tailWord_4180717).sum := by decide
  have hdescent : baseEnd_4180717 < baseStart_4180717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180734 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_4180734 : Nat := 118140960795 + 4180734 * 2 ^ 59
def prefixEnd_4180734 : Nat := 4983230072969 + 3 ^ 40 * 4180734 * 2
def baseEnd_4180734 : Nat := 1431150687062767395132107

theorem tailTrace_4180734 : CollatzResearch.WordTrace tailWord_4180734 prefixEnd_4180734 1431150687062767395132107 := by
  unfold tailWord_4180734
  simp only [CollatzResearch.WordTrace]
  refine ⟨19060487004490275670858657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101655930690614803577912837 19060487004490275670858657)
  ·
    refine ⟨14295365253367706753143993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19060487004490275670858657 14295365253367706753143993)
    ·
      refine ⟨10721523940025780064857995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14295365253367706753143993 10721523940025780064857995)
      ·
        refine ⟨16082285910038670097286993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10721523940025780064857995 16082285910038670097286993)
        ·
          refine ⟨12061714432529002572965245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16082285910038670097286993 12061714432529002572965245)
          ·
            refine ⟨4523142912198375964861967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12061714432529002572965245 4523142912198375964861967)
            ·
              refine ⟨6784714368297563947292951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523142912198375964861967 6784714368297563947292951)
              ·
                refine ⟨10177071552446345920939427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6784714368297563947292951 10177071552446345920939427)
                ·
                  refine ⟨15265607328669518881409141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10177071552446345920939427 15265607328669518881409141)
                  ·
                    refine ⟨1431150687062767395132107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15265607328669518881409141 1431150687062767395132107)
                    ·
                      rfl

theorem cell22_4180734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_4180734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180734 prefixEnd_4180734 := by exact prefixLift 4180734
  have htrace : WordTrace (prefixWord ++ tailWord_4180734) baseStart_4180734 baseEnd_4180734 := by
    simpa [prefixWord, tailWord_4180734, baseEnd_4180734] using wordTrace_append hprefix tailTrace_4180734
  have hstable : (prefixWord ++ tailWord_4180734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180734).length < 2 ^ (prefixWord ++ tailWord_4180734).sum := by decide
  have hdescent : baseEnd_4180734 < baseStart_4180734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180854 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_4180854 : Nat := 118140960795 + 4180854 * 2 ^ 59
def prefixEnd_4180854 : Nat := 4983230072969 + 3 ^ 40 * 4180854 * 2
def baseEnd_4180854 : Nat := 477063921838375694043913

theorem tailTrace_4180854 : CollatzResearch.WordTrace tailWord_4180854 prefixEnd_4180854 477063921838375694043913 := by
  unfold tailWord_4180854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9530517049717966616327351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101658848530324977240825077 9530517049717966616327351)
  ·
    refine ⟨14295775574576949924491027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9530517049717966616327351 14295775574576949924491027)
    ·
      refine ⟨21443663361865424886736541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14295775574576949924491027 21443663361865424886736541)
      ·
        refine ⟨8041373760699534332526203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21443663361865424886736541 8041373760699534332526203)
        ·
          refine ⟨12062060641049301498789305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8041373760699534332526203 12062060641049301498789305)
          ·
            refine ⟨9046545480786976124091979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12062060641049301498789305 9046545480786976124091979)
            ·
              refine ⟨13569818221180464186137969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046545480786976124091979 13569818221180464186137969)
              ·
                refine ⟨10177363665885348139603477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13569818221180464186137969 10177363665885348139603477)
                ·
                  refine ⟨477063921838375694043913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10177363665885348139603477 477063921838375694043913)
                  ·
                    rfl

theorem cell22_4180854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_4180854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180854 prefixEnd_4180854 := by exact prefixLift 4180854
  have htrace : WordTrace (prefixWord ++ tailWord_4180854) baseStart_4180854 baseEnd_4180854 := by
    simpa [prefixWord, tailWord_4180854, baseEnd_4180854] using wordTrace_append hprefix tailTrace_4180854
  have hstable : (prefixWord ++ tailWord_4180854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180854).length < 2 ^ (prefixWord ++ tailWord_4180854).sum := by decide
  have hdescent : baseEnd_4180854 < baseStart_4180854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180903 : List Nat := [1, 1, 6, 1, 3, 1, 3, 1, 2, 3]
def baseStart_4180903 : Nat := 118140960795 + 4180903 * 2 ^ 59
def prefixEnd_4180903 : Nat := 4983230072969 + 3 ^ 40 * 4180903 * 2
def baseEnd_4180903 : Nat := 1431208539216507287656589

theorem tailTrace_4180903 : CollatzResearch.WordTrace tailWord_4180903 prefixEnd_4180903 1431208539216507287656589 := by
  unfold tailWord_4180903
  simp only [CollatzResearch.WordTrace]
  refine ⟨152490059972309947229771363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101660039981539964819847575 152490059972309947229771363)
  ·
    refine ⟨228735089958464920844657045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152490059972309947229771363 228735089958464920844657045)
    ·
      refine ⟨10721957341803043164593299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 228735089958464920844657045 10721957341803043164593299)
      ·
        refine ⟨16082936012704564746889949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10721957341803043164593299 16082936012704564746889949)
        ·
          refine ⟨6031101004764211780083731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16082936012704564746889949 6031101004764211780083731)
          ·
            refine ⟨9046651507146317670125597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6031101004764211780083731 9046651507146317670125597)
            ·
              refine ⟨3392494315179869126297099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9046651507146317670125597 3392494315179869126297099)
              ·
                refine ⟨5088741472769803689445649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3392494315179869126297099 5088741472769803689445649)
                ·
                  refine ⟨3816556104577352767084237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5088741472769803689445649 3816556104577352767084237)
                  ·
                    refine ⟨1431208539216507287656589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3816556104577352767084237 1431208539216507287656589)
                    ·
                      rfl

theorem cell22_4180903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_4180903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180903 prefixEnd_4180903 := by exact prefixLift 4180903
  have htrace : WordTrace (prefixWord ++ tailWord_4180903) baseStart_4180903 baseEnd_4180903 := by
    simpa [prefixWord, tailWord_4180903, baseEnd_4180903] using wordTrace_append hprefix tailTrace_4180903
  have hstable : (prefixWord ++ tailWord_4180903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180903).length < 2 ^ (prefixWord ++ tailWord_4180903).sum := by decide
  have hdescent : baseEnd_4180903 < baseStart_4180903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180916 : List Nat := [2, 5, 2, 1, 1, 1, 4, 6]
def baseStart_4180916 : Nat := 118140960795 + 4180916 * 2 ^ 59
def prefixEnd_4180916 : Nat := 4983230072969 + 3 ^ 40 * 4180916 * 2
def baseEnd_4180916 : Nat := 159023665486908843009061

theorem tailTrace_4180916 : CollatzResearch.WordTrace tailWord_4180916 prefixEnd_4180916 159023665486908843009061 := by
  unfold tailWord_4180916
  simp only [CollatzResearch.WordTrace]
  refine ⟨76245267060631425224997301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101660356080841900299996401 76245267060631425224997301)
  ·
    refine ⟨7147993786934196114843497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76245267060631425224997301 7147993786934196114843497)
    ·
      refine ⟨5360995340200647086132623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7147993786934196114843497 5360995340200647086132623)
      ·
        refine ⟨8041493010300970629198935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5360995340200647086132623 8041493010300970629198935)
        ·
          refine ⟨12062239515451455943798403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8041493010300970629198935 12062239515451455943798403)
          ·
            refine ⟨18093359273177183915697605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12062239515451455943798403 18093359273177183915697605)
            ·
              refine ⟨3392504863720721984193301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18093359273177183915697605 3392504863720721984193301)
              ·
                refine ⟨159023665486908843009061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3392504863720721984193301 159023665486908843009061)
                ·
                  rfl

theorem cell22_4180916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 6].length) (baseStart_4180916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180916 prefixEnd_4180916 := by exact prefixLift 4180916
  have htrace : WordTrace (prefixWord ++ tailWord_4180916) baseStart_4180916 baseEnd_4180916 := by
    simpa [prefixWord, tailWord_4180916, baseEnd_4180916] using wordTrace_append hprefix tailTrace_4180916
  have hstable : (prefixWord ++ tailWord_4180916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180916).length < 2 ^ (prefixWord ++ tailWord_4180916).sum := by decide
  have hdescent : baseEnd_4180916 < baseStart_4180916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4180989 : List Nat := [1, 4, 1, 1, 1, 2, 1, 7, 4]
def baseStart_4180989 : Nat := 118140960795 + 4180989 * 2 ^ 59
def prefixEnd_4180989 : Nat := 4983230072969 + 3 ^ 40 * 4180989 * 2
def baseEnd_4180989 : Nat := 477079326258010576668775

theorem tailTrace_4180989 : CollatzResearch.WordTrace tailWord_4180989 prefixEnd_4180989 477079326258010576668775 := by
  unfold tailWord_4180989
  simp only [CollatzResearch.WordTrace]
  refine ⟨152493196649998383917402021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101662131099998922611601347 152493196649998383917402021)
  ·
    refine ⟨28592474371874696984512879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152493196649998383917402021 28592474371874696984512879)
    ·
      refine ⟨42888711557812045476769319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28592474371874696984512879 42888711557812045476769319)
      ·
        refine ⟨64333067336718068215153979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42888711557812045476769319 64333067336718068215153979)
        ·
          refine ⟨96499601005077102322730969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64333067336718068215153979 96499601005077102322730969)
          ·
            refine ⟨72374700753807826742048227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96499601005077102322730969 72374700753807826742048227)
            ·
              refine ⟨108562051130711740113072341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72374700753807826742048227 108562051130711740113072341)
              ·
                refine ⟨2544423073376056408900133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108562051130711740113072341 2544423073376056408900133)
                ·
                  refine ⟨477079326258010576668775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2544423073376056408900133 477079326258010576668775)
                  ·
                    rfl

theorem cell22_4180989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_4180989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4180989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4180989 prefixEnd_4180989 := by exact prefixLift 4180989
  have htrace : WordTrace (prefixWord ++ tailWord_4180989) baseStart_4180989 baseEnd_4180989 := by
    simpa [prefixWord, tailWord_4180989, baseEnd_4180989] using wordTrace_append hprefix tailTrace_4180989
  have hstable : (prefixWord ++ tailWord_4180989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4180989).length < 2 ^ (prefixWord ++ tailWord_4180989).sum := by decide
  have hdescent : baseEnd_4180989 < baseStart_4180989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4180989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181006 : List Nat := [4, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_4181006 : Nat := 118140960795 + 4181006 * 2 ^ 59
def prefixEnd_4181006 : Nat := 4983230072969 + 3 ^ 40 * 4181006 * 2
def baseEnd_4181006 : Nat := 477081266073816450777091

theorem tailTrace_4181006 : CollatzResearch.WordTrace tailWord_4181006 prefixEnd_4181006 477081266073816450777091 := by
  unfold tailWord_4181006
  simp only [CollatzResearch.WordTrace]
  refine ⟨19061727086367099477596359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101662544460624530547180581 19061727086367099477596359)
  ·
    refine ⟨28592590629550649216394539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19061727086367099477596359 28592590629550649216394539)
    ·
      refine ⟨42888885944325973824591809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28592590629550649216394539 42888885944325973824591809)
      ·
        refine ⟨32166664458244480368443857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42888885944325973824591809 32166664458244480368443857)
        ·
          refine ⟨24124998343683360276332893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32166664458244480368443857 24124998343683360276332893)
          ·
            refine ⟨9046874378881260103624835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24124998343683360276332893 9046874378881260103624835)
            ·
              refine ⟨13570311568321890155437253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9046874378881260103624835 13570311568321890155437253)
              ·
                refine ⟨2544433419060354404144485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13570311568321890155437253 2544433419060354404144485)
                ·
                  refine ⟨477081266073816450777091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2544433419060354404144485 477081266073816450777091)
                  ·
                    rfl

theorem cell22_4181006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_4181006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181006 prefixEnd_4181006 := by exact prefixLift 4181006
  have htrace : WordTrace (prefixWord ++ tailWord_4181006) baseStart_4181006 baseEnd_4181006 := by
    simpa [prefixWord, tailWord_4181006, baseEnd_4181006] using wordTrace_append hprefix tailTrace_4181006
  have hstable : (prefixWord ++ tailWord_4181006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181006).length < 2 ^ (prefixWord ++ tailWord_4181006).sum := by decide
  have hdescent : baseEnd_4181006 < baseStart_4181006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181017 : List Nat := [1, 2, 1, 2, 1, 1, 7, 7]
def baseStart_4181017 : Nat := 118140960795 + 4181017 * 2 ^ 59
def prefixEnd_4181017 : Nat := 4983230072969 + 3 ^ 40 * 4181017 * 2
def baseEnd_4181017 : Nat := 159027507082916554478471

theorem tailTrace_4181017 : CollatzResearch.WordTrace tailWord_4181017 prefixEnd_4181017 159027507082916554478471 := by
  unfold tailWord_4181017
  simp only [CollatzResearch.WordTrace]
  refine ⟨152494217893896944699421305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101662811929264629799614203 152494217893896944699421305)
  ·
    refine ⟨114370663420422708524565979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152494217893896944699421305 114370663420422708524565979)
    ·
      refine ⟨171555995130634062786848969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114370663420422708524565979 171555995130634062786848969)
      ·
        refine ⟨128666996347975547090136727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171555995130634062786848969 128666996347975547090136727)
        ·
          refine ⟨193000494521963320635205091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128666996347975547090136727 193000494521963320635205091)
          ·
            refine ⟨289500741782944980952807637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193000494521963320635205091 289500741782944980952807637)
            ·
              refine ⟨6785173635537772991081429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 289500741782944980952807637 6785173635537772991081429)
              ·
                refine ⟨159027507082916554478471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6785173635537772991081429 159027507082916554478471)
                ·
                  rfl

theorem cell22_4181017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 7].length) (baseStart_4181017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181017 prefixEnd_4181017 := by exact prefixLift 4181017
  have htrace : WordTrace (prefixWord ++ tailWord_4181017) baseStart_4181017 baseEnd_4181017 := by
    simpa [prefixWord, tailWord_4181017, baseEnd_4181017] using wordTrace_append hprefix tailTrace_4181017
  have hstable : (prefixWord ++ tailWord_4181017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181017).length < 2 ^ (prefixWord ++ tailWord_4181017).sum := by decide
  have hdescent : baseEnd_4181017 < baseStart_4181017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181021 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_4181021 : Nat := 118140960795 + 4181021 * 2 ^ 59
def prefixEnd_4181021 : Nat := 4983230072969 + 3 ^ 40 * 4181021 * 2
def baseEnd_4181021 : Nat := 1431248933027994313206227

theorem tailTrace_4181021 : CollatzResearch.WordTrace tailWord_4181021 prefixEnd_4181021 1431248933027994313206227 := by
  unfold tailWord_4181021
  simp only [CollatzResearch.WordTrace]
  refine ⟨152494363785882453382566917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101662909190588302255044611 152494363785882453382566917)
  ·
    refine ⟨28592693209852960009231297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152494363785882453382566917 28592693209852960009231297)
    ·
      refine ⟨21444519907389720006923473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28592693209852960009231297 21444519907389720006923473)
      ·
        refine ⟨16083389930542290005192605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21444519907389720006923473 16083389930542290005192605)
        ·
          refine ⟨6031271223953358751947227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16083389930542290005192605 6031271223953358751947227)
          ·
            refine ⟨9046906835930038127920841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6031271223953358751947227 9046906835930038127920841)
            ·
              refine ⟨6785180126947528595940631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9046906835930038127920841 6785180126947528595940631)
              ·
                refine ⟨10177770190421292893910947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6785180126947528595940631 10177770190421292893910947)
                ·
                  refine ⟨15266655285631939340866421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10177770190421292893910947 15266655285631939340866421)
                  ·
                    refine ⟨1431248933027994313206227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15266655285631939340866421 1431248933027994313206227)
                    ·
                      rfl

theorem cell22_4181021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_4181021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181021 prefixEnd_4181021 := by exact prefixLift 4181021
  have htrace : WordTrace (prefixWord ++ tailWord_4181021) baseStart_4181021 baseEnd_4181021 := by
    simpa [prefixWord, tailWord_4181021, baseEnd_4181021] using wordTrace_append hprefix tailTrace_4181021
  have hstable : (prefixWord ++ tailWord_4181021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181021).length < 2 ^ (prefixWord ++ tailWord_4181021).sum := by decide
  have hdescent : baseEnd_4181021 < baseStart_4181021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181085 : List Nat := [1, 4, 4, 1, 3, 1, 2, 6]
def baseStart_4181085 : Nat := 118140960795 + 4181085 * 2 ^ 59
def prefixEnd_4181085 : Nat := 4983230072969 + 3 ^ 40 * 4181085 * 2
def baseEnd_4181085 : Nat := 159030093503991053289559

theorem tailTrace_4181085 : CollatzResearch.WordTrace tailWord_4181085 prefixEnd_4181085 159030093503991053289559 := by
  unfold tailWord_4181085
  simp only [CollatzResearch.WordTrace]
  refine ⟨152496698057650592312896709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101664465371767061541931139 152496698057650592312896709)
  ·
    refine ⟨28593130885809486058668133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152496698057650592312896709 28593130885809486058668133)
    ·
      refine ⟨5361212041089278636000275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28593130885809486058668133 5361212041089278636000275)
      ·
        refine ⟨8041818061633917954000413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361212041089278636000275 8041818061633917954000413)
        ·
          refine ⟨3015681773112719232750155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8041818061633917954000413 3015681773112719232750155)
          ·
            refine ⟨4523522659669078849125233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015681773112719232750155 4523522659669078849125233)
            ·
              refine ⟨3392641994751809136843925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4523522659669078849125233 3392641994751809136843925)
              ·
                refine ⟨159030093503991053289559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3392641994751809136843925 159030093503991053289559)
                ·
                  rfl

theorem cell22_4181085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 6].length) (baseStart_4181085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181085 prefixEnd_4181085 := by exact prefixLift 4181085
  have htrace : WordTrace (prefixWord ++ tailWord_4181085) baseStart_4181085 baseEnd_4181085 := by
    simpa [prefixWord, tailWord_4181085, baseEnd_4181085] using wordTrace_append hprefix tailTrace_4181085
  have hstable : (prefixWord ++ tailWord_4181085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181085).length < 2 ^ (prefixWord ++ tailWord_4181085).sum := by decide
  have hdescent : baseEnd_4181085 < baseStart_4181085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181143 : List Nat := [1, 1, 3, 3, 3, 3, 1, 2, 1, 4]
def baseStart_4181143 : Nat := 118140960795 + 4181143 * 2 ^ 59
def prefixEnd_4181143 : Nat := 4983230072969 + 3 ^ 40 * 4181143 * 2
def baseEnd_4181143 : Nat := 1431290696121226661655853

theorem tailTrace_4181143 : CollatzResearch.WordTrace tailWord_4181143 prefixEnd_4181143 1431290696121226661655853 := by
  unfold tailWord_4181143
  simp only [CollatzResearch.WordTrace]
  refine ⟨152498813491440468218508083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101665875660960312145672055 152498813491440468218508083)
  ·
    refine ⟨228748220237160702327762125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152498813491440468218508083 228748220237160702327762125)
    ·
      refine ⟨85780582588935263372910797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228748220237160702327762125 85780582588935263372910797)
      ·
        refine ⟨32167718470850723764841549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85780582588935263372910797 32167718470850723764841549)
        ·
          refine ⟨12062894426569021411815581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32167718470850723764841549 12062894426569021411815581)
          ·
            refine ⟨4523585409963383029430843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12062894426569021411815581 4523585409963383029430843)
            ·
              refine ⟨6785378114945074544146265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523585409963383029430843 6785378114945074544146265)
              ·
                refine ⟨5089033586208805908109699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6785378114945074544146265 5089033586208805908109699)
                ·
                  refine ⟨7633550379313208862164549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5089033586208805908109699 7633550379313208862164549)
                  ·
                    refine ⟨1431290696121226661655853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7633550379313208862164549 1431290696121226661655853)
                    ·
                      rfl

theorem cell22_4181143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_4181143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181143 prefixEnd_4181143 := by exact prefixLift 4181143
  have htrace : WordTrace (prefixWord ++ tailWord_4181143) baseStart_4181143 baseEnd_4181143 := by
    simpa [prefixWord, tailWord_4181143, baseEnd_4181143] using wordTrace_append hprefix tailTrace_4181143
  have hstable : (prefixWord ++ tailWord_4181143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181143).length < 2 ^ (prefixWord ++ tailWord_4181143).sum := by decide
  have hdescent : baseEnd_4181143 < baseStart_4181143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181156 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_4181156 : Nat := 118140960795 + 4181156 * 2 ^ 59
def prefixEnd_4181156 : Nat := 4983230072969 + 3 ^ 40 * 4181156 * 2
def baseEnd_4181156 : Nat := 1431295146286898961080813

theorem tailTrace_4181156 : CollatzResearch.WordTrace tailWord_4181156 prefixEnd_4181156 1431295146286898961080813 := by
  unfold tailWord_4181156
  simp only [CollatzResearch.WordTrace]
  refine ⟨76249643820196685719365661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101666191760262247625820881 76249643820196685719365661)
  ·
    refine ⟨28593616432573757144762123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76249643820196685719365661 28593616432573757144762123)
    ·
      refine ⟨42890424648860635717143185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28593616432573757144762123 42890424648860635717143185)
      ·
        refine ⟨32167818486645476787857389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42890424648860635717143185 32167818486645476787857389)
        ·
          refine ⟨12062931932492053795446521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32167818486645476787857389 12062931932492053795446521)
          ·
            refine ⟨9047198949369040346584891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12062931932492053795446521 9047198949369040346584891)
            ·
              refine ⟨13570798424053560519877337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9047198949369040346584891 13570798424053560519877337)
              ·
                refine ⟨10178098818040170389908003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13570798424053560519877337 10178098818040170389908003)
                ·
                  refine ⟨15267148227060255584862005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10178098818040170389908003 15267148227060255584862005)
                  ·
                    refine ⟨1431295146286898961080813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15267148227060255584862005 1431295146286898961080813)
                    ·
                      rfl

theorem cell22_4181156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_4181156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181156 prefixEnd_4181156 := by exact prefixLift 4181156
  have htrace : WordTrace (prefixWord ++ tailWord_4181156) baseStart_4181156 baseEnd_4181156 := by
    simpa [prefixWord, tailWord_4181156, baseEnd_4181156] using wordTrace_append hprefix tailTrace_4181156
  have hstable : (prefixWord ++ tailWord_4181156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181156).length < 2 ^ (prefixWord ++ tailWord_4181156).sum := by decide
  have hdescent : baseEnd_4181156 < baseStart_4181156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181169 : List Nat := [1, 2, 2, 5, 1, 11]
def baseStart_4181169 : Nat := 118140960795 + 4181169 * 2 ^ 59
def prefixEnd_4181169 : Nat := 4983230072969 + 3 ^ 40 * 4181169 * 2
def baseEnd_4181169 : Nat := 17670365388303348895133

theorem tailTrace_4181169 : CollatzResearch.WordTrace tailWord_4181169 prefixEnd_4181169 17670365388303348895133 := by
  unfold tailWord_4181169
  simp only [CollatzResearch.WordTrace]
  refine ⟨152499761789346274658954561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101666507859564183105969707 152499761789346274658954561)
  ·
    refine ⟨114374821342009705994215921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152499761789346274658954561 114374821342009705994215921)
    ·
      refine ⟨85781116006507279495661941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114374821342009705994215921 85781116006507279495661941)
      ·
        refine ⟨8041979625610057452718307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85781116006507279495661941 8041979625610057452718307)
        ·
          refine ⟨12062969438415086179077461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8041979625610057452718307 12062969438415086179077461)
          ·
            refine ⟨17670365388303348895133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 12062969438415086179077461 17670365388303348895133)
            ·
              rfl

theorem cell22_4181169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 11].length) (baseStart_4181169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181169 prefixEnd_4181169 := by exact prefixLift 4181169
  have htrace : WordTrace (prefixWord ++ tailWord_4181169) baseStart_4181169 baseEnd_4181169 := by
    simpa [prefixWord, tailWord_4181169, baseEnd_4181169] using wordTrace_append hprefix tailTrace_4181169
  have hstable : (prefixWord ++ tailWord_4181169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181169).length < 2 ^ (prefixWord ++ tailWord_4181169).sum := by decide
  have hdescent : baseEnd_4181169 < baseStart_4181169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181231 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 7]
def baseStart_4181231 : Nat := 118140960795 + 4181231 * 2 ^ 59
def prefixEnd_4181231 : Nat := 4983230072969 + 3 ^ 40 * 4181231 * 2
def baseEnd_4181231 : Nat := 477106940106541255151861

theorem tailTrace_4181231 : CollatzResearch.WordTrace tailWord_4181231 prefixEnd_4181231 477106940106541255151861 := by
  unfold tailWord_4181231
  simp only [CollatzResearch.WordTrace]
  refine ⟨152502023115121659247711547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101668015410081106165141031 152502023115121659247711547)
  ·
    refine ⟨228753034672682488871567321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152502023115121659247711547 228753034672682488871567321)
    ·
      refine ⟨171564776004511866653675491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228753034672682488871567321 171564776004511866653675491)
      ·
        refine ⟨257347164006767799980513237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171564776004511866653675491 257347164006767799980513237)
        ·
          refine ⟨6031574156408620312043279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 257347164006767799980513237 6031574156408620312043279)
          ·
            refine ⟨9047361234612930468064919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6031574156408620312043279 9047361234612930468064919)
            ·
              refine ⟨13571041851919395702097379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9047361234612930468064919 13571041851919395702097379)
              ·
                refine ⟨20356562777879093553146069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13571041851919395702097379 20356562777879093553146069)
                ·
                  refine ⟨477106940106541255151861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20356562777879093553146069 477106940106541255151861)
                  ·
                    rfl

theorem cell22_4181231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 7].length) (baseStart_4181231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181231 prefixEnd_4181231 := by exact prefixLift 4181231
  have htrace : WordTrace (prefixWord ++ tailWord_4181231) baseStart_4181231 baseEnd_4181231 := by
    simpa [prefixWord, tailWord_4181231, baseEnd_4181231] using wordTrace_append hprefix tailTrace_4181231
  have hstable : (prefixWord ++ tailWord_4181231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181231).length < 2 ^ (prefixWord ++ tailWord_4181231).sum := by decide
  have hdescent : baseEnd_4181231 < baseStart_4181231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181306 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_4181306 : Nat := 118140960795 + 4181306 * 2 ^ 59
def prefixEnd_4181306 : Nat := 4983230072969 + 3 ^ 40 * 4181306 * 2
def baseEnd_4181306 : Nat := 1431346494352348569830353

theorem tailTrace_4181306 : CollatzResearch.WordTrace tailWord_4181306 prefixEnd_4181306 1431346494352348569830353 := by
  unfold tailWord_4181306
  simp only [CollatzResearch.WordTrace]
  refine ⟨38126189647462486764172943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101669839059899964704461181 38126189647462486764172943)
  ·
    refine ⟨57189284471193730146259415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38126189647462486764172943 57189284471193730146259415)
    ·
      refine ⟨85783926706790595219389123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57189284471193730146259415 85783926706790595219389123)
      ·
        refine ⟨128675890060185892829083685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85783926706790595219389123 128675890060185892829083685)
        ·
          refine ⟨24126729386284854905453191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128675890060185892829083685 24126729386284854905453191)
          ·
            refine ⟨36190094079427282358179787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24126729386284854905453191 36190094079427282358179787)
            ·
              refine ⟨54285141119140923537269681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36190094079427282358179787 54285141119140923537269681)
              ·
                refine ⟨40713855839355692652952261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54285141119140923537269681 40713855839355692652952261)
                ·
                  refine ⟨7633847969879192372428549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40713855839355692652952261 7633847969879192372428549)
                  ·
                    refine ⟨1431346494352348569830353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7633847969879192372428549 1431346494352348569830353)
                    ·
                      rfl

theorem cell22_4181306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_4181306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181306 prefixEnd_4181306 := by exact prefixLift 4181306
  have htrace : WordTrace (prefixWord ++ tailWord_4181306) baseStart_4181306 baseEnd_4181306 := by
    simpa [prefixWord, tailWord_4181306, baseEnd_4181306] using wordTrace_append hprefix tailTrace_4181306
  have hstable : (prefixWord ++ tailWord_4181306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181306).length < 2 ^ (prefixWord ++ tailWord_4181306).sum := by decide
  have hdescent : baseEnd_4181306 < baseStart_4181306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181374 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_4181374 : Nat := 118140960795 + 4181374 * 2 ^ 59
def prefixEnd_4181374 : Nat := 4983230072969 + 3 ^ 40 * 4181374 * 2
def baseEnd_4181374 : Nat := 1431369772142019059130145

theorem tailTrace_4181374 : CollatzResearch.WordTrace tailWord_4181374 prefixEnd_4181374 1431369772142019059130145 := by
  unfold tailWord_4181374
  simp only [CollatzResearch.WordTrace]
  refine ⟨19063404844200449333770897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101671492502402396446778117 19063404844200449333770897)
  ·
    refine ⟨14297553633150337000328173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19063404844200449333770897 14297553633150337000328173)
    ·
      refine ⟨5361582612431376375123065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14297553633150337000328173 5361582612431376375123065)
      ·
        refine ⟨4021186959323532281342299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5361582612431376375123065 4021186959323532281342299)
        ·
          refine ⟨6031780438985298422013449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4021186959323532281342299 6031780438985298422013449)
          ·
            refine ⟨4523835329238973816510087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6031780438985298422013449 4523835329238973816510087)
            ·
              refine ⟨6785752993858460724765131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523835329238973816510087 6785752993858460724765131)
              ·
                refine ⟨10178629490787691087147697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6785752993858460724765131 10178629490787691087147697)
                ·
                  refine ⟨7633972118090768315360773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10178629490787691087147697 7633972118090768315360773)
                  ·
                    refine ⟨1431369772142019059130145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7633972118090768315360773 1431369772142019059130145)
                    ·
                      rfl

theorem cell22_4181374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_4181374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181374 prefixEnd_4181374 := by exact prefixLift 4181374
  have htrace : WordTrace (prefixWord ++ tailWord_4181374) baseStart_4181374 baseEnd_4181374 := by
    simpa [prefixWord, tailWord_4181374, baseEnd_4181374] using wordTrace_append hprefix tailTrace_4181374
  have hstable : (prefixWord ++ tailWord_4181374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181374).length < 2 ^ (prefixWord ++ tailWord_4181374).sum := by decide
  have hdescent : baseEnd_4181374 < baseStart_4181374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181443 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 4, 3]
def baseStart_4181443 : Nat := 118140960795 + 4181443 * 2 ^ 59
def prefixEnd_4181443 : Nat := 4983230072969 + 3 ^ 40 * 4181443 * 2
def baseEnd_4181443 : Nat := 1431393392252125879154933

theorem tailTrace_4181443 : CollatzResearch.WordTrace tailWord_4181443 prefixEnd_4181443 1431393392252125879154933 := by
  unfold tailWord_4181443
  simp only [CollatzResearch.WordTrace]
  refine ⟨152509755390353619454428983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101673170260235746302952655 152509755390353619454428983)
  ·
    refine ⟨228764633085530429181643475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152509755390353619454428983 228764633085530429181643475)
    ·
      refine ⟨343146949628295643772465213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228764633085530429181643475 343146949628295643772465213)
      ·
        refine ⟨128680106110610866414674455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343146949628295643772465213 128680106110610866414674455)
        ·
          refine ⟨193020159165916299622011683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128680106110610866414674455 193020159165916299622011683)
          ·
            refine ⟨289530238748874449433017525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193020159165916299622011683 289530238748874449433017525)
            ·
              refine ⟨27143459882706979634345393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289530238748874449433017525 27143459882706979634345393)
              ·
                refine ⟨20357594912030234725759045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27143459882706979634345393 20357594912030234725759045)
                ·
                  refine ⟨3817049046005669011079821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20357594912030234725759045 3817049046005669011079821)
                  ·
                    refine ⟨1431393392252125879154933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817049046005669011079821 1431393392252125879154933)
                    ·
                      rfl

theorem cell22_4181443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 3].length) (baseStart_4181443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181443 prefixEnd_4181443 := by exact prefixLift 4181443
  have htrace : WordTrace (prefixWord ++ tailWord_4181443) baseStart_4181443 baseEnd_4181443 := by
    simpa [prefixWord, tailWord_4181443, baseEnd_4181443] using wordTrace_append hprefix tailTrace_4181443
  have hstable : (prefixWord ++ tailWord_4181443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181443).length < 2 ^ (prefixWord ++ tailWord_4181443).sum := by decide
  have hdescent : baseEnd_4181443 < baseStart_4181443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181462 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_4181462 : Nat := 118140960795 + 4181462 * 2 ^ 59
def prefixEnd_4181462 : Nat := 4983230072969 + 3 ^ 40 * 4181462 * 2
def baseEnd_4181462 : Nat := 477133298780138720976625

theorem tailTrace_4181462 : CollatzResearch.WordTrace tailWord_4181462 prefixEnd_4181462 477133298780138720976625 := by
  unfold tailWord_4181462
  simp only [CollatzResearch.WordTrace]
  refine ⟨9531903023580299106210665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101673632251523190466247093 9531903023580299106210665)
  ·
    refine ⟨7148927267685224329657999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9531903023580299106210665 7148927267685224329657999)
    ·
      refine ⟨10723390901527836494486999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7148927267685224329657999 10723390901527836494486999)
      ·
        refine ⟨16085086352291754741730499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10723390901527836494486999 16085086352291754741730499)
        ·
          refine ⟨24127629528437632112595749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16085086352291754741730499 24127629528437632112595749)
          ·
            refine ⟨4523930536582056021111703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24127629528437632112595749 4523930536582056021111703)
            ·
              refine ⟨6785895804873084031667555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523930536582056021111703 6785895804873084031667555)
              ·
                refine ⟨10178843707309626047501333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6785895804873084031667555 10178843707309626047501333)
                ·
                  refine ⟨477133298780138720976625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10178843707309626047501333 477133298780138720976625)
                  ·
                    rfl

theorem cell22_4181462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_4181462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181462 prefixEnd_4181462 := by exact prefixLift 4181462
  have htrace : WordTrace (prefixWord ++ tailWord_4181462) baseStart_4181462 baseEnd_4181462 := by
    simpa [prefixWord, tailWord_4181462, baseEnd_4181462] using wordTrace_append hprefix tailTrace_4181462
  have hstable : (prefixWord ++ tailWord_4181462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181462).length < 2 ^ (prefixWord ++ tailWord_4181462).sum := by decide
  have hdescent : baseEnd_4181462 < baseStart_4181462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181473 : List Nat := [1, 2, 3, 1, 2, 4, 2, 7]
def baseStart_4181473 : Nat := 118140960795 + 4181473 * 2 ^ 59
def prefixEnd_4181473 : Nat := 4983230072969 + 3 ^ 40 * 4181473 * 2
def baseEnd_4181473 : Nat := 159044851318357311211649

theorem tailTrace_4181473 : CollatzResearch.WordTrace tailWord_4181473 prefixEnd_4181473 159044851318357311211649 := by
  unfold tailWord_4181473
  simp only [CollatzResearch.WordTrace]
  refine ⟨152510849580244934578021073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101673899720163289718680715 152510849580244934578021073)
  ·
    refine ⟨114383137185183700933515805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152510849580244934578021073 114383137185183700933515805)
    ·
      refine ⟨42893676444443887850068427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114383137185183700933515805 42893676444443887850068427)
      ·
        refine ⟨64340514666665831775102641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42893676444443887850068427 64340514666665831775102641)
        ·
          refine ⟨48255385999999373831326981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64340514666665831775102641 48255385999999373831326981)
          ·
            refine ⟨9047884874999882593373809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48255385999999373831326981 9047884874999882593373809)
            ·
              refine ⟨6785913656249911945030357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9047884874999882593373809 6785913656249911945030357)
              ·
                refine ⟨159044851318357311211649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6785913656249911945030357 159044851318357311211649)
                ·
                  rfl

theorem cell22_4181473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 7].length) (baseStart_4181473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181473 prefixEnd_4181473 := by exact prefixLift 4181473
  have htrace : WordTrace (prefixWord ++ tailWord_4181473) baseStart_4181473 baseEnd_4181473 := by
    simpa [prefixWord, tailWord_4181473, baseEnd_4181473] using wordTrace_append hprefix tailTrace_4181473
  have hstable : (prefixWord ++ tailWord_4181473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181473).length < 2 ^ (prefixWord ++ tailWord_4181473).sum := by decide
  have hdescent : baseEnd_4181473 < baseStart_4181473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181477 : List Nat := [1, 3, 1, 5, 1, 2, 1, 3, 2, 3]
def baseStart_4181477 : Nat := 118140960795 + 4181477 * 2 ^ 59
def prefixEnd_4181477 : Nat := 4983230072969 + 3 ^ 40 * 4181477 * 2
def baseEnd_4181477 : Nat := 1431405031146961123804829

theorem tailTrace_4181477 : CollatzResearch.WordTrace tailWord_4181477 prefixEnd_4181477 1431405031146961123804829 := by
  unfold tailWord_4181477
  simp only [CollatzResearch.WordTrace]
  refine ⟨152510995472230443261166685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101673996981486962174111123 152510995472230443261166685)
  ·
    refine ⟨57191623302086416222937507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152510995472230443261166685 57191623302086416222937507)
    ·
      refine ⟨85787434953129624334406261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57191623302086416222937507 85787434953129624334406261)
      ·
        refine ⟨8042572026855902281350587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85787434953129624334406261 8042572026855902281350587)
        ·
          refine ⟨12063858040283853422025881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8042572026855902281350587 12063858040283853422025881)
          ·
            refine ⟨9047893530212890066519411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12063858040283853422025881 9047893530212890066519411)
            ·
              refine ⟨13571840295319335099779117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9047893530212890066519411 13571840295319335099779117)
              ·
                refine ⟨5089440110744750662417169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13571840295319335099779117 5089440110744750662417169)
                ·
                  refine ⟨3817080083058562996812877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5089440110744750662417169 3817080083058562996812877)
                  ·
                    refine ⟨1431405031146961123804829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817080083058562996812877 1431405031146961123804829)
                    ·
                      rfl

theorem cell22_4181477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_4181477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181477 prefixEnd_4181477 := by exact prefixLift 4181477
  have htrace : WordTrace (prefixWord ++ tailWord_4181477) baseStart_4181477 baseEnd_4181477 := by
    simpa [prefixWord, tailWord_4181477, baseEnd_4181477] using wordTrace_append hprefix tailTrace_4181477
  have hstable : (prefixWord ++ tailWord_4181477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181477).length < 2 ^ (prefixWord ++ tailWord_4181477).sum := by decide
  have hdescent : baseEnd_4181477 < baseStart_4181477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181524 : List Nat := [2, 4, 3, 1, 3, 1, 1, 7]
def baseStart_4181524 : Nat := 118140960795 + 4181524 * 2 ^ 59
def prefixEnd_4181524 : Nat := 4983230072969 + 3 ^ 40 * 4181524 * 2
def baseEnd_4181524 : Nat := 159046791134163185319965

theorem tailTrace_4181524 : CollatzResearch.WordTrace tailWord_4181524 prefixEnd_4181524 159046791134163185319965 := by
  unfold tailWord_4181524
  simp only [CollatzResearch.WordTrace]
  refine ⟨76256354851530085144063813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101675139802040113525418417 76256354851530085144063813)
  ·
    refine ⟨14298066534661890964511965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76256354851530085144063813 14298066534661890964511965)
    ·
      refine ⟨5361774950498209111691987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14298066534661890964511965 5361774950498209111691987)
      ·
        refine ⟨8042662425747313667537981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5361774950498209111691987 8042662425747313667537981)
        ·
          refine ⟨3015998409655242625326743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8042662425747313667537981 3015998409655242625326743)
          ·
            refine ⟨4523997614482863937990115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3015998409655242625326743 4523997614482863937990115)
            ·
              refine ⟨6785996421724295906985173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4523997614482863937990115 6785996421724295906985173)
              ·
                refine ⟨159046791134163185319965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6785996421724295906985173 159046791134163185319965)
                ·
                  rfl

theorem cell22_4181524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 7].length) (baseStart_4181524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181524 prefixEnd_4181524 := by exact prefixLift 4181524
  have htrace : WordTrace (prefixWord ++ tailWord_4181524) baseStart_4181524 baseEnd_4181524 := by
    simpa [prefixWord, tailWord_4181524, baseEnd_4181524] using wordTrace_append hprefix tailTrace_4181524
  have hstable : (prefixWord ++ tailWord_4181524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181524).length < 2 ^ (prefixWord ++ tailWord_4181524).sum := by decide
  have hdescent : baseEnd_4181524 < baseStart_4181524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181580 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 6]
def baseStart_4181580 : Nat := 118140960795 + 4181580 * 2 ^ 59
def prefixEnd_4181580 : Nat := 4983230072969 + 3 ^ 40 * 4181580 * 2
def baseEnd_4181580 : Nat := 477146763383967729493171

theorem tailTrace_4181580 : CollatzResearch.WordTrace tailWord_4181580 prefixEnd_4181580 477146763383967729493171 := by
  unfold tailWord_4181580
  simp only [CollatzResearch.WordTrace]
  refine ⟨76257376095428645926083097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101676501460571527901444129 76257376095428645926083097)
  ·
    refine ⟨57193032071571484444562323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76257376095428645926083097 57193032071571484444562323)
    ·
      refine ⟨85789548107357226666843485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57193032071571484444562323 85789548107357226666843485)
      ·
        refine ⟨32171080540258960000066307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85789548107357226666843485 32171080540258960000066307)
        ·
          refine ⟨48256620810388440000099461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32171080540258960000066307 48256620810388440000099461)
          ·
            refine ⟨9048116401947832500018649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48256620810388440000099461 9048116401947832500018649)
            ·
              refine ⟨6786087301460874375013987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9048116401947832500018649 6786087301460874375013987)
              ·
                refine ⟨10179130952191311562520981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6786087301460874375013987 10179130952191311562520981)
                ·
                  refine ⟨477146763383967729493171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10179130952191311562520981 477146763383967729493171)
                  ·
                    rfl

theorem cell22_4181580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_4181580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181580 prefixEnd_4181580 := by exact prefixLift 4181580
  have htrace : WordTrace (prefixWord ++ tailWord_4181580) baseStart_4181580 baseEnd_4181580 := by
    simpa [prefixWord, tailWord_4181580, baseEnd_4181580] using wordTrace_append hprefix tailTrace_4181580
  have hstable : (prefixWord ++ tailWord_4181580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181580).length < 2 ^ (prefixWord ++ tailWord_4181580).sum := by decide
  have hdescent : baseEnd_4181580 < baseStart_4181580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181610 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_4181610 : Nat := 118140960795 + 4181610 * 2 ^ 59
def prefixEnd_4181610 : Nat := 4983230072969 + 3 ^ 40 * 4181610 * 2
def baseEnd_4181610 : Nat := 1431450559764993110229421

theorem tailTrace_4181610 : CollatzResearch.WordTrace tailWord_4181610 prefixEnd_4181610 1431450559764993110229421 := by
  unfold tailWord_4181610
  simp only [CollatzResearch.WordTrace]
  refine ⟨38128961595187151743939571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101677230920499071317172189 38128961595187151743939571)
  ·
    refine ⟨57193442392780727615909357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38128961595187151743939571 57193442392780727615909357)
    ·
      refine ⟨21447540897292772855966009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57193442392780727615909357 21447540897292772855966009)
      ·
        refine ⟨16085655672969579641974507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21447540897292772855966009 16085655672969579641974507)
        ·
          refine ⟨24128483509454369462961761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16085655672969579641974507 24128483509454369462961761)
          ·
            refine ⟨18096362632090777097221321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24128483509454369462961761 18096362632090777097221321)
            ·
              refine ⟨13572271974068082822915991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18096362632090777097221321 13572271974068082822915991)
              ·
                refine ⟨20358407961102124234373987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13572271974068082822915991 20358407961102124234373987)
                ·
                  refine ⟨30537611941653186351560981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20358407961102124234373987 30537611941653186351560981)
                  ·
                    refine ⟨1431450559764993110229421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30537611941653186351560981 1431450559764993110229421)
                    ·
                      rfl

theorem cell22_4181610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_4181610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181610 prefixEnd_4181610 := by exact prefixLift 4181610
  have htrace : WordTrace (prefixWord ++ tailWord_4181610) baseStart_4181610 baseEnd_4181610 := by
    simpa [prefixWord, tailWord_4181610, baseEnd_4181610] using wordTrace_append hprefix tailTrace_4181610
  have hstable : (prefixWord ++ tailWord_4181610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181610).length < 2 ^ (prefixWord ++ tailWord_4181610).sum := by decide
  have hdescent : baseEnd_4181610 < baseStart_4181610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181646 : List Nat := [4, 1, 1, 3, 1, 4, 2, 1, 2, 3]
def baseStart_4181646 : Nat := 118140960795 + 4181646 * 2 ^ 59
def prefixEnd_4181646 : Nat := 4983230072969 + 3 ^ 40 * 4181646 * 2
def baseEnd_4181646 : Nat := 1431462883300701016329311

theorem tailTrace_4181646 : CollatzResearch.WordTrace tailWord_4181646 prefixEnd_4181646 1431462883300701016329311 := by
  unfold tailWord_4181646
  simp only [CollatzResearch.WordTrace]
  refine ⟨19064644926077273140508599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101678106272412123416045861 19064644926077273140508599)
  ·
    refine ⟨28596967389115909710762899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19064644926077273140508599 28596967389115909710762899)
    ·
      refine ⟨42895451083673864566144349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28596967389115909710762899 42895451083673864566144349)
      ·
        refine ⟨16085794156377699212304131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42895451083673864566144349 16085794156377699212304131)
        ·
          refine ⟨24128691234566548818456197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16085794156377699212304131 24128691234566548818456197)
          ·
            refine ⟨4524129606481227903460537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24128691234566548818456197 4524129606481227903460537)
            ·
              refine ⟨3393097204860920927595403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4524129606481227903460537 3393097204860920927595403)
              ·
                refine ⟨5089645807291381391393105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3393097204860920927595403 5089645807291381391393105)
                ·
                  refine ⟨3817234355468536043544829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5089645807291381391393105 3817234355468536043544829)
                  ·
                    refine ⟨1431462883300701016329311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817234355468536043544829 1431462883300701016329311)
                    ·
                      rfl

theorem cell22_4181646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_4181646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181646 prefixEnd_4181646 := by exact prefixLift 4181646
  have htrace : WordTrace (prefixWord ++ tailWord_4181646) baseStart_4181646 baseEnd_4181646 := by
    simpa [prefixWord, tailWord_4181646, baseEnd_4181646] using wordTrace_append hprefix tailTrace_4181646
  have hstable : (prefixWord ++ tailWord_4181646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181646).length < 2 ^ (prefixWord ++ tailWord_4181646).sum := by decide
  have hdescent : baseEnd_4181646 < baseStart_4181646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181687 : List Nat := [1, 1, 3, 1, 5, 2, 2, 2, 5]
def baseStart_4181687 : Nat := 118140960795 + 4181687 * 2 ^ 59
def prefixEnd_4181687 : Nat := 4983230072969 + 3 ^ 40 * 4181687 * 2
def baseEnd_4181687 : Nat := 477158972812863525351395

theorem tailTrace_4181687 : CollatzResearch.WordTrace tailWord_4181687 prefixEnd_4181687 477158972812863525351395 := by
  unfold tailWord_4181687
  simp only [CollatzResearch.WordTrace]
  refine ⟨152518654801469649126311315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101679103200979766084207543 152518654801469649126311315)
  ·
    refine ⟨228777982202204473689466973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152518654801469649126311315 228777982202204473689466973)
    ·
      refine ⟨85791743325826677633550115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228777982202204473689466973 85791743325826677633550115)
      ·
        refine ⟨128687614988740016450325173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85791743325826677633550115 128687614988740016450325173)
        ·
          refine ⟨12064463905194376542217985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128687614988740016450325173 12064463905194376542217985)
          ·
            refine ⟨9048347928895782406663489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12064463905194376542217985 9048347928895782406663489)
            ·
              refine ⟨6786260946671836804997617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9048347928895782406663489 6786260946671836804997617)
              ·
                refine ⟨5089695710003877603748213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6786260946671836804997617 5089695710003877603748213)
                ·
                  refine ⟨477158972812863525351395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5089695710003877603748213 477158972812863525351395)
                  ·
                    rfl

theorem cell22_4181687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 5].length) (baseStart_4181687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181687 prefixEnd_4181687 := by exact prefixLift 4181687
  have htrace : WordTrace (prefixWord ++ tailWord_4181687) baseStart_4181687 baseEnd_4181687 := by
    simpa [prefixWord, tailWord_4181687, baseEnd_4181687] using wordTrace_append hprefix tailTrace_4181687
  have hstable : (prefixWord ++ tailWord_4181687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181687).length < 2 ^ (prefixWord ++ tailWord_4181687).sum := by decide
  have hdescent : baseEnd_4181687 < baseStart_4181687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181762 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_4181762 : Nat := 118140960795 + 4181762 * 2 ^ 59
def prefixEnd_4181762 : Nat := 4983230072969 + 3 ^ 40 * 4181762 * 2
def baseEnd_4181762 : Nat := 1431502592471315380428955

theorem tailTrace_4181762 : CollatzResearch.WordTrace tailWord_4181762 prefixEnd_4181762 1431502592471315380428955 := by
  unfold tailWord_4181762
  simp only [CollatzResearch.WordTrace]
  refine ⟨38130347569049484233822885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101680926850798624623527693 38130347569049484233822885)
  ·
    refine ⟨7149440169196778293841791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38130347569049484233822885 7149440169196778293841791)
    ·
      refine ⟨10724160253795167440762687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7149440169196778293841791 10724160253795167440762687)
      ·
        refine ⟨16086240380692751161144031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10724160253795167440762687 16086240380692751161144031)
        ·
          refine ⟨24129360571039126741716047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16086240380692751161144031 24129360571039126741716047)
          ·
            refine ⟨36194040856558690112574071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24129360571039126741716047 36194040856558690112574071)
            ·
              refine ⟨54291061284838035168861107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36194040856558690112574071 54291061284838035168861107)
              ·
                refine ⟨81436591927257052753291661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54291061284838035168861107 81436591927257052753291661)
                ·
                  refine ⟨30538721972721394782484373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81436591927257052753291661 30538721972721394782484373)
                  ·
                    refine ⟨1431502592471315380428955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30538721972721394782484373 1431502592471315380428955)
                    ·
                      rfl

theorem cell22_4181762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_4181762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181762 prefixEnd_4181762 := by exact prefixLift 4181762
  have htrace : WordTrace (prefixWord ++ tailWord_4181762) baseStart_4181762 baseEnd_4181762 := by
    simpa [prefixWord, tailWord_4181762, baseEnd_4181762] using wordTrace_append hprefix tailTrace_4181762
  have hstable : (prefixWord ++ tailWord_4181762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181762).length < 2 ^ (prefixWord ++ tailWord_4181762).sum := by decide
  have hdescent : baseEnd_4181762 < baseStart_4181762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181764 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_4181764 : Nat := 118140960795 + 4181764 * 2 ^ 59
def prefixEnd_4181764 : Nat := 4983230072969 + 3 ^ 40 * 4181764 * 2
def baseEnd_4181764 : Nat := 1431503277112188041878949

theorem tailTrace_4181764 : CollatzResearch.WordTrace tailWord_4181764 prefixEnd_4181764 1431503277112188041878949 := by
  unfold tailWord_4181764
  simp only [CollatzResearch.WordTrace]
  refine ⟨76260731611095345638432173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101680975481460460851242897 76260731611095345638432173)
  ·
    refine ⟨28597774354160754614412065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76260731611095345638432173 28597774354160754614412065)
    ·
      refine ⟨21448330765620565960809049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28597774354160754614412065 21448330765620565960809049)
      ·
        refine ⟨16086248074215424470606787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21448330765620565960809049 16086248074215424470606787)
        ·
          refine ⟨24129372111323136705910181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16086248074215424470606787 24129372111323136705910181)
          ·
            refine ⟨4524257270873088132358159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24129372111323136705910181 4524257270873088132358159)
            ·
              refine ⟨6786385906309632198537239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524257270873088132358159 6786385906309632198537239)
              ·
                refine ⟨10179578859464448297805859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6786385906309632198537239 10179578859464448297805859)
                ·
                  refine ⟨15269368289196672446708789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10179578859464448297805859 15269368289196672446708789)
                  ·
                    refine ⟨1431503277112188041878949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15269368289196672446708789 1431503277112188041878949)
                    ·
                      rfl

theorem cell22_4181764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_4181764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181764 prefixEnd_4181764 := by exact prefixLift 4181764
  have htrace : WordTrace (prefixWord ++ tailWord_4181764) baseStart_4181764 baseEnd_4181764 := by
    simpa [prefixWord, tailWord_4181764, baseEnd_4181764] using wordTrace_append hprefix tailTrace_4181764
  have hstable : (prefixWord ++ tailWord_4181764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181764).length < 2 ^ (prefixWord ++ tailWord_4181764).sum := by decide
  have hdescent : baseEnd_4181764 < baseStart_4181764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181809 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 3, 3]
def baseStart_4181809 : Nat := 118140960795 + 4181809 * 2 ^ 59
def prefixEnd_4181809 : Nat := 4983230072969 + 3 ^ 40 * 4181809 * 2
def baseEnd_4181809 : Nat := 1431518681531822924503811

theorem tailTrace_4181809 : CollatzResearch.WordTrace tailWord_4181809 prefixEnd_4181809 1431518681531822924503811 := by
  unfold tailWord_4181809
  simp only [CollatzResearch.WordTrace]
  refine ⟨152523104507027663962252481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101682069671351775974834987 152523104507027663962252481)
  ·
    refine ⟨114392328380270747971689361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152523104507027663962252481 114392328380270747971689361)
    ·
      refine ⟨85794246285203060978767021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114392328380270747971689361 85794246285203060978767021)
      ·
        refine ⟨32172842356951147867037633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85794246285203060978767021 32172842356951147867037633)
        ·
          refine ⟨24129631767713360900278225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32172842356951147867037633 24129631767713360900278225)
          ·
            refine ⟨18097223825785020675208669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24129631767713360900278225 18097223825785020675208669)
            ·
              refine ⟨6786458934669382753203251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18097223825785020675208669 6786458934669382753203251)
              ·
                refine ⟨10179688402004074129804877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6786458934669382753203251 10179688402004074129804877)
                ·
                  refine ⟨3817383150751527798676829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10179688402004074129804877 3817383150751527798676829)
                  ·
                    refine ⟨1431518681531822924503811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817383150751527798676829 1431518681531822924503811)
                    ·
                      rfl

theorem cell22_4181809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_4181809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181809 prefixEnd_4181809 := by exact prefixLift 4181809
  have htrace : WordTrace (prefixWord ++ tailWord_4181809) baseStart_4181809 baseEnd_4181809 := by
    simpa [prefixWord, tailWord_4181809, baseEnd_4181809] using wordTrace_append hprefix tailTrace_4181809
  have hstable : (prefixWord ++ tailWord_4181809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181809).length < 2 ^ (prefixWord ++ tailWord_4181809).sum := by decide
  have hdescent : baseEnd_4181809 < baseStart_4181809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181860 : List Nat := [2, 3, 1, 1, 5, 2, 2, 2, 1, 3]
def baseStart_4181860 : Nat := 118140960795 + 4181860 * 2 ^ 59
def prefixEnd_4181860 : Nat := 4983230072969 + 3 ^ 40 * 4181860 * 2
def baseEnd_4181860 : Nat := 1431536139874075791478655

theorem tailTrace_4181860 : CollatzResearch.WordTrace tailWord_4181860 prefixEnd_4181860 1431536139874075791478655 := by
  unfold tailWord_4181860
  simp only [CollatzResearch.WordTrace]
  refine ⟨76262482314921449836179517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101683309753228599781572689 76262482314921449836179517)
  ·
    refine ⟨28598430868095543688567319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76262482314921449836179517 28598430868095543688567319)
    ·
      refine ⟨42897646302143315532850979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28598430868095543688567319 42897646302143315532850979)
      ·
        refine ⟨64346469453214973299276469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42897646302143315532850979 64346469453214973299276469)
        ·
          refine ⟨6032481511238903746807169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64346469453214973299276469 6032481511238903746807169)
          ·
            refine ⟨4524361133429177810105377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6032481511238903746807169 4524361133429177810105377)
            ·
              refine ⟨3393270850071883357579033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4524361133429177810105377 3393270850071883357579033)
              ·
                refine ⟨2544953137553912518184275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3393270850071883357579033 2544953137553912518184275)
                ·
                  refine ⟨3817429706330868777276413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2544953137553912518184275 3817429706330868777276413)
                  ·
                    refine ⟨1431536139874075791478655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817429706330868777276413 1431536139874075791478655)
                    ·
                      rfl

theorem cell22_4181860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_4181860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181860 prefixEnd_4181860 := by exact prefixLift 4181860
  have htrace : WordTrace (prefixWord ++ tailWord_4181860) baseStart_4181860 baseEnd_4181860 := by
    simpa [prefixWord, tailWord_4181860, baseEnd_4181860] using wordTrace_append hprefix tailTrace_4181860
  have hstable : (prefixWord ++ tailWord_4181860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181860).length < 2 ^ (prefixWord ++ tailWord_4181860).sum := by decide
  have hdescent : baseEnd_4181860 < baseStart_4181860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181882 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_4181882 : Nat := 118140960795 + 4181882 * 2 ^ 59
def prefixEnd_4181882 : Nat := 4983230072969 + 3 ^ 40 * 4181882 * 2
def baseEnd_4181882 : Nat := 1431543670923675067428587

theorem tailTrace_4181882 : CollatzResearch.WordTrace tailWord_4181882 prefixEnd_4181882 1431543670923675067428587 := by
  unfold tailWord_4181882
  simp only [CollatzResearch.WordTrace]
  refine ⟨38131441758940799357414975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101683844690508798286439933 38131441758940799357414975)
  ·
    refine ⟨57197162638411199036122463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38131441758940799357414975 57197162638411199036122463)
    ·
      refine ⟨85795743957616798554183695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57197162638411199036122463 85795743957616798554183695)
      ·
        refine ⟨128693615936425197831275543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85795743957616798554183695 128693615936425197831275543)
        ·
          refine ⟨193040423904637796746913315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128693615936425197831275543 193040423904637796746913315)
          ·
            refine ⟨289560635856956695120369973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193040423904637796746913315 289560635856956695120369973)
            ·
              refine ⟨27146309611589690167534685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289560635856956695120369973 27146309611589690167534685)
              ·
                refine ⟨10179866104346133812825507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27146309611589690167534685 10179866104346133812825507)
                ·
                  refine ⟨15269799156519200719238261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10179866104346133812825507 15269799156519200719238261)
                  ·
                    refine ⟨1431543670923675067428587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15269799156519200719238261 1431543670923675067428587)
                    ·
                      rfl

theorem cell22_4181882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_4181882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181882 prefixEnd_4181882 := by exact prefixLift 4181882
  have htrace : WordTrace (prefixWord ++ tailWord_4181882) baseStart_4181882 baseEnd_4181882 := by
    simpa [prefixWord, tailWord_4181882, baseEnd_4181882] using wordTrace_append hprefix tailTrace_4181882
  have hstable : (prefixWord ++ tailWord_4181882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181882).length < 2 ^ (prefixWord ++ tailWord_4181882).sum := by decide
  have hdescent : baseEnd_4181882 < baseStart_4181882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181886 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4181886 : Nat := 118140960795 + 4181886 * 2 ^ 59
def prefixEnd_4181886 : Nat := 4983230072969 + 3 ^ 40 * 4181886 * 2
def baseEnd_4181886 : Nat := 1431545040205420390328575

theorem tailTrace_4181886 : CollatzResearch.WordTrace tailWord_4181886 prefixEnd_4181886 1431545040205420390328575 := by
  unfold tailWord_4181886
  simp only [CollatzResearch.WordTrace]
  refine ⟨19065739115968588264100689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101683941951832470741870341 19065739115968588264100689)
  ·
    refine ⟨14299304336976441198075517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19065739115968588264100689 14299304336976441198075517)
    ·
      refine ⟨5362239126366165449278319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14299304336976441198075517 5362239126366165449278319)
      ·
        refine ⟨8043358689549248173917479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5362239126366165449278319 8043358689549248173917479)
        ·
          refine ⟨12065038034323872260876219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8043358689549248173917479 12065038034323872260876219)
          ·
            refine ⟨18097557051485808391314329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12065038034323872260876219 18097557051485808391314329)
            ·
              refine ⟨13573167788614356293485747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18097557051485808391314329 13573167788614356293485747)
              ·
                refine ⟨20359751682921534440228621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13573167788614356293485747 20359751682921534440228621)
                ·
                  refine ⟨7634906881095575415085733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20359751682921534440228621 7634906881095575415085733)
                  ·
                    refine ⟨1431545040205420390328575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7634906881095575415085733 1431545040205420390328575)
                    ·
                      rfl

theorem cell22_4181886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4181886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181886 prefixEnd_4181886 := by exact prefixLift 4181886
  have htrace : WordTrace (prefixWord ++ tailWord_4181886) baseStart_4181886 baseEnd_4181886 := by
    simpa [prefixWord, tailWord_4181886, baseEnd_4181886] using wordTrace_append hprefix tailTrace_4181886
  have hstable : (prefixWord ++ tailWord_4181886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181886).length < 2 ^ (prefixWord ++ tailWord_4181886).sum := by decide
  have hdescent : baseEnd_4181886 < baseStart_4181886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181897 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 1, 6]
def baseStart_4181897 : Nat := 118140960795 + 4181897 * 2 ^ 59
def prefixEnd_4181897 : Nat := 4983230072969 + 3 ^ 40 * 4181897 * 2
def baseEnd_4181897 : Nat := 1431548805730220028303541

theorem tailTrace_4181897 : CollatzResearch.WordTrace tailWord_4181897 prefixEnd_4181897 1431548805730220028303541 := by
  unfold tailWord_4181897
  simp only [CollatzResearch.WordTrace]
  refine ⟨152526314130708854991455945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101684209420472569994303963 152526314130708854991455945)
  ·
    refine ⟨114394735598031641243591959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152526314130708854991455945 114394735598031641243591959)
    ·
      refine ⟨171592103397047461865387939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114394735598031641243591959 171592103397047461865387939)
      ·
        refine ⟨257388155095571192798081909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171592103397047461865387939 257388155095571192798081909)
        ·
          refine ⟨24130139540209799324820179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257388155095571192798081909 24130139540209799324820179)
          ·
            refine ⟨36195209310314698987230269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24130139540209799324820179 36195209310314698987230269)
            ·
              refine ⟨13573203491368012120211351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36195209310314698987230269 13573203491368012120211351)
              ·
                refine ⟨20359805237052018180317027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13573203491368012120211351 20359805237052018180317027)
                ·
                  refine ⟨30539707855578027270475541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20359805237052018180317027 30539707855578027270475541)
                  ·
                    refine ⟨1431548805730220028303541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30539707855578027270475541 1431548805730220028303541)
                    ·
                      rfl

theorem cell22_4181897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 6].length) (baseStart_4181897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181897 prefixEnd_4181897 := by exact prefixLift 4181897
  have htrace : WordTrace (prefixWord ++ tailWord_4181897) baseStart_4181897 baseEnd_4181897 := by
    simpa [prefixWord, tailWord_4181897, baseEnd_4181897] using wordTrace_append hprefix tailTrace_4181897
  have hstable : (prefixWord ++ tailWord_4181897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181897).length < 2 ^ (prefixWord ++ tailWord_4181897).sum := by decide
  have hdescent : baseEnd_4181897 < baseStart_4181897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181916 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 4, 3]
def baseStart_4181916 : Nat := 118140960795 + 4181916 * 2 ^ 59
def prefixEnd_4181916 : Nat := 4983230072969 + 3 ^ 40 * 4181916 * 2
def baseEnd_4181916 : Nat := 1431555309818510312078483

theorem tailTrace_4181916 : CollatzResearch.WordTrace tailWord_4181916 prefixEnd_4181916 1431555309818510312078483 := by
  unfold tailWord_4181916
  simp only [CollatzResearch.WordTrace]
  refine ⟨76263503558820010618198801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101684671411760014157598401 76263503558820010618198801)
  ·
    refine ⟨57197627669115007963649101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76263503558820010618198801 57197627669115007963649101)
    ·
      refine ⟨21449110375918127986368413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57197627669115007963649101 21449110375918127986368413)
      ·
        refine ⟨8043416390969297994888155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21449110375918127986368413 8043416390969297994888155)
        ·
          refine ⟨12065124586453946992332233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8043416390969297994888155 12065124586453946992332233)
          ·
            refine ⟨9048843439840460244249175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12065124586453946992332233 9048843439840460244249175)
            ·
              refine ⟨13573265159760690366373763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9048843439840460244249175 13573265159760690366373763)
              ·
                refine ⟨20359897739641035549560645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13573265159760690366373763 20359897739641035549560645)
                ·
                  refine ⟨3817480826182694165542621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20359897739641035549560645 3817480826182694165542621)
                  ·
                    refine ⟨1431555309818510312078483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817480826182694165542621 1431555309818510312078483)
                    ·
                      rfl

theorem cell22_4181916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_4181916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181916 prefixEnd_4181916 := by exact prefixLift 4181916
  have htrace : WordTrace (prefixWord ++ tailWord_4181916) baseStart_4181916 baseEnd_4181916 := by
    simpa [prefixWord, tailWord_4181916, baseEnd_4181916] using wordTrace_append hprefix tailTrace_4181916
  have hstable : (prefixWord ++ tailWord_4181916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181916).length < 2 ^ (prefixWord ++ tailWord_4181916).sum := by decide
  have hdescent : baseEnd_4181916 < baseStart_4181916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181918 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_4181918 : Nat := 118140960795 + 4181918 * 2 ^ 59
def prefixEnd_4181918 : Nat := 4983230072969 + 3 ^ 40 * 4181918 * 2
def baseEnd_4181918 : Nat := 477185331486460991176159

theorem tailTrace_4181918 : CollatzResearch.WordTrace tailWord_4181918 prefixEnd_4181918 477185331486460991176159 := by
  unfold tailWord_4181918
  simp only [CollatzResearch.WordTrace]
  refine ⟨19065885007954096947246301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101684720042421850385313605 19065885007954096947246301)
  ·
    refine ⟨7149706877982786355217363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19065885007954096947246301 7149706877982786355217363)
    ·
      refine ⟨10724560316974179532826045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7149706877982786355217363 10724560316974179532826045)
      ·
        refine ⟨4021710118865317324809767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10724560316974179532826045 4021710118865317324809767)
        ·
          refine ⟨6032565178297975987214651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4021710118865317324809767 6032565178297975987214651)
          ·
            refine ⟨9048847767446963980821977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6032565178297975987214651 9048847767446963980821977)
            ·
              refine ⟨6786635825585222985616483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9048847767446963980821977 6786635825585222985616483)
              ·
                refine ⟨10179953738377834478424725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6786635825585222985616483 10179953738377834478424725)
                ·
                  refine ⟨477185331486460991176159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10179953738377834478424725 477185331486460991176159)
                  ·
                    rfl

theorem cell22_4181918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_4181918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181918 prefixEnd_4181918 := by exact prefixLift 4181918
  have htrace : WordTrace (prefixWord ++ tailWord_4181918) baseStart_4181918 baseEnd_4181918 := by
    simpa [prefixWord, tailWord_4181918, baseEnd_4181918] using wordTrace_append hprefix tailTrace_4181918
  have hstable : (prefixWord ++ tailWord_4181918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181918).length < 2 ^ (prefixWord ++ tailWord_4181918).sum := by decide
  have hdescent : baseEnd_4181918 < baseStart_4181918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181944 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 3, 3]
def baseStart_4181944 : Nat := 118140960795 + 4181944 * 2 ^ 59
def prefixEnd_4181944 : Nat := 4983230072969 + 3 ^ 40 * 4181944 * 2
def baseEnd_4181944 : Nat := 1431564894790727572378397

theorem tailTrace_4181944 : CollatzResearch.WordTrace tailWord_4181944 prefixEnd_4181944 1431564894790727572378397 := by
  unfold tailWord_4181944
  simp only [CollatzResearch.WordTrace]
  refine ⟨76264014180769291009208443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101685352241025721345611257 76264014180769291009208443)
  ·
    refine ⟨114396021271153936513812665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76264014180769291009208443 114396021271153936513812665)
    ·
      refine ⟨85797015953365452385359499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114396021271153936513812665 85797015953365452385359499)
      ·
        refine ⟨128695523930048178578039249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85797015953365452385359499 128695523930048178578039249)
        ·
          refine ⟨96521642947536133933529437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128695523930048178578039249 96521642947536133933529437)
          ·
            refine ⟨36195616105326050225073539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96521642947536133933529437 36195616105326050225073539)
            ·
              refine ⟨54293424157989075337610309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36195616105326050225073539 54293424157989075337610309)
              ·
                refine ⟨10180017029622951625801933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54293424157989075337610309 10180017029622951625801933)
                ·
                  refine ⟨3817506386108606859675725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10180017029622951625801933 3817506386108606859675725)
                  ·
                    refine ⟨1431564894790727572378397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817506386108606859675725 1431564894790727572378397)
                    ·
                      rfl

theorem cell22_4181944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_4181944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181944 prefixEnd_4181944 := by exact prefixLift 4181944
  have htrace : WordTrace (prefixWord ++ tailWord_4181944) baseStart_4181944 baseEnd_4181944 := by
    simpa [prefixWord, tailWord_4181944, baseEnd_4181944] using wordTrace_append hprefix tailTrace_4181944
  have hstable : (prefixWord ++ tailWord_4181944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181944).length < 2 ^ (prefixWord ++ tailWord_4181944).sum := by decide
  have hdescent : baseEnd_4181944 < baseStart_4181944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181978 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 3, 3]
def baseStart_4181978 : Nat := 118140960795 + 4181978 * 2 ^ 59
def prefixEnd_4181978 : Nat := 4983230072969 + 3 ^ 40 * 4181978 * 2
def baseEnd_4181978 : Nat := 1431576533685562817028293

theorem tailTrace_4181978 : CollatzResearch.WordTrace tailWord_4181978 prefixEnd_4181978 1431576533685562817028293 := by
  unfold tailWord_4181978
  simp only [CollatzResearch.WordTrace]
  refine ⟨38132317110853851456288647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101686178962276937216769725 38132317110853851456288647)
  ·
    refine ⟨57198475666280777184432971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38132317110853851456288647 57198475666280777184432971)
    ·
      refine ⟨85797713499421165776649457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57198475666280777184432971 85797713499421165776649457)
      ·
        refine ⟨64348285124565874332487093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85797713499421165776649457 64348285124565874332487093)
        ·
          refine ⟨6032651730428050718670665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64348285124565874332487093 6032651730428050718670665)
          ·
            refine ⟨4524488797821038039002999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6032651730428050718670665 4524488797821038039002999)
            ·
              refine ⟨6786733196731557058504499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4524488797821038039002999 6786733196731557058504499)
              ·
                refine ⟨10180099795097335587756749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6786733196731557058504499 10180099795097335587756749)
                ·
                  refine ⟨3817537423161500845408781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10180099795097335587756749 3817537423161500845408781)
                  ·
                    refine ⟨1431576533685562817028293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817537423161500845408781 1431576533685562817028293)
                    ·
                      rfl

theorem cell22_4181978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 3, 3].length) (baseStart_4181978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181978 prefixEnd_4181978 := by exact prefixLift 4181978
  have htrace : WordTrace (prefixWord ++ tailWord_4181978) baseStart_4181978 baseEnd_4181978 := by
    simpa [prefixWord, tailWord_4181978, baseEnd_4181978] using wordTrace_append hprefix tailTrace_4181978
  have hstable : (prefixWord ++ tailWord_4181978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181978).length < 2 ^ (prefixWord ++ tailWord_4181978).sum := by decide
  have hdescent : baseEnd_4181978 < baseStart_4181978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4181991 : List Nat := [1, 1, 5, 2, 3, 1, 1, 3, 5]
def baseStart_4181991 : Nat := 118140960795 + 4181991 * 2 ^ 59
def prefixEnd_4181991 : Nat := 4983230072969 + 3 ^ 40 * 4181991 * 2
def baseEnd_4181991 : Nat := 477193661283745038817751

theorem tailTrace_4181991 : CollatzResearch.WordTrace tailWord_4181991 prefixEnd_4181991 477193661283745038817751 := by
  unfold tailWord_4181991
  simp only [CollatzResearch.WordTrace]
  refine ⟨152529742592368309045377827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101686495061578872696918551 152529742592368309045377827)
  ·
    refine ⟨228794613888552463568066741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152529742592368309045377827 228794613888552463568066741)
    ·
      refine ⟨21449495052051793459506257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228794613888552463568066741 21449495052051793459506257)
      ·
        refine ⟨16087121289038845094629693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21449495052051793459506257 16087121289038845094629693)
        ·
          refine ⟨6032670483389566910486135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16087121289038845094629693 6032670483389566910486135)
          ·
            refine ⟨9049005725084350365729203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6032670483389566910486135 9049005725084350365729203)
            ·
              refine ⟨13573508587626525548593805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9049005725084350365729203 13573508587626525548593805)
              ·
                refine ⟨5090065720359947080722677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13573508587626525548593805 5090065720359947080722677)
                ·
                  refine ⟨477193661283745038817751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5090065720359947080722677 477193661283745038817751)
                  ·
                    rfl

theorem cell22_4181991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 5].length) (baseStart_4181991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4181991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4181991 prefixEnd_4181991 := by exact prefixLift 4181991
  have htrace : WordTrace (prefixWord ++ tailWord_4181991) baseStart_4181991 baseEnd_4181991 := by
    simpa [prefixWord, tailWord_4181991, baseEnd_4181991] using wordTrace_append hprefix tailTrace_4181991
  have hstable : (prefixWord ++ tailWord_4181991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4181991).length < 2 ^ (prefixWord ++ tailWord_4181991).sum := by decide
  have hdescent : baseEnd_4181991 < baseStart_4181991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4181991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182029 : List Nat := [1, 7, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_4182029 : Nat := 118140960795 + 4182029 * 2 ^ 59
def prefixEnd_4182029 : Nat := 4983230072969 + 3 ^ 40 * 4182029 * 2
def baseEnd_4182029 : Nat := 1431593992027815684003137

theorem tailTrace_4182029 : CollatzResearch.WordTrace tailWord_4182029 prefixEnd_4182029 1431593992027815684003137 := by
  unfold tailWord_4182029
  simp only [CollatzResearch.WordTrace]
  refine ⟨152531128566230641535261141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101687419044153761023507427 152531128566230641535261141)
  ·
    refine ⟨3574948325771030660982683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 152531128566230641535261141 3574948325771030660982683)
    ·
      refine ⟨5362422488656545991474025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3574948325771030660982683 5362422488656545991474025)
      ·
        refine ⟨4021816866492409493605519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5362422488656545991474025 4021816866492409493605519)
        ·
          refine ⟨6032725299738614240408279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4021816866492409493605519 6032725299738614240408279)
          ·
            refine ⟨9049087949607921360612419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6032725299738614240408279 9049087949607921360612419)
            ·
              refine ⟨13573631924411882040918629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9049087949607921360612419 13573631924411882040918629)
              ·
                refine ⟨2545055985827227882672243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13573631924411882040918629 2545055985827227882672243)
                ·
                  refine ⟨3817583978740841824008365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545055985827227882672243 3817583978740841824008365)
                  ·
                    refine ⟨1431593992027815684003137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817583978740841824008365 1431593992027815684003137)
                    ·
                      rfl

theorem cell22_4182029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_4182029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182029 prefixEnd_4182029 := by exact prefixLift 4182029
  have htrace : WordTrace (prefixWord ++ tailWord_4182029) baseStart_4182029 baseEnd_4182029 := by
    simpa [prefixWord, tailWord_4182029, baseEnd_4182029] using wordTrace_append hprefix tailTrace_4182029
  have hstable : (prefixWord ++ tailWord_4182029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182029).length < 2 ^ (prefixWord ++ tailWord_4182029).sum := by decide
  have hdescent : baseEnd_4182029 < baseStart_4182029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182051 : List Nat := [1, 1, 1, 4, 3, 1, 1, 5, 2, 3]
def baseStart_4182051 : Nat := 118140960795 + 4182051 * 2 ^ 59
def prefixEnd_4182051 : Nat := 4983230072969 + 3 ^ 40 * 4182051 * 2
def baseEnd_4182051 : Nat := 1431601523077414959953069

theorem tailTrace_4182051 : CollatzResearch.WordTrace tailWord_4182051 prefixEnd_4182051 1431601523077414959953069 := by
  unfold tailWord_4182051
  simp only [CollatzResearch.WordTrace]
  refine ⟨152531930972150939292562007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101687953981433959528374671 152531930972150939292562007)
  ·
    refine ⟨228797896458226408938843011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152531930972150939292562007 228797896458226408938843011)
    ·
      refine ⟨343196844687339613408264517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228797896458226408938843011 343196844687339613408264517)
      ·
        refine ⟨64349408378876177514049597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343196844687339613408264517 64349408378876177514049597)
        ·
          refine ⟨24131028142078566567768599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64349408378876177514049597 24131028142078566567768599)
          ·
            refine ⟨36196542213117849851652899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24131028142078566567768599 36196542213117849851652899)
            ·
              refine ⟨54294813319676774777479349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36196542213117849851652899 54294813319676774777479349)
              ·
                refine ⟨5090138748719697635388689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54294813319676774777479349 5090138748719697635388689)
                ·
                  refine ⟨3817604061539773226541517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5090138748719697635388689 3817604061539773226541517)
                  ·
                    refine ⟨1431601523077414959953069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817604061539773226541517 1431601523077414959953069)
                    ·
                      rfl

theorem cell22_4182051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 3].length) (baseStart_4182051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182051 prefixEnd_4182051 := by exact prefixLift 4182051
  have htrace : WordTrace (prefixWord ++ tailWord_4182051) baseStart_4182051 baseEnd_4182051 := by
    simpa [prefixWord, tailWord_4182051, baseEnd_4182051] using wordTrace_append hprefix tailTrace_4182051
  have hstable : (prefixWord ++ tailWord_4182051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182051).length < 2 ^ (prefixWord ++ tailWord_4182051).sum := by decide
  have hdescent : baseEnd_4182051 < baseStart_4182051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182066 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_4182066 : Nat := 118140960795 + 4182066 * 2 ^ 59
def prefixEnd_4182066 : Nat := 4983230072969 + 3 ^ 40 * 4182066 * 2
def baseEnd_4182066 : Nat := 1431606657883959920828023

theorem tailTrace_4182066 : CollatzResearch.WordTrace tailWord_4182066 prefixEnd_4182066 1431606657883959920828023 := by
  unfold tailWord_4182066
  simp only [CollatzResearch.WordTrace]
  refine ⟨38133119516774149213589513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101688318711397731236238701 38133119516774149213589513)
  ·
    refine ⟨28599839637580611910192135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38133119516774149213589513 28599839637580611910192135)
    ·
      refine ⟨42899759456370917865288203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28599839637580611910192135 42899759456370917865288203)
      ·
        refine ⟨64349639184556376797932305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42899759456370917865288203 64349639184556376797932305)
        ·
          refine ⟨48262229388417282598449229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64349639184556376797932305 48262229388417282598449229)
          ·
            refine ⟨18098336020656480974418461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48262229388417282598449229 18098336020656480974418461)
            ·
              refine ⟨6786876007746180365406923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18098336020656480974418461 6786876007746180365406923)
              ·
                refine ⟨10180314011619270548110385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6786876007746180365406923 10180314011619270548110385)
                ·
                  refine ⟨7635235508714452911082789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10180314011619270548110385 7635235508714452911082789)
                  ·
                    refine ⟨1431606657883959920828023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7635235508714452911082789 1431606657883959920828023)
                    ·
                      rfl

theorem cell22_4182066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_4182066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182066 prefixEnd_4182066 := by exact prefixLift 4182066
  have htrace : WordTrace (prefixWord ++ tailWord_4182066) baseStart_4182066 baseEnd_4182066 := by
    simpa [prefixWord, tailWord_4182066, baseEnd_4182066] using wordTrace_append hprefix tailTrace_4182066
  have hstable : (prefixWord ++ tailWord_4182066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182066).length < 2 ^ (prefixWord ++ tailWord_4182066).sum := by decide
  have hdescent : baseEnd_4182066 < baseStart_4182066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182130 : List Nat := [3, 2, 1, 2, 2, 2, 3, 3, 1, 3]
def baseStart_4182130 : Nat := 118140960795 + 4182130 * 2 ^ 59
def prefixEnd_4182130 : Nat := 4983230072969 + 3 ^ 40 * 4182130 * 2
def baseEnd_4182130 : Nat := 1431628566391885087227827

theorem tailTrace_4182130 : CollatzResearch.WordTrace tailWord_4182130 prefixEnd_4182130 1431628566391885087227827 := by
  unfold tailWord_4182130
  simp only [CollatzResearch.WordTrace]
  refine ⟨38133703084716183946171961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101689874892576490523125229 38133703084716183946171961)
  ·
    refine ⟨28600277313537137959628971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38133703084716183946171961 28600277313537137959628971)
    ·
      refine ⟨42900415970305706939443457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28600277313537137959628971 42900415970305706939443457)
      ·
        refine ⟨32175311977729280204582593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42900415970305706939443457 32175311977729280204582593)
        ·
          refine ⟨24131483983296960153436945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32175311977729280204582593 24131483983296960153436945)
          ·
            refine ⟨18098612987472720115077709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24131483983296960153436945 18098612987472720115077709)
            ·
              refine ⟨6786979870302270043154141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18098612987472720115077709 6786979870302270043154141)
              ·
                refine ⟨2545117451363351266182803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6786979870302270043154141 2545117451363351266182803)
                ·
                  refine ⟨3817676177045026899274205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545117451363351266182803 3817676177045026899274205)
                  ·
                    refine ⟨1431628566391885087227827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817676177045026899274205 1431628566391885087227827)
                    ·
                      rfl

theorem cell22_4182130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_4182130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182130 prefixEnd_4182130 := by exact prefixLift 4182130
  have htrace : WordTrace (prefixWord ++ tailWord_4182130) baseStart_4182130 baseEnd_4182130 := by
    simpa [prefixWord, tailWord_4182130, baseEnd_4182130] using wordTrace_append hprefix tailTrace_4182130
  have hstable : (prefixWord ++ tailWord_4182130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182130).length < 2 ^ (prefixWord ++ tailWord_4182130).sum := by decide
  have hdescent : baseEnd_4182130 < baseStart_4182130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182139 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 7, 4]
def baseStart_4182139 : Nat := 118140960795 + 4182139 * 2 ^ 59
def prefixEnd_4182139 : Nat := 4983230072969 + 3 ^ 40 * 4182139 * 2
def baseEnd_4182139 : Nat := 1431631647275812063752799

theorem tailTrace_4182139 : CollatzResearch.WordTrace tailWord_4182139 prefixEnd_4182139 1431631647275812063752799 := by
  unfold tailWord_4182139
  simp only [CollatzResearch.WordTrace]
  refine ⟨152535140595832130321765471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101690093730554753547843647 152535140595832130321765471)
  ·
    refine ⟨228802710893748195482648207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152535140595832130321765471 228802710893748195482648207)
    ·
      refine ⟨343204066340622293223972311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228802710893748195482648207 343204066340622293223972311)
      ·
        refine ⟨514806099510933439835958467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343204066340622293223972311 514806099510933439835958467)
        ·
          refine ⟨772209149266400159753937701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514806099510933439835958467 772209149266400159753937701)
          ·
            refine ⟨144789215487450029953863319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 772209149266400159753937701 144789215487450029953863319)
            ·
              refine ⟨217183823231175044930794979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144789215487450029953863319 217183823231175044930794979)
              ·
                refine ⟨325775734846762567396192469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217183823231175044930794979 325775734846762567396192469)
                ·
                  refine ⟨7635368785470997673348261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 325775734846762567396192469 7635368785470997673348261)
                  ·
                    refine ⟨1431631647275812063752799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7635368785470997673348261 1431631647275812063752799)
                    ·
                      rfl

theorem cell22_4182139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 4].length) (baseStart_4182139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182139 prefixEnd_4182139 := by exact prefixLift 4182139
  have htrace : WordTrace (prefixWord ++ tailWord_4182139) baseStart_4182139 baseEnd_4182139 := by
    simpa [prefixWord, tailWord_4182139, baseEnd_4182139] using wordTrace_append hprefix tailTrace_4182139
  have hstable : (prefixWord ++ tailWord_4182139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182139).length < 2 ^ (prefixWord ++ tailWord_4182139).sum := by decide
  have hdescent : baseEnd_4182139 < baseStart_4182139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182169 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 5, 5]
def baseStart_4182169 : Nat := 118140960795 + 4182169 * 2 ^ 59
def prefixEnd_4182169 : Nat := 4983230072969 + 3 ^ 40 * 4182169 * 2
def baseEnd_4182169 : Nat := 1431641916888901985502707

theorem tailTrace_4182169 : CollatzResearch.WordTrace tailWord_4182169 prefixEnd_4182169 1431641916888901985502707 := by
  unfold tailWord_4182169
  simp only [CollatzResearch.WordTrace]
  refine ⟨152536234785723445445357561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101690823190482296963571707 152536234785723445445357561)
  ·
    refine ⟨114402176089292584084018171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152536234785723445445357561 114402176089292584084018171)
    ·
      refine ⟨171603264133938876126027257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114402176089292584084018171 171603264133938876126027257)
      ·
        refine ⟨128702448100454157094520443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171603264133938876126027257 128702448100454157094520443)
        ·
          refine ⟨193053672150681235641780665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128702448100454157094520443 193053672150681235641780665)
          ·
            refine ⟨144790254113010926731335499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193053672150681235641780665 144790254113010926731335499)
            ·
              refine ⟨217185381169516390097003249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144790254113010926731335499 217185381169516390097003249)
              ·
                refine ⟨162889035877137292572752437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217185381169516390097003249 162889035877137292572752437)
                ·
                  refine ⟨15270847113481621178695541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162889035877137292572752437 15270847113481621178695541)
                  ·
                    refine ⟨1431641916888901985502707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15270847113481621178695541 1431641916888901985502707)
                    ·
                      rfl

theorem cell22_4182169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_4182169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182169 prefixEnd_4182169 := by exact prefixLift 4182169
  have htrace : WordTrace (prefixWord ++ tailWord_4182169) baseStart_4182169 baseEnd_4182169 := by
    simpa [prefixWord, tailWord_4182169, baseEnd_4182169] using wordTrace_append hprefix tailTrace_4182169
  have hstable : (prefixWord ++ tailWord_4182169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182169).length < 2 ^ (prefixWord ++ tailWord_4182169).sum := by decide
  have hdescent : baseEnd_4182169 < baseStart_4182169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182173 : List Nat := [1, 4, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_4182173 : Nat := 118140960795 + 4182173 * 2 ^ 59
def prefixEnd_4182173 : Nat := 4983230072969 + 3 ^ 40 * 4182173 * 2
def baseEnd_4182173 : Nat := 1431643286170647308402695

theorem tailTrace_4182173 : CollatzResearch.WordTrace tailWord_4182173 prefixEnd_4182173 1431643286170647308402695 := by
  unfold tailWord_4182173
  simp only [CollatzResearch.WordTrace]
  refine ⟨152536380677708954128503173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101690920451805969419002115 152536380677708954128503173)
  ·
    refine ⟨28600571377070428899094345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152536380677708954128503173 28600571377070428899094345)
    ·
      refine ⟨21450428532802821674320759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28600571377070428899094345 21450428532802821674320759)
      ·
        refine ⟨32175642799204232511481139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21450428532802821674320759 32175642799204232511481139)
        ·
          refine ⟨48263464198806348767221709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32175642799204232511481139 48263464198806348767221709)
          ·
            refine ⟨18098799074552380787708141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48263464198806348767221709 18098799074552380787708141)
            ·
              refine ⟨6787049652957142795390553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18098799074552380787708141 6787049652957142795390553)
              ·
                refine ⟨5090287239717857096542915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6787049652957142795390553 5090287239717857096542915)
                ·
                  refine ⟨7635430859576785644814373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5090287239717857096542915 7635430859576785644814373)
                  ·
                    refine ⟨1431643286170647308402695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7635430859576785644814373 1431643286170647308402695)
                    ·
                      rfl

theorem cell22_4182173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_4182173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182173 prefixEnd_4182173 := by exact prefixLift 4182173
  have htrace : WordTrace (prefixWord ++ tailWord_4182173) baseStart_4182173 baseEnd_4182173 := by
    simpa [prefixWord, tailWord_4182173, baseEnd_4182173] using wordTrace_append hprefix tailTrace_4182173
  have hstable : (prefixWord ++ tailWord_4182173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182173).length < 2 ^ (prefixWord ++ tailWord_4182173).sum := by decide
  have hdescent : baseEnd_4182173 < baseStart_4182173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182199 : List Nat := [1, 1, 3, 1, 4, 12]
def baseStart_4182199 : Nat := 118140960795 + 4182199 * 2 ^ 59
def prefixEnd_4182199 : Nat := 4983230072969 + 3 ^ 40 * 4182199 * 2
def baseEnd_4182199 : Nat := 17674718351876443299415

theorem tailTrace_4182199 : CollatzResearch.WordTrace tailWord_4182199 prefixEnd_4182199 17674718351876443299415 := by
  unfold tailWord_4182199
  simp only [CollatzResearch.WordTrace]
  refine ⟨152537328975614760568949651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101691552650409840379299767 152537328975614760568949651)
  ·
    refine ⟨228805993463422140853424477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152537328975614760568949651 228805993463422140853424477)
    ·
      refine ⟨85802247548783302820034179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228805993463422140853424477 85802247548783302820034179)
      ·
        refine ⟨128703371323174954230051269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85802247548783302820034179 128703371323174954230051269)
        ·
          refine ⟨24131882123095303918134613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128703371323174954230051269 24131882123095303918134613)
          ·
            refine ⟨17674718351876443299415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 24131882123095303918134613 17674718351876443299415)
            ·
              rfl

theorem cell22_4182199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 12].length) (baseStart_4182199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182199 prefixEnd_4182199 := by exact prefixLift 4182199
  have htrace : WordTrace (prefixWord ++ tailWord_4182199) baseStart_4182199 baseEnd_4182199 := by
    simpa [prefixWord, tailWord_4182199, baseEnd_4182199] using wordTrace_append hprefix tailTrace_4182199
  have hstable : (prefixWord ++ tailWord_4182199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182199).length < 2 ^ (prefixWord ++ tailWord_4182199).sum := by decide
  have hdescent : baseEnd_4182199 < baseStart_4182199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182201 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 2, 4]
def baseStart_4182201 : Nat := 118140960795 + 4182201 * 2 ^ 59
def prefixEnd_4182201 : Nat := 4983230072969 + 3 ^ 40 * 4182201 * 2
def baseEnd_4182201 : Nat := 1431652871142864568702609

theorem tailTrace_4182201 : CollatzResearch.WordTrace tailWord_4182201 prefixEnd_4182201 1431652871142864568702609 := by
  unfold tailWord_4182201
  simp only [CollatzResearch.WordTrace]
  refine ⟨152537401921607514910522457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101691601281071676607014971 152537401921607514910522457)
  ·
    refine ⟨114403051441205636182891843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152537401921607514910522457 114403051441205636182891843)
    ·
      refine ⟨171604577161808454274337765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114403051441205636182891843 171604577161808454274337765)
      ·
        refine ⟨32175858217839085176438331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171604577161808454274337765 32175858217839085176438331)
        ·
          refine ⟨48263787326758627764657497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32175858217839085176438331 48263787326758627764657497)
          ·
            refine ⟨36197840495068970823493123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48263787326758627764657497 36197840495068970823493123)
            ·
              refine ⟨54296760742603456235239685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36197840495068970823493123 54296760742603456235239685)
              ·
                refine ⟨10180642639238148044107441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54296760742603456235239685 10180642639238148044107441)
                ·
                  refine ⟨7635481979428611033080581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10180642639238148044107441 7635481979428611033080581)
                  ·
                    refine ⟨1431652871142864568702609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7635481979428611033080581 1431652871142864568702609)
                    ·
                      rfl

theorem cell22_4182201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_4182201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182201 prefixEnd_4182201 := by exact prefixLift 4182201
  have htrace : WordTrace (prefixWord ++ tailWord_4182201) baseStart_4182201 baseEnd_4182201 := by
    simpa [prefixWord, tailWord_4182201, baseEnd_4182201] using wordTrace_append hprefix tailTrace_4182201
  have hstable : (prefixWord ++ tailWord_4182201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182201).length < 2 ^ (prefixWord ++ tailWord_4182201).sum := by decide
  have hdescent : baseEnd_4182201 < baseStart_4182201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182203 : List Nat := [1, 1, 1, 1, 1, 2, 8, 2, 2, 3]
def baseStart_4182203 : Nat := 118140960795 + 4182203 * 2 ^ 59
def prefixEnd_4182203 : Nat := 4983230072969 + 3 ^ 40 * 4182203 * 2
def baseEnd_4182203 : Nat := 1431653555783737230152603

theorem tailTrace_4182203 : CollatzResearch.WordTrace tailWord_4182203 prefixEnd_4182203 1431653555783737230152603 := by
  unfold tailWord_4182203
  simp only [CollatzResearch.WordTrace]
  refine ⟨152537474867600269252095263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101691649911733512834730175 152537474867600269252095263)
  ·
    refine ⟨228806212301400403878142895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152537474867600269252095263 228806212301400403878142895)
    ·
      refine ⟨343209318452100605817214343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228806212301400403878142895 343209318452100605817214343)
      ·
        refine ⟨514813977678150908725821515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343209318452100605817214343 514813977678150908725821515)
        ·
          refine ⟨772220966517226363088732273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514813977678150908725821515 772220966517226363088732273)
          ·
            refine ⟨579165724887919772316549205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772220966517226363088732273 579165724887919772316549205)
            ·
              refine ⟨6787098338530309831834561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 579165724887919772316549205 6787098338530309831834561)
              ·
                refine ⟨5090323753897732373875921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6787098338530309831834561 5090323753897732373875921)
                ·
                  refine ⟨3817742815423299280406941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5090323753897732373875921 3817742815423299280406941)
                  ·
                    refine ⟨1431653555783737230152603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817742815423299280406941 1431653555783737230152603)
                    ·
                      rfl

theorem cell22_4182203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 3].length) (baseStart_4182203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182203 prefixEnd_4182203 := by exact prefixLift 4182203
  have htrace : WordTrace (prefixWord ++ tailWord_4182203) baseStart_4182203 baseEnd_4182203 := by
    simpa [prefixWord, tailWord_4182203, baseEnd_4182203] using wordTrace_append hprefix tailTrace_4182203
  have hstable : (prefixWord ++ tailWord_4182203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182203).length < 2 ^ (prefixWord ++ tailWord_4182203).sum := by decide
  have hdescent : baseEnd_4182203 < baseStart_4182203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182220 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 1, 5]
def baseStart_4182220 : Nat := 118140960795 + 4182220 * 2 ^ 59
def prefixEnd_4182220 : Nat := 4983230072969 + 3 ^ 40 * 4182220 * 2
def baseEnd_4182220 : Nat := 1431659375231154852477551

theorem tailTrace_4182220 : CollatzResearch.WordTrace tailWord_4182220 prefixEnd_4182220 1431659375231154852477551 := by
  unfold tailWord_4182220
  simp only [CollatzResearch.WordTrace]
  refine ⟨76269047454269340577732057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101692063272359120770309409 76269047454269340577732057)
  ·
    refine ⟨57201785590702005433299043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76269047454269340577732057 57201785590702005433299043)
    ·
      refine ⟨85802678386053008149948565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57201785590702005433299043 85802678386053008149948565)
      ·
        refine ⟨4022000549346234757028839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 85802678386053008149948565 4022000549346234757028839)
        ·
          refine ⟨6033000824019352135543259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022000549346234757028839 6033000824019352135543259)
          ·
            refine ⟨9049501236029028203314889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6033000824019352135543259 9049501236029028203314889)
            ·
              refine ⟨6787125927021771152486167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9049501236029028203314889 6787125927021771152486167)
              ·
                refine ⟨10180688890532656728729251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6787125927021771152486167 10180688890532656728729251)
                ·
                  refine ⟨15271033335798985093093877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10180688890532656728729251 15271033335798985093093877)
                  ·
                    refine ⟨1431659375231154852477551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15271033335798985093093877 1431659375231154852477551)
                    ·
                      rfl

theorem cell22_4182220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_4182220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182220 prefixEnd_4182220 := by exact prefixLift 4182220
  have htrace : WordTrace (prefixWord ++ tailWord_4182220) baseStart_4182220 baseEnd_4182220 := by
    simpa [prefixWord, tailWord_4182220, baseEnd_4182220] using wordTrace_append hprefix tailTrace_4182220
  have hstable : (prefixWord ++ tailWord_4182220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182220).length < 2 ^ (prefixWord ++ tailWord_4182220).sum := by decide
  have hdescent : baseEnd_4182220 < baseStart_4182220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182291 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 3, 4]
def baseStart_4182291 : Nat := 118140960795 + 4182291 * 2 ^ 59
def prefixEnd_4182291 : Nat := 4983230072969 + 3 ^ 40 * 4182291 * 2
def baseEnd_4182291 : Nat := 1431683679982134333952333

theorem tailTrace_4182291 : CollatzResearch.WordTrace tailWord_4182291 prefixEnd_4182291 1431683679982134333952333 := by
  unfold tailWord_4182291
  simp only [CollatzResearch.WordTrace]
  refine ⟨152540684491281460281298727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101693789660854306854199151 152540684491281460281298727)
  ·
    refine ⟨228811026736922190421948091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152540684491281460281298727 228811026736922190421948091)
    ·
      refine ⟨343216540105383285632922137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228811026736922190421948091 343216540105383285632922137)
      ·
        refine ⟨257412405079037464224691603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343216540105383285632922137 257412405079037464224691603)
        ·
          refine ⟨386118607618556196337037405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257412405079037464224691603 386118607618556196337037405)
          ·
            refine ⟨144794477856958573626389027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386118607618556196337037405 144794477856958573626389027)
            ·
              refine ⟨217191716785437860439583541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144794477856958573626389027 217191716785437860439583541)
              ·
                refine ⟨20361723448634799416210957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217191716785437860439583541 20361723448634799416210957)
                ·
                  refine ⟨7635646293238049781079109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20361723448634799416210957 7635646293238049781079109)
                  ·
                    refine ⟨1431683679982134333952333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7635646293238049781079109 1431683679982134333952333)
                    ·
                      rfl

theorem cell22_4182291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 4].length) (baseStart_4182291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182291 prefixEnd_4182291 := by exact prefixLift 4182291
  have htrace : WordTrace (prefixWord ++ tailWord_4182291) baseStart_4182291 baseEnd_4182291 := by
    simpa [prefixWord, tailWord_4182291, baseEnd_4182291] using wordTrace_append hprefix tailTrace_4182291
  have hstable : (prefixWord ++ tailWord_4182291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182291).length < 2 ^ (prefixWord ++ tailWord_4182291).sum := by decide
  have hdescent : baseEnd_4182291 < baseStart_4182291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182336 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 1, 6]
def baseStart_4182336 : Nat := 118140960795 + 4182336 * 2 ^ 59
def prefixEnd_4182336 : Nat := 4983230072969 + 3 ^ 40 * 4182336 * 2
def baseEnd_4182336 : Nat := 1431699084401769216577195

theorem tailTrace_4182336 : CollatzResearch.WordTrace tailWord_4182336 prefixEnd_4182336 1431699084401769216577195 := by
  unfold tailWord_4182336
  simp only [CollatzResearch.WordTrace]
  refine ⟨76271162888059216483343431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101694883850745621977791241 76271162888059216483343431)
  ·
    refine ⟨114406744332088824725015147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76271162888059216483343431 114406744332088824725015147)
    ·
      refine ⟨171610116498133237087522721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114406744332088824725015147 171610116498133237087522721)
      ·
        refine ⟨128707587373599927815642041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171610116498133237087522721 128707587373599927815642041)
        ·
          refine ⟨96530690530199945861731531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128707587373599927815642041 96530690530199945861731531)
          ·
            refine ⟨144796035795299918792597297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96530690530199945861731531 144796035795299918792597297)
            ·
              refine ⟨108597026846474939094447973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144796035795299918792597297 108597026846474939094447973)
              ·
                refine ⟨20361942533714051080208995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108597026846474939094447973 20361942533714051080208995)
                ·
                  refine ⟨30542913800571076620313493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20361942533714051080208995 30542913800571076620313493)
                  ·
                    refine ⟨1431699084401769216577195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30542913800571076620313493 1431699084401769216577195)
                    ·
                      rfl

theorem cell22_4182336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_4182336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182336 prefixEnd_4182336 := by exact prefixLift 4182336
  have htrace : WordTrace (prefixWord ++ tailWord_4182336) baseStart_4182336 baseEnd_4182336 := by
    simpa [prefixWord, tailWord_4182336, baseEnd_4182336] using wordTrace_append hprefix tailTrace_4182336
  have hstable : (prefixWord ++ tailWord_4182336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182336).length < 2 ^ (prefixWord ++ tailWord_4182336).sum := by decide
  have hdescent : baseEnd_4182336 < baseStart_4182336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182353 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 2, 4]
def baseStart_4182353 : Nat := 118140960795 + 4182353 * 2 ^ 59
def prefixEnd_4182353 : Nat := 4983230072969 + 3 ^ 40 * 4182353 * 2
def baseEnd_4182353 : Nat := 1431704903849186838902143

theorem tailTrace_4182353 : CollatzResearch.WordTrace tailWord_4182353 prefixEnd_4182353 1431704903849186838902143 := by
  unfold tailWord_4182353
  simp only [CollatzResearch.WordTrace]
  refine ⟨152542945817056844870055713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101695297211371229913370475 152542945817056844870055713)
  ·
    refine ⟨114407209362792633652541785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152542945817056844870055713 114407209362792633652541785)
    ·
      refine ⟨85805407022094475239406339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114407209362792633652541785 85805407022094475239406339)
      ·
        refine ⟨128708110533141712859109509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85805407022094475239406339 128708110533141712859109509)
        ·
          refine ⟨24132770724964071161083033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128708110533141712859109509 24132770724964071161083033)
          ·
            refine ⟨18099578043723053370812275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24132770724964071161083033 18099578043723053370812275)
            ·
              refine ⟨27149367065584580056218413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18099578043723053370812275 27149367065584580056218413)
              ·
                refine ⟨10181012649594217521081905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27149367065584580056218413 10181012649594217521081905)
                ·
                  refine ⟨7635759487195663140811429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10181012649594217521081905 7635759487195663140811429)
                  ·
                    refine ⟨1431704903849186838902143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7635759487195663140811429 1431704903849186838902143)
                    ·
                      rfl

theorem cell22_4182353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 4].length) (baseStart_4182353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182353 prefixEnd_4182353 := by exact prefixLift 4182353
  have htrace : WordTrace (prefixWord ++ tailWord_4182353) baseStart_4182353 baseEnd_4182353 := by
    simpa [prefixWord, tailWord_4182353, baseEnd_4182353] using wordTrace_append hprefix tailTrace_4182353
  have hstable : (prefixWord ++ tailWord_4182353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182353).length < 2 ^ (prefixWord ++ tailWord_4182353).sum := by decide
  have hdescent : baseEnd_4182353 < baseStart_4182353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182368 : List Nat := [2, 1, 1, 3, 6, 9]
def baseStart_4182368 : Nat := 118140960795 + 4182368 * 2 ^ 59
def prefixEnd_4182368 : Nat := 4983230072969 + 3 ^ 40 * 4182368 * 2
def baseEnd_4182368 : Nat := 17675432575996688886137

theorem tailTrace_4182368 : CollatzResearch.WordTrace tailWord_4182368 prefixEnd_4182368 17675432575996688886137 := by
  unfold tailWord_4182368
  simp only [CollatzResearch.WordTrace]
  refine ⟨76271746456001251215925879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101695661941335001621234505 76271746456001251215925879)
  ·
    refine ⟨114407619684001876823888819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76271746456001251215925879 114407619684001876823888819)
    ·
      refine ⟨171611429526002815235833229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114407619684001876823888819 171611429526002815235833229)
      ·
        refine ⟨64354286072251055713437461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171611429526002815235833229 64354286072251055713437461)
        ·
          refine ⟨3016607159636768236567381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64354286072251055713437461 3016607159636768236567381)
          ·
            refine ⟨17675432575996688886137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 3016607159636768236567381 17675432575996688886137)
            ·
              rfl

theorem cell22_4182368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 9].length) (baseStart_4182368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182368 prefixEnd_4182368 := by exact prefixLift 4182368
  have htrace : WordTrace (prefixWord ++ tailWord_4182368) baseStart_4182368 baseEnd_4182368 := by
    simpa [prefixWord, tailWord_4182368, baseEnd_4182368] using wordTrace_append hprefix tailTrace_4182368
  have hstable : (prefixWord ++ tailWord_4182368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182368).length < 2 ^ (prefixWord ++ tailWord_4182368).sum := by decide
  have hdescent : baseEnd_4182368 < baseStart_4182368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182370 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_4182370 : Nat := 118140960795 + 4182370 * 2 ^ 59
def prefixEnd_4182370 : Nat := 4983230072969 + 3 ^ 40 * 4182370 * 2
def baseEnd_4182370 : Nat := 1431710723296604461227091

theorem tailTrace_4182370 : CollatzResearch.WordTrace tailWord_4182370 prefixEnd_4182370 1431710723296604461227091 := by
  unfold tailWord_4182370
  simp only [CollatzResearch.WordTrace]
  refine ⟨38135891464498814193356141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101695710571996837848949709 38135891464498814193356141)
  ·
    refine ⟨14300959299187055322508553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38135891464498814193356141 14300959299187055322508553)
    ·
      refine ⟨10725719474390291491881415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14300959299187055322508553 10725719474390291491881415)
      ·
        refine ⟨16088579211585437237822123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10725719474390291491881415 16088579211585437237822123)
        ·
          refine ⟨24132868817378155856733185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16088579211585437237822123 24132868817378155856733185)
          ·
            refine ⟨18099651613033616892549889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24132868817378155856733185 18099651613033616892549889)
            ·
              refine ⟨13574738709775212669412417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18099651613033616892549889 13574738709775212669412417)
              ·
                refine ⟨10181054032331409502059313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13574738709775212669412417 10181054032331409502059313)
                ·
                  refine ⟨7635790524248557126544485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10181054032331409502059313 7635790524248557126544485)
                  ·
                    refine ⟨1431710723296604461227091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7635790524248557126544485 1431710723296604461227091)
                    ·
                      rfl

theorem cell22_4182370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_4182370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182370 prefixEnd_4182370 := by exact prefixLift 4182370
  have htrace : WordTrace (prefixWord ++ tailWord_4182370) baseStart_4182370 baseEnd_4182370 := by
    simpa [prefixWord, tailWord_4182370, baseEnd_4182370] using wordTrace_append hprefix tailTrace_4182370
  have hstable : (prefixWord ++ tailWord_4182370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182370).length < 2 ^ (prefixWord ++ tailWord_4182370).sum := by decide
  have hdescent : baseEnd_4182370 < baseStart_4182370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182468 : List Nat := [2, 3, 3, 2, 3, 1, 1, 3, 1, 3]
def baseStart_4182468 : Nat := 118140960795 + 4182468 * 2 ^ 59
def prefixEnd_4182468 : Nat := 4983230072969 + 3 ^ 40 * 4182468 * 2
def baseEnd_4182468 : Nat := 1431744270699364872276791

theorem tailTrace_4182468 : CollatzResearch.WordTrace tailWord_4182468 prefixEnd_4182468 1431744270699364872276791 := by
  unfold tailWord_4182468
  simp only [CollatzResearch.WordTrace]
  refine ⟨76273570105820109755246029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101698093474426813006994705 76273570105820109755246029)
  ·
    refine ⟨28602588789682541158217261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76273570105820109755246029 28602588789682541158217261)
    ·
      refine ⟨10725970796130952934331473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28602588789682541158217261 10725970796130952934331473)
      ·
        refine ⟨8044478097098214700748605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10725970796130952934331473 8044478097098214700748605)
        ·
          refine ⟨3016679286411830512780727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8044478097098214700748605 3016679286411830512780727)
          ·
            refine ⟨4525018929617745769171091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016679286411830512780727 4525018929617745769171091)
            ·
              refine ⟨6787528394426618653756637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4525018929617745769171091 6787528394426618653756637)
              ·
                refine ⟨2545323147909981995158739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6787528394426618653756637 2545323147909981995158739)
                ·
                  refine ⟨3817984721864972992738109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545323147909981995158739 3817984721864972992738109)
                  ·
                    refine ⟨1431744270699364872276791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3817984721864972992738109 1431744270699364872276791)
                    ·
                      rfl

theorem cell22_4182468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_4182468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182468 prefixEnd_4182468 := by exact prefixLift 4182468
  have htrace : WordTrace (prefixWord ++ tailWord_4182468) baseStart_4182468 baseEnd_4182468 := by
    simpa [prefixWord, tailWord_4182468, baseEnd_4182468] using wordTrace_append hprefix tailTrace_4182468
  have hstable : (prefixWord ++ tailWord_4182468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182468).length < 2 ^ (prefixWord ++ tailWord_4182468).sum := by decide
  have hdescent : baseEnd_4182468 < baseStart_4182468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182473 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 1, 5]
def baseStart_4182473 : Nat := 118140960795 + 4182473 * 2 ^ 59
def prefixEnd_4182473 : Nat := 4983230072969 + 3 ^ 40 * 4182473 * 2
def baseEnd_4182473 : Nat := 1431745982301546525901775

theorem tailTrace_4182473 : CollatzResearch.WordTrace tailWord_4182473 prefixEnd_4182473 1431745982301546525901775 := by
  unfold tailWord_4182473
  simp only [CollatzResearch.WordTrace]
  refine ⟨152547322576622105364424073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101698215051081403576282715 152547322576622105364424073)
  ·
    refine ⟨114410491932466579023318055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152547322576622105364424073 114410491932466579023318055)
    ·
      refine ⟨171615737898699868534977083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114410491932466579023318055 171615737898699868534977083)
      ·
        refine ⟨257423606848049802802465625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171615737898699868534977083 257423606848049802802465625)
        ·
          refine ⟨193067705136037352101849219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257423606848049802802465625 193067705136037352101849219)
          ·
            refine ⟨289601557704056028152773829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193067705136037352101849219 289601557704056028152773829)
            ·
              refine ⟨54300292069510505278645093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289601557704056028152773829 54300292069510505278645093)
              ·
                refine ⟨10181304763033219739745955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54300292069510505278645093 10181304763033219739745955)
                ·
                  refine ⟨15271957144549829609618933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10181304763033219739745955 15271957144549829609618933)
                  ·
                    refine ⟨1431745982301546525901775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15271957144549829609618933 1431745982301546525901775)
                    ·
                      rfl

theorem cell22_4182473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 5].length) (baseStart_4182473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182473 prefixEnd_4182473 := by exact prefixLift 4182473
  have htrace : WordTrace (prefixWord ++ tailWord_4182473) baseStart_4182473 baseEnd_4182473 := by
    simpa [prefixWord, tailWord_4182473, baseEnd_4182473] using wordTrace_append hprefix tailTrace_4182473
  have hstable : (prefixWord ++ tailWord_4182473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182473).length < 2 ^ (prefixWord ++ tailWord_4182473).sum := by decide
  have hdescent : baseEnd_4182473 < baseStart_4182473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182490 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 4, 3]
def baseStart_4182490 : Nat := 118140960795 + 4182490 * 2 ^ 59
def prefixEnd_4182490 : Nat := 4983230072969 + 3 ^ 40 * 4182490 * 2
def baseEnd_4182490 : Nat := 1431751801748964148226723

theorem tailTrace_4182490 : CollatzResearch.WordTrace tailWord_4182490 prefixEnd_4182490 1431751801748964148226723 := by
  unfold tailWord_4182490
  simp only [CollatzResearch.WordTrace]
  refine ⟨38136985654390129316948231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101698628411707011511861949 38136985654390129316948231)
  ·
    refine ⟨57205478481585193975422347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38136985654390129316948231 57205478481585193975422347)
    ·
      refine ⟨85808217722377790963133521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57205478481585193975422347 85808217722377790963133521)
      ·
        refine ⟨64356163291783343222350141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85808217722377790963133521 64356163291783343222350141)
        ·
          refine ⟨24133561234418753708381303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64356163291783343222350141 24133561234418753708381303)
          ·
            refine ⟨36200341851628130562571955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24133561234418753708381303 36200341851628130562571955)
            ·
              refine ⟨54300512777442195843857933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36200341851628130562571955 54300512777442195843857933)
              ·
                refine ⟨20362692291540823441446725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54300512777442195843857933 20362692291540823441446725)
                ·
                  refine ⟨3818004804663904395271261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20362692291540823441446725 3818004804663904395271261)
                  ·
                    refine ⟨1431751801748964148226723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3818004804663904395271261 1431751801748964148226723)
                    ·
                      rfl

theorem cell22_4182490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_4182490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182490 prefixEnd_4182490 := by exact prefixLift 4182490
  have htrace : WordTrace (prefixWord ++ tailWord_4182490) baseStart_4182490 baseEnd_4182490 := by
    simpa [prefixWord, tailWord_4182490, baseEnd_4182490] using wordTrace_append hprefix tailTrace_4182490
  have hstable : (prefixWord ++ tailWord_4182490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182490).length < 2 ^ (prefixWord ++ tailWord_4182490).sum := by decide
  have hdescent : baseEnd_4182490 < baseStart_4182490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182498 : List Nat := [3, 3, 3, 2, 2, 1, 2, 1, 5]
def baseStart_4182498 : Nat := 118140960795 + 4182498 * 2 ^ 59
def prefixEnd_4182498 : Nat := 4983230072969 + 3 ^ 40 * 4182498 * 2
def baseEnd_4182498 : Nat := 477251513437484931342233

theorem tailTrace_4182498 : CollatzResearch.WordTrace tailWord_4182498 prefixEnd_4182498 477251513437484931342233 := by
  unfold tailWord_4182498
  simp only [CollatzResearch.WordTrace]
  refine ⟨38137058600382883658521037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101698822934354356422722765 38137058600382883658521037)
  ·
    refine ⟨14301396975143581371945389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38137058600382883658521037 14301396975143581371945389)
    ·
      refine ⟨5363023865678843014479521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14301396975143581371945389 5363023865678843014479521)
      ·
        refine ⟨4022267899259132260859641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5363023865678843014479521 4022267899259132260859641)
        ·
          refine ⟨3016700924444349195644731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4022267899259132260859641 3016700924444349195644731)
          ·
            refine ⟨4525051386666523793467097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3016700924444349195644731 4525051386666523793467097)
            ·
              refine ⟨3393788539999892845100323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4525051386666523793467097 3393788539999892845100323)
              ·
                refine ⟨5090682809999839267650485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3393788539999892845100323 5090682809999839267650485)
                ·
                  refine ⟨477251513437484931342233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5090682809999839267650485 477251513437484931342233)
                  ·
                    rfl

theorem cell22_4182498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_4182498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182498 prefixEnd_4182498 := by exact prefixLift 4182498
  have htrace : WordTrace (prefixWord ++ tailWord_4182498) baseStart_4182498 baseEnd_4182498 := by
    simpa [prefixWord, tailWord_4182498, baseEnd_4182498] using wordTrace_append hprefix tailTrace_4182498
  have hstable : (prefixWord ++ tailWord_4182498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182498).length < 2 ^ (prefixWord ++ tailWord_4182498).sum := by decide
  have hdescent : baseEnd_4182498 < baseStart_4182498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182541 : List Nat := [1, 7, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_4182541 : Nat := 118140960795 + 4182541 * 2 ^ 59
def prefixEnd_4182541 : Nat := 4983230072969 + 3 ^ 40 * 4182541 * 2
def baseEnd_4182541 : Nat := 1431769260091217015201567

theorem tailTrace_4182541 : CollatzResearch.WordTrace tailWord_4182541 prefixEnd_4182541 1431769260091217015201567 := by
  unfold tailWord_4182541
  simp only [CollatzResearch.WordTrace]
  refine ⟨152549802740375752977899477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101699868493583835318599651 152549802740375752977899477)
  ·
    refine ⟨3575386001727556710419519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 152549802740375752977899477 3575386001727556710419519)
    ·
      refine ⟨5363079002591335065629279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3575386001727556710419519 5363079002591335065629279)
      ·
        refine ⟨8044618503887002598443919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5363079002591335065629279 8044618503887002598443919)
        ·
          refine ⟨12066927755830503897665879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8044618503887002598443919 12066927755830503897665879)
          ·
            refine ⟨18100391633745755846498819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12066927755830503897665879 18100391633745755846498819)
            ·
              refine ⟨27150587450618633769748229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18100391633745755846498819 27150587450618633769748229)
              ·
                refine ⟨5090735146990993831827793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27150587450618633769748229 5090735146990993831827793)
                ·
                  refine ⟨3818051360243245373870845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5090735146990993831827793 3818051360243245373870845)
                  ·
                    refine ⟨1431769260091217015201567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3818051360243245373870845 1431769260091217015201567)
                    ·
                      rfl

theorem cell22_4182541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_4182541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182541 prefixEnd_4182541 := by exact prefixLift 4182541
  have htrace : WordTrace (prefixWord ++ tailWord_4182541) baseStart_4182541 baseEnd_4182541 := by
    simpa [prefixWord, tailWord_4182541, baseEnd_4182541] using wordTrace_append hprefix tailTrace_4182541
  have hstable : (prefixWord ++ tailWord_4182541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182541).length < 2 ^ (prefixWord ++ tailWord_4182541).sum := by decide
  have hdescent : baseEnd_4182541 < baseStart_4182541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182565 : List Nat := [1, 3, 1, 2, 2, 1, 4, 3, 5]
def baseStart_4182565 : Nat := 118140960795 + 4182565 * 2 ^ 59
def prefixEnd_4182565 : Nat := 4983230072969 + 3 ^ 40 * 4182565 * 2
def baseEnd_4182565 : Nat := 477259158593896317533831

theorem tailTrace_4182565 : CollatzResearch.WordTrace tailWord_4182565 prefixEnd_4182565 477259158593896317533831 := by
  unfold tailWord_4182565
  simp only [CollatzResearch.WordTrace]
  refine ⟨152550678092288805076773149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101700452061525870051182099 152550678092288805076773149)
  ·
    refine ⟨57206504284608301903789931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152550678092288805076773149 57206504284608301903789931)
    ·
      refine ⟨85809756426912452855684897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57206504284608301903789931 85809756426912452855684897)
      ·
        refine ⟨64357317320184339641763673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85809756426912452855684897 64357317320184339641763673)
        ·
          refine ⟨48267987990138254731322755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64357317320184339641763673 48267987990138254731322755)
          ·
            refine ⟨72401981985207382096984133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48267987990138254731322755 72401981985207382096984133)
            ·
              refine ⟨13575371622226384143184525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72401981985207382096984133 13575371622226384143184525)
              ·
                refine ⟨5090764358334894053694197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13575371622226384143184525 5090764358334894053694197)
                ·
                  refine ⟨477259158593896317533831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5090764358334894053694197 477259158593896317533831)
                  ·
                    rfl

theorem cell22_4182565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_4182565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182565 prefixEnd_4182565 := by exact prefixLift 4182565
  have htrace : WordTrace (prefixWord ++ tailWord_4182565) baseStart_4182565 baseEnd_4182565 := by
    simpa [prefixWord, tailWord_4182565, baseEnd_4182565] using wordTrace_append hprefix tailTrace_4182565
  have hstable : (prefixWord ++ tailWord_4182565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182565).length < 2 ^ (prefixWord ++ tailWord_4182565).sum := by decide
  have hdescent : baseEnd_4182565 < baseStart_4182565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182573 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_4182573 : Nat := 118140960795 + 4182573 * 2 ^ 59
def prefixEnd_4182573 : Nat := 4983230072969 + 3 ^ 40 * 4182573 * 2
def baseEnd_4182573 : Nat := 1431780214345179598401469

theorem tailTrace_4182573 : CollatzResearch.WordTrace tailWord_4182573 prefixEnd_4182573 1431780214345179598401469 := by
  unfold tailWord_4182573
  simp only [CollatzResearch.WordTrace]
  refine ⟨152550969876259822443064373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101700646584173214962042915 152550969876259822443064373)
  ·
    refine ⟨14301653425899358354037285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152550969876259822443064373 14301653425899358354037285)
    ·
      refine ⟨2681560017356129691381991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14301653425899358354037285 2681560017356129691381991)
      ·
        refine ⟨4022340026034194537072987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2681560017356129691381991 4022340026034194537072987)
        ·
          refine ⟨6033510039051291805609481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4022340026034194537072987 6033510039051291805609481)
          ·
            refine ⟨4525132529288468854207111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6033510039051291805609481 4525132529288468854207111)
            ·
              refine ⟨6787698793932703281310667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4525132529288468854207111 6787698793932703281310667)
              ·
                refine ⟨10181548190899054921966001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6787698793932703281310667 10181548190899054921966001)
                ·
                  refine ⟨7636161143174291191474501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10181548190899054921966001 7636161143174291191474501)
                  ·
                    refine ⟨1431780214345179598401469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7636161143174291191474501 1431780214345179598401469)
                    ·
                      rfl

theorem cell22_4182573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_4182573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182573 prefixEnd_4182573 := by exact prefixLift 4182573
  have htrace : WordTrace (prefixWord ++ tailWord_4182573) baseStart_4182573 baseEnd_4182573 := by
    simpa [prefixWord, tailWord_4182573, baseEnd_4182573] using wordTrace_append hprefix tailTrace_4182573
  have hstable : (prefixWord ++ tailWord_4182573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182573).length < 2 ^ (prefixWord ++ tailWord_4182573).sum := by decide
  have hdescent : baseEnd_4182573 < baseStart_4182573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182629 : List Nat := [1, 3, 1, 3, 4, 1, 2, 2, 1, 4]
def baseStart_4182629 : Nat := 118140960795 + 4182629 * 2 ^ 59
def prefixEnd_4182629 : Nat := 4983230072969 + 3 ^ 40 * 4182629 * 2
def baseEnd_4182629 : Nat := 1431799384289614119001297

theorem tailTrace_4182629 : CollatzResearch.WordTrace tailWord_4182629 prefixEnd_4182629 1431799384289614119001297 := by
  unfold tailWord_4182629
  simp only [CollatzResearch.WordTrace]
  refine ⟨152553012364056944007102941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101702008242704629338068627 152553012364056944007102941)
  ·
    refine ⟨57207379636521354002663603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152553012364056944007102941 57207379636521354002663603)
    ·
      refine ⟨85811069454782031003995405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57207379636521354002663603 85811069454782031003995405)
      ·
        refine ⟨32179151045543261626498277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85811069454782031003995405 32179151045543261626498277)
        ·
          refine ⟨6033590821039361554968427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32179151045543261626498277 6033590821039361554968427)
          ·
            refine ⟨9050386231559042332452641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6033590821039361554968427 9050386231559042332452641)
            ·
              refine ⟨6787789673669281749339481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9050386231559042332452641 6787789673669281749339481)
              ·
                refine ⟨5090842255251961312004611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6787789673669281749339481 5090842255251961312004611)
                ·
                  refine ⟨7636263382877941968006917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5090842255251961312004611 7636263382877941968006917)
                  ·
                    refine ⟨1431799384289614119001297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7636263382877941968006917 1431799384289614119001297)
                    ·
                      rfl

theorem cell22_4182629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_4182629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182629 prefixEnd_4182629 := by exact prefixLift 4182629
  have htrace : WordTrace (prefixWord ++ tailWord_4182629) baseStart_4182629 baseEnd_4182629 := by
    simpa [prefixWord, tailWord_4182629, baseEnd_4182629] using wordTrace_append hprefix tailTrace_4182629
  have hstable : (prefixWord ++ tailWord_4182629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182629).length < 2 ^ (prefixWord ++ tailWord_4182629).sum := by decide
  have hdescent : baseEnd_4182629 < baseStart_4182629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182657 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 2, 4]
def baseStart_4182657 : Nat := 118140960795 + 4182657 * 2 ^ 59
def prefixEnd_4182657 : Nat := 4983230072969 + 3 ^ 40 * 4182657 * 2
def baseEnd_4182657 : Nat := 1431808969261831379301211

theorem tailTrace_4182657 : CollatzResearch.WordTrace tailWord_4182657 prefixEnd_4182657 1431808969261831379301211 := by
  unfold tailWord_4182657
  simp only [CollatzResearch.WordTrace]
  refine ⟨152554033607955504789122225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101702689071970336526081483 152554033607955504789122225)
  ·
    refine ⟨114415525205966628591841669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152554033607955504789122225 114415525205966628591841669)
    ·
      refine ⟨21452910976118742860970313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114415525205966628591841669 21452910976118742860970313)
      ·
        refine ⟨16089683232089057145727735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21452910976118742860970313 16089683232089057145727735)
        ·
          refine ⟨24134524848133585718591603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16089683232089057145727735 24134524848133585718591603)
          ·
            refine ⟨36201787272200378577887405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24134524848133585718591603 36201787272200378577887405)
            ·
              refine ⟨13575670227075141966707777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36201787272200378577887405 13575670227075141966707777)
              ·
                refine ⟨10181752670306356475030833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13575670227075141966707777 10181752670306356475030833)
                ·
                  refine ⟨7636314502729767356273125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10181752670306356475030833 7636314502729767356273125)
                  ·
                    refine ⟨1431808969261831379301211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7636314502729767356273125 1431808969261831379301211)
                    ·
                      rfl

theorem cell22_4182657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_4182657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182657 prefixEnd_4182657 := by exact prefixLift 4182657
  have htrace : WordTrace (prefixWord ++ tailWord_4182657) baseStart_4182657 baseEnd_4182657 := by
    simpa [prefixWord, tailWord_4182657, baseEnd_4182657] using wordTrace_append hprefix tailTrace_4182657
  have hstable : (prefixWord ++ tailWord_4182657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182657).length < 2 ^ (prefixWord ++ tailWord_4182657).sum := by decide
  have hdescent : baseEnd_4182657 < baseStart_4182657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182676 : List Nat := [2, 4, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_4182676 : Nat := 118140960795 + 4182676 * 2 ^ 59
def prefixEnd_4182676 : Nat := 4983230072969 + 3 ^ 40 * 4182676 * 2
def baseEnd_4182676 : Nat := 1431815473350121663076153

theorem tailTrace_4182676 : CollatzResearch.WordTrace tailWord_4182676 prefixEnd_4182676 1431815473350121663076153 := by
  unfold tailWord_4182676
  simp only [CollatzResearch.WordTrace]
  refine ⟨76277363297443335517031941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101703151063257780689375921 76277363297443335517031941)
  ·
    refine ⟨14302005618270625409443489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76277363297443335517031941 14302005618270625409443489)
    ·
      refine ⟨10726504213702969057082617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14302005618270625409443489 10726504213702969057082617)
      ·
        refine ⟨8044878160277226792811963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10726504213702969057082617 8044878160277226792811963)
        ·
          refine ⟨12067317240415840189217945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8044878160277226792811963 12067317240415840189217945)
          ·
            refine ⟨9050487930311880141913459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12067317240415840189217945 9050487930311880141913459)
            ·
              refine ⟨13575731895467820212870189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9050487930311880141913459 13575731895467820212870189)
              ·
                refine ⟨5090899460800432579826321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13575731895467820212870189 5090899460800432579826321)
                ·
                  refine ⟨3818174595600324434869741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5090899460800432579826321 3818174595600324434869741)
                  ·
                    refine ⟨1431815473350121663076153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3818174595600324434869741 1431815473350121663076153)
                    ·
                      rfl

theorem cell22_4182676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_4182676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182676 prefixEnd_4182676 := by exact prefixLift 4182676
  have htrace : WordTrace (prefixWord ++ tailWord_4182676) baseStart_4182676 baseEnd_4182676 := by
    simpa [prefixWord, tailWord_4182676, baseEnd_4182676] using wordTrace_append hprefix tailTrace_4182676
  have hstable : (prefixWord ++ tailWord_4182676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182676).length < 2 ^ (prefixWord ++ tailWord_4182676).sum := by decide
  have hdescent : baseEnd_4182676 < baseStart_4182676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182704 : List Nat := [2, 1, 1, 1, 2, 1, 3, 7, 1, 3]
def baseStart_4182704 : Nat := 118140960795 + 4182704 * 2 ^ 59
def prefixEnd_4182704 : Nat := 4983230072969 + 3 ^ 40 * 4182704 * 2
def baseEnd_4182704 : Nat := 1431825058322338923376067

theorem tailTrace_4182704 : CollatzResearch.WordTrace tailWord_4182704 prefixEnd_4182704 1431825058322338923376067 := by
  unfold tailWord_4182704
  simp only [CollatzResearch.WordTrace]
  refine ⟨76277873919392615908041583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101703831892523487877388777 76277873919392615908041583)
  ·
    refine ⟨114416810879088923862062375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76277873919392615908041583 114416810879088923862062375)
    ·
      refine ⟨171625216318633385793093563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114416810879088923862062375 171625216318633385793093563)
      ·
        refine ⟨257437824477950078689640345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171625216318633385793093563 257437824477950078689640345)
        ·
          refine ⟨193078368358462559017230259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257437824477950078689640345 193078368358462559017230259)
          ·
            refine ⟨289617552537693838525845389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193078368358462559017230259 289617552537693838525845389)
            ·
              refine ⟨108606582201635189447192021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289617552537693838525845389 108606582201635189447192021)
              ·
                refine ⟨2545466770350824752668563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 108606582201635189447192021 2545466770350824752668563)
                ·
                  refine ⟨3818200155526237129002845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545466770350824752668563 3818200155526237129002845)
                  ·
                    refine ⟨1431825058322338923376067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3818200155526237129002845 1431825058322338923376067)
                    ·
                      rfl

theorem cell22_4182704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 7, 1, 3].length) (baseStart_4182704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182704 prefixEnd_4182704 := by exact prefixLift 4182704
  have htrace : WordTrace (prefixWord ++ tailWord_4182704) baseStart_4182704 baseEnd_4182704 := by
    simpa [prefixWord, tailWord_4182704, baseEnd_4182704] using wordTrace_append hprefix tailTrace_4182704
  have hstable : (prefixWord ++ tailWord_4182704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182704).length < 2 ^ (prefixWord ++ tailWord_4182704).sum := by decide
  have hdescent : baseEnd_4182704 < baseStart_4182704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182717 : List Nat := [1, 4, 1, 2, 1, 3, 1, 4, 5]
def baseStart_4182717 : Nat := 118140960795 + 4182717 * 2 ^ 59
def prefixEnd_4182717 : Nat := 4983230072969 + 3 ^ 40 * 4182717 * 2
def baseEnd_4182717 : Nat := 477276502829337074267009

theorem tailTrace_4182717 : CollatzResearch.WordTrace tailWord_4182717 prefixEnd_4182717 477276502829337074267009 := by
  unfold tailWord_4182717
  simp only [CollatzResearch.WordTrace]
  refine ⟨152556221987738135036306405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101704147991825423357537603 152556221987738135036306405)
  ·
    refine ⟨28604291622700900319307451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152556221987738135036306405 28604291622700900319307451)
    ·
      refine ⟨42906437434051350478961177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28604291622700900319307451 42906437434051350478961177)
      ·
        refine ⟨32179828075538512859220883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42906437434051350478961177 32179828075538512859220883)
        ·
          refine ⟨48269742113307769288831325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32179828075538512859220883 48269742113307769288831325)
          ·
            refine ⟨18101153292490413483311747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48269742113307769288831325 18101153292490413483311747)
            ·
              refine ⟨27151729938735620224967621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18101153292490413483311747 27151729938735620224967621)
              ·
                refine ⟨5090949363512928792181429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27151729938735620224967621 5090949363512928792181429)
                ·
                  refine ⟨477276502829337074267009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5090949363512928792181429 477276502829337074267009)
                  ·
                    rfl

theorem cell22_4182717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_4182717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182717 prefixEnd_4182717 := by exact prefixLift 4182717
  have htrace : WordTrace (prefixWord ++ tailWord_4182717) baseStart_4182717 baseEnd_4182717 := by
    simpa [prefixWord, tailWord_4182717, baseEnd_4182717] using wordTrace_append hprefix tailTrace_4182717
  have hstable : (prefixWord ++ tailWord_4182717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182717).length < 2 ^ (prefixWord ++ tailWord_4182717).sum := by decide
  have hdescent : baseEnd_4182717 < baseStart_4182717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182732 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_4182732 : Nat := 118140960795 + 4182732 * 2 ^ 59
def prefixEnd_4182732 : Nat := 4983230072969 + 3 ^ 40 * 4182732 * 2
def baseEnd_4182732 : Nat := 1431834643294556183675981

theorem tailTrace_4182732 : CollatzResearch.WordTrace tailWord_4182732 prefixEnd_4182732 1431834643294556183675981 := by
  unfold tailWord_4182732
  simp only [CollatzResearch.WordTrace]
  refine ⟨76278384541341896299051225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101704512721789195065401633 76278384541341896299051225)
  ·
    refine ⟨57208788406006422224288419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76278384541341896299051225 57208788406006422224288419)
    ·
      refine ⟨85813182609009633336432629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57208788406006422224288419 85813182609009633336432629)
      ·
        refine ⟨8044985869594653125290559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85813182609009633336432629 8044985869594653125290559)
        ·
          refine ⟨12067478804391979687935839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8044985869594653125290559 12067478804391979687935839)
          ·
            refine ⟨18101218206587969531903759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12067478804391979687935839 18101218206587969531903759)
            ·
              refine ⟨27151827309881954297855639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18101218206587969531903759 27151827309881954297855639)
              ·
                refine ⟨40727740964822931446783459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27151827309881954297855639 40727740964822931446783459)
                ·
                  refine ⟨61091611447234397170175189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40727740964822931446783459 61091611447234397170175189)
                  ·
                    refine ⟨1431834643294556183675981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61091611447234397170175189 1431834643294556183675981)
                    ·
                      rfl

theorem cell22_4182732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_4182732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182732 prefixEnd_4182732 := by exact prefixLift 4182732
  have htrace : WordTrace (prefixWord ++ tailWord_4182732) baseStart_4182732 baseEnd_4182732 := by
    simpa [prefixWord, tailWord_4182732, baseEnd_4182732] using wordTrace_append hprefix tailTrace_4182732
  have hstable : (prefixWord ++ tailWord_4182732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182732).length < 2 ^ (prefixWord ++ tailWord_4182732).sum := by decide
  have hdescent : baseEnd_4182732 < baseStart_4182732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182792 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 1, 6]
def baseStart_4182792 : Nat := 118140960795 + 4182792 * 2 ^ 59
def prefixEnd_4182792 : Nat := 4983230072969 + 3 ^ 40 * 4182792 * 2
def baseEnd_4182792 : Nat := 1431855182520736027175797

theorem tailTrace_4182792 : CollatzResearch.WordTrace tailWord_4182792 prefixEnd_4182792 1431855182520736027175797 := by
  unfold tailWord_4182792
  simp only [CollatzResearch.WordTrace]
  refine ⟨76279478731233211422643315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101705971641644281896857753 76279478731233211422643315)
  ·
    refine ⟨114419218096849817133964973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76279478731233211422643315 114419218096849817133964973)
    ·
      refine ⟨42907206786318681425236865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114419218096849817133964973 42907206786318681425236865)
      ·
        refine ⟨32180405089739011068927649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42907206786318681425236865 32180405089739011068927649)
        ·
          refine ⟨24135303817304258301695737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32180405089739011068927649 24135303817304258301695737)
          ·
            refine ⟨18101477862978193726271803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24135303817304258301695737 18101477862978193726271803)
            ·
              refine ⟨27152216794467290589407705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18101477862978193726271803 27152216794467290589407705)
              ·
                refine ⟨20364162595850467942055779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27152216794467290589407705 20364162595850467942055779)
                ·
                  refine ⟨30546243893775701913083669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20364162595850467942055779 30546243893775701913083669)
                  ·
                    refine ⟨1431855182520736027175797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30546243893775701913083669 1431855182520736027175797)
                    ·
                      rfl

theorem cell22_4182792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_4182792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182792 prefixEnd_4182792 := by exact prefixLift 4182792
  have htrace : WordTrace (prefixWord ++ tailWord_4182792) baseStart_4182792 baseEnd_4182792 := by
    simpa [prefixWord, tailWord_4182792, baseEnd_4182792] using wordTrace_append hprefix tailTrace_4182792
  have hstable : (prefixWord ++ tailWord_4182792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182792).length < 2 ^ (prefixWord ++ tailWord_4182792).sum := by decide
  have hdescent : baseEnd_4182792 < baseStart_4182792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182845 : List Nat := [1, 4, 1, 4, 2, 2, 2, 1, 2, 3]
def baseStart_4182845 : Nat := 118140960795 + 4182845 * 2 ^ 59
def prefixEnd_4182845 : Nat := 4983230072969 + 3 ^ 40 * 4182845 * 2
def baseEnd_4182845 : Nat := 1431873325503861555600635

theorem tailTrace_4182845 : CollatzResearch.WordTrace tailWord_4182845 prefixEnd_4182845 1431873325503861555600635 := by
  unfold tailWord_4182845
  simp only [CollatzResearch.WordTrace]
  refine ⟨152560890531274412896965989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101707260354182941931310659 152560890531274412896965989)
  ·
    refine ⟨28605166974613952418181123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152560890531274412896965989 28605166974613952418181123)
    ·
      refine ⟨42907750461920928627271685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28605166974613952418181123 42907750461920928627271685)
      ·
        refine ⟨8045203211610174117613441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42907750461920928627271685 8045203211610174117613441)
        ·
          refine ⟨6033902408707630588210081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8045203211610174117613441 6033902408707630588210081)
          ·
            refine ⟨4525426806530722941157561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6033902408707630588210081 4525426806530722941157561)
            ·
              refine ⟨3394070104898042205868171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4525426806530722941157561 3394070104898042205868171)
              ·
                refine ⟨5091105157347063308802257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394070104898042205868171 5091105157347063308802257)
                ·
                  refine ⟨3818328868010297481601693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5091105157347063308802257 3818328868010297481601693)
                  ·
                    refine ⟨1431873325503861555600635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3818328868010297481601693 1431873325503861555600635)
                    ·
                      rfl

theorem cell22_4182845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_4182845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182845 prefixEnd_4182845 := by exact prefixLift 4182845
  have htrace : WordTrace (prefixWord ++ tailWord_4182845) baseStart_4182845 baseEnd_4182845 := by
    simpa [prefixWord, tailWord_4182845, baseEnd_4182845] using wordTrace_append hprefix tailTrace_4182845
  have hstable : (prefixWord ++ tailWord_4182845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182845).length < 2 ^ (prefixWord ++ tailWord_4182845).sum := by decide
  have hdescent : baseEnd_4182845 < baseStart_4182845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182929 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 4, 3]
def baseStart_4182929 : Nat := 118140960795 + 4182929 * 2 ^ 59
def prefixEnd_4182929 : Nat := 4983230072969 + 3 ^ 40 * 4182929 * 2
def baseEnd_4182929 : Nat := 1431902080420513336500377

theorem tailTrace_4182929 : CollatzResearch.WordTrace tailWord_4182929 prefixEnd_4182929 1431902080420513336500377 := by
  unfold tailWord_4182929
  simp only [CollatzResearch.WordTrace]
  refine ⟨152563954262970095243023841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101709302841980063495349227 152563954262970095243023841)
  ·
    refine ⟨114422965697227571432267881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152563954262970095243023841 114422965697227571432267881)
    ·
      refine ⟨85817224272920678574200911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114422965697227571432267881 85817224272920678574200911)
      ·
        refine ⟨128725836409381017861301367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85817224272920678574200911 128725836409381017861301367)
        ·
          refine ⟨193088754614071526791952051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128725836409381017861301367 193088754614071526791952051)
          ·
            refine ⟨289633131921107290187928077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193088754614071526791952051 289633131921107290187928077)
            ·
              refine ⟨108612424470415233820473029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289633131921107290187928077 108612424470415233820473029)
              ·
                refine ⟨20364829588202856341338693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108612424470415233820473029 20364829588202856341338693)
                ·
                  refine ⟨3818405547788035564001005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20364829588202856341338693 3818405547788035564001005)
                  ·
                    refine ⟨1431902080420513336500377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3818405547788035564001005 1431902080420513336500377)
                    ·
                      rfl

theorem cell22_4182929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 3].length) (baseStart_4182929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182929 prefixEnd_4182929 := by exact prefixLift 4182929
  have htrace : WordTrace (prefixWord ++ tailWord_4182929) baseStart_4182929 baseEnd_4182929 := by
    simpa [prefixWord, tailWord_4182929, baseEnd_4182929] using wordTrace_append hprefix tailTrace_4182929
  have hstable : (prefixWord ++ tailWord_4182929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182929).length < 2 ^ (prefixWord ++ tailWord_4182929).sum := by decide
  have hdescent : baseEnd_4182929 < baseStart_4182929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182933 : List Nat := [1, 3, 2, 1, 1, 6, 2, 1, 1, 4]
def baseStart_4182933 : Nat := 118140960795 + 4182933 * 2 ^ 59
def prefixEnd_4182933 : Nat := 4983230072969 + 3 ^ 40 * 4182933 * 2
def baseEnd_4182933 : Nat := 1431903449702258659400365

theorem tailTrace_4182933 : CollatzResearch.WordTrace tailWord_4182933 prefixEnd_4182933 1431903449702258659400365 := by
  unfold tailWord_4182933
  simp only [CollatzResearch.WordTrace]
  refine ⟨152564100154955603926169453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101709400103303735950779635 152564100154955603926169453)
  ·
    refine ⟨57211537558108351472313545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152564100154955603926169453 57211537558108351472313545)
    ·
      refine ⟨42908653168581263604235159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57211537558108351472313545 42908653168581263604235159)
      ·
        refine ⟨64362979752871895406352739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42908653168581263604235159 64362979752871895406352739)
        ·
          refine ⟨96544469629307843109529109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64362979752871895406352739 96544469629307843109529109)
          ·
            refine ⟨4525522013873805145759177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96544469629307843109529109 4525522013873805145759177)
            ·
              refine ⟨3394141510405353859319383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4525522013873805145759177 3394141510405353859319383)
              ·
                refine ⟨5091212265608030788979075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394141510405353859319383 5091212265608030788979075)
                ·
                  refine ⟨7636818398412046183468613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091212265608030788979075 7636818398412046183468613)
                  ·
                    refine ⟨1431903449702258659400365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7636818398412046183468613 1431903449702258659400365)
                    ·
                      rfl

theorem cell22_4182933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_4182933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182933 prefixEnd_4182933 := by exact prefixLift 4182933
  have htrace : WordTrace (prefixWord ++ tailWord_4182933) baseStart_4182933 baseEnd_4182933 := by
    simpa [prefixWord, tailWord_4182933, baseEnd_4182933] using wordTrace_append hprefix tailTrace_4182933
  have hstable : (prefixWord ++ tailWord_4182933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182933).length < 2 ^ (prefixWord ++ tailWord_4182933).sum := by decide
  have hdescent : baseEnd_4182933 < baseStart_4182933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182944 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 2, 4]
def baseStart_4182944 : Nat := 118140960795 + 4182944 * 2 ^ 59
def prefixEnd_4182944 : Nat := 4983230072969 + 3 ^ 40 * 4182944 * 2
def baseEnd_4182944 : Nat := 1431907215227058297375331

theorem tailTrace_4182944 : CollatzResearch.WordTrace tailWord_4182944 prefixEnd_4182944 1431907215227058297375331 := by
  unfold tailWord_4182944
  simp only [CollatzResearch.WordTrace]
  refine ⟨76282250678957876402409943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101709667571943835203213257 76282250678957876402409943)
  ·
    refine ⟨114423376018436814603614915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76282250678957876402409943 114423376018436814603614915)
    ·
      refine ⟨171635064027655221905422373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114423376018436814603614915 171635064027655221905422373)
      ·
        refine ⟨32181574505185354107266695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171635064027655221905422373 32181574505185354107266695)
        ·
          refine ⟨48272361757778031160900043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32181574505185354107266695 48272361757778031160900043)
          ·
            refine ⟨72408542636667046741350065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48272361757778031160900043 72408542636667046741350065)
            ·
              refine ⟨54306406977500285056012549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72408542636667046741350065 54306406977500285056012549)
              ·
                refine ⟨10182451308281303448002353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54306406977500285056012549 10182451308281303448002353)
                ·
                  refine ⟨7636838481210977586001765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10182451308281303448002353 7636838481210977586001765)
                  ·
                    refine ⟨1431907215227058297375331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7636838481210977586001765 1431907215227058297375331)
                    ·
                      rfl

theorem cell22_4182944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_4182944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182944 prefixEnd_4182944 := by exact prefixLift 4182944
  have htrace : WordTrace (prefixWord ++ tailWord_4182944) baseStart_4182944 baseEnd_4182944 := by
    simpa [prefixWord, tailWord_4182944, baseEnd_4182944] using wordTrace_append hprefix tailTrace_4182944
  have hstable : (prefixWord ++ tailWord_4182944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182944).length < 2 ^ (prefixWord ++ tailWord_4182944).sum := by decide
  have hdescent : baseEnd_4182944 < baseStart_4182944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182974 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_4182974 : Nat := 118140960795 + 4182974 * 2 ^ 59
def prefixEnd_4182974 : Nat := 4983230072969 + 3 ^ 40 * 4182974 * 2
def baseEnd_4182974 : Nat := 1431917484840148219125239

theorem tailTrace_4182974 : CollatzResearch.WordTrace tailWord_4182974 prefixEnd_4182974 1431917484840148219125239 := by
  unfold tailWord_4182974
  simp only [CollatzResearch.WordTrace]
  refine ⟨19070699443475883491051497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101710397031871378618941317 19070699443475883491051497)
  ·
    refine ⟨14303024582606912618288623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19070699443475883491051497 14303024582606912618288623)
    ·
      refine ⟨21454536873910368927432935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14303024582606912618288623 21454536873910368927432935)
      ·
        refine ⟨32181805310865553391149403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21454536873910368927432935 32181805310865553391149403)
        ·
          refine ⟨48272707966298330086724105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32181805310865553391149403 48272707966298330086724105)
          ·
            refine ⟨36204530974723747565043079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48272707966298330086724105 36204530974723747565043079)
            ·
              refine ⟨54306796462085621347564619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36204530974723747565043079 54306796462085621347564619)
              ·
                refine ⟨81460194693128432021346929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54306796462085621347564619 81460194693128432021346929)
                ·
                  refine ⟨61095146019846324016010197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81460194693128432021346929 61095146019846324016010197)
                  ·
                    refine ⟨1431917484840148219125239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61095146019846324016010197 1431917484840148219125239)
                    ·
                      rfl

theorem cell22_4182974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_4182974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182974 prefixEnd_4182974 := by exact prefixLift 4182974
  have htrace : WordTrace (prefixWord ++ tailWord_4182974) baseStart_4182974 baseEnd_4182974 := by
    simpa [prefixWord, tailWord_4182974, baseEnd_4182974] using wordTrace_append hprefix tailTrace_4182974
  have hstable : (prefixWord ++ tailWord_4182974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182974).length < 2 ^ (prefixWord ++ tailWord_4182974).sum := by decide
  have hdescent : baseEnd_4182974 < baseStart_4182974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4182976 : List Nat := [2, 1, 1, 2, 3, 5, 2, 6]
def baseStart_4182976 : Nat := 118140960795 + 4182976 * 2 ^ 59
def prefixEnd_4182976 : Nat := 4983230072969 + 3 ^ 40 * 4182976 * 2
def baseEnd_4182976 : Nat := 159102018831224542286137

theorem tailTrace_4182976 : CollatzResearch.WordTrace tailWord_4182976 prefixEnd_4182976 159102018831224542286137 := by
  unfold tailWord_4182976
  simp only [CollatzResearch.WordTrace]
  refine ⟨76282834246899911134992391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101710445662533214846656521 76282834246899911134992391)
  ·
    refine ⟨114424251370349866702488587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76282834246899911134992391 114424251370349866702488587)
    ·
      refine ⟨171636377055524800053732881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114424251370349866702488587 171636377055524800053732881)
      ·
        refine ⟨128727282791643600040299661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171636377055524800053732881 128727282791643600040299661)
        ·
          refine ⟨48272731046866350015112373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128727282791643600040299661 48272731046866350015112373)
          ·
            refine ⟨4525568535643720313916785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48272731046866350015112373 4525568535643720313916785)
            ·
              refine ⟨3394176401732790235437589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4525568535643720313916785 3394176401732790235437589)
              ·
                refine ⟨159102018831224542286137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3394176401732790235437589 159102018831224542286137)
                ·
                  rfl

theorem cell22_4182976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 6].length) (baseStart_4182976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4182976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4182976 prefixEnd_4182976 := by exact prefixLift 4182976
  have htrace : WordTrace (prefixWord ++ tailWord_4182976) baseStart_4182976 baseEnd_4182976 := by
    simpa [prefixWord, tailWord_4182976, baseEnd_4182976] using wordTrace_append hprefix tailTrace_4182976
  have hstable : (prefixWord ++ tailWord_4182976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4182976).length < 2 ^ (prefixWord ++ tailWord_4182976).sum := by decide
  have hdescent : baseEnd_4182976 < baseStart_4182976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4182976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183096 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 1, 6]
def baseStart_4183096 : Nat := 118140960795 + 4183096 * 2 ^ 59
def prefixEnd_4183096 : Nat := 4983230072969 + 3 ^ 40 * 4183096 * 2
def baseEnd_4183096 : Nat := 1431959247933380567574865

theorem tailTrace_4183096 : CollatzResearch.WordTrace tailWord_4183096 prefixEnd_4183096 1431959247933380567574865 := by
  unfold tailWord_4183096
  simp only [CollatzResearch.WordTrace]
  refine ⟨76285022626682541382176571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101713363502243388509568761 76285022626682541382176571)
  ·
    refine ⟨114427533940023812073264857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76285022626682541382176571 114427533940023812073264857)
    ·
      refine ⟨85820650455017859054948643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114427533940023812073264857 85820650455017859054948643)
      ·
        refine ⟨128730975682526788582422965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85820650455017859054948643 128730975682526788582422965)
        ·
          refine ⟨12068528970236886429602153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128730975682526788582422965 12068528970236886429602153)
          ·
            refine ⟨9051396727677664822201615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12068528970236886429602153 9051396727677664822201615)
            ·
              refine ⟨13577095091516497233302423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9051396727677664822201615 13577095091516497233302423)
              ·
                refine ⟨20365642637274745849953635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13577095091516497233302423 20365642637274745849953635)
                ·
                  refine ⟨30548463955912118774930453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20365642637274745849953635 30548463955912118774930453)
                  ·
                    refine ⟨1431959247933380567574865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30548463955912118774930453 1431959247933380567574865)
                    ·
                      rfl

theorem cell22_4183096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_4183096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183096 prefixEnd_4183096 := by exact prefixLift 4183096
  have htrace : WordTrace (prefixWord ++ tailWord_4183096) baseStart_4183096 baseEnd_4183096 := by
    simpa [prefixWord, tailWord_4183096, baseEnd_4183096] using wordTrace_append hprefix tailTrace_4183096
  have hstable : (prefixWord ++ tailWord_4183096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183096).length < 2 ^ (prefixWord ++ tailWord_4183096).sum := by decide
  have hdescent : baseEnd_4183096 < baseStart_4183096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183102 : List Nat := [4, 2, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_4183102 : Nat := 118140960795 + 4183102 * 2 ^ 59
def prefixEnd_4183102 : Nat := 4983230072969 + 3 ^ 40 * 4183102 * 2
def baseEnd_4183102 : Nat := 1431961301855998551924847

theorem tailTrace_4183102 : CollatzResearch.WordTrace tailWord_4183102 prefixEnd_4183102 1431961301855998551924847 := by
  unfold tailWord_4183102
  simp only [CollatzResearch.WordTrace]
  refine ⟨19071283011417918223633945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101713509394228897192714373 19071283011417918223633945)
  ·
    refine ⟨14303462258563438667725459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19071283011417918223633945 14303462258563438667725459)
    ·
      refine ⟨21455193387845158001588189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14303462258563438667725459 21455193387845158001588189)
      ·
        refine ⟨8045697520441934250595571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21455193387845158001588189 8045697520441934250595571)
        ·
          refine ⟨12068546280662901375893357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8045697520441934250595571 12068546280662901375893357)
          ·
            refine ⟨4525704855248588015960009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12068546280662901375893357 4525704855248588015960009)
            ·
              refine ⟨3394278641436441011970007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4525704855248588015960009 3394278641436441011970007)
              ·
                refine ⟨5091417962154661517955011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394278641436441011970007 5091417962154661517955011)
                ·
                  refine ⟨7637126943231992276932517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091417962154661517955011 7637126943231992276932517)
                  ·
                    refine ⟨1431961301855998551924847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7637126943231992276932517 1431961301855998551924847)
                    ·
                      rfl

theorem cell22_4183102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_4183102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183102 prefixEnd_4183102 := by exact prefixLift 4183102
  have htrace : WordTrace (prefixWord ++ tailWord_4183102) baseStart_4183102 baseEnd_4183102 := by
    simpa [prefixWord, tailWord_4183102, baseEnd_4183102] using wordTrace_append hprefix tailTrace_4183102
  have hstable : (prefixWord ++ tailWord_4183102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183102).length < 2 ^ (prefixWord ++ tailWord_4183102).sum := by decide
  have hdescent : baseEnd_4183102 < baseStart_4183102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183143 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 3, 3]
def baseStart_4183143 : Nat := 118140960795 + 4183143 * 2 ^ 59
def prefixEnd_4183143 : Nat := 4983230072969 + 3 ^ 40 * 4183143 * 2
def baseEnd_4183143 : Nat := 1431975336993888111649721

theorem tailTrace_4183143 : CollatzResearch.WordTrace tailWord_4183143 prefixEnd_4183143 1431975336993888111649721 := by
  unfold tailWord_4183143
  simp only [CollatzResearch.WordTrace]
  refine ⟨152571759484194809791314083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101714506322796539860876055 152571759484194809791314083)
  ·
    refine ⟨228857639226292214686971125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152571759484194809791314083 228857639226292214686971125)
    ·
      refine ⟨21455403677464895126903543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228857639226292214686971125 21455403677464895126903543)
      ·
        refine ⟨32183105516197342690355315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21455403677464895126903543 32183105516197342690355315)
        ·
          refine ⟨48274658274296014035532973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32183105516197342690355315 48274658274296014035532973)
          ·
            refine ⟨18102996852861005263324865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48274658274296014035532973 18102996852861005263324865)
            ·
              refine ⟨13577247639645753947493649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18102996852861005263324865 13577247639645753947493649)
              ·
                refine ⟨10182935729734315460620237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13577247639645753947493649 10182935729734315460620237)
                ·
                  refine ⟨3818600898650368297732589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10182935729734315460620237 3818600898650368297732589)
                  ·
                    refine ⟨1431975336993888111649721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3818600898650368297732589 1431975336993888111649721)
                    ·
                      rfl

theorem cell22_4183143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_4183143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183143 prefixEnd_4183143 := by exact prefixLift 4183143
  have htrace : WordTrace (prefixWord ++ tailWord_4183143) baseStart_4183143 baseEnd_4183143 := by
    simpa [prefixWord, tailWord_4183143, baseEnd_4183143] using wordTrace_append hprefix tailTrace_4183143
  have hstable : (prefixWord ++ tailWord_4183143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183143).length < 2 ^ (prefixWord ++ tailWord_4183143).sum := by decide
  have hdescent : baseEnd_4183143 < baseStart_4183143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183160 : List Nat := [2, 1, 2, 1, 1, 1, 7, 3, 1, 3]
def baseStart_4183160 : Nat := 118140960795 + 4183160 * 2 ^ 59
def prefixEnd_4183160 : Nat := 4983230072969 + 3 ^ 40 * 4183160 * 2
def baseEnd_4183160 : Nat := 1431981156441305733974669

theorem tailTrace_4183160 : CollatzResearch.WordTrace tailWord_4183160 prefixEnd_4183160 1431981156441305733974669 := by
  unfold tailWord_4183160
  simp only [CollatzResearch.WordTrace]
  refine ⟨76286189762566610847341467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101714919683422147796455289 76286189762566610847341467)
  ·
    refine ⟨114429284643849916271012201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76286189762566610847341467 114429284643849916271012201)
    ·
      refine ⟨85821963482887437203259151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114429284643849916271012201 85821963482887437203259151)
      ·
        refine ⟨128732945224331155804888727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85821963482887437203259151 128732945224331155804888727)
        ·
          refine ⟨193099417836496733707333091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128732945224331155804888727 193099417836496733707333091)
          ·
            refine ⟨289649126754745100560999637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193099417836496733707333091 289649126754745100560999637)
            ·
              refine ⟨6788651408314338294398429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 289649126754745100560999637 6788651408314338294398429)
              ·
                refine ⟨2545744278117876860399411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6788651408314338294398429 2545744278117876860399411)
                ·
                  refine ⟨3818616417176815290599117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545744278117876860399411 3818616417176815290599117)
                  ·
                    refine ⟨1431981156441305733974669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3818616417176815290599117 1431981156441305733974669)
                    ·
                      rfl

theorem cell22_4183160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_4183160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183160 prefixEnd_4183160 := by exact prefixLift 4183160
  have htrace : WordTrace (prefixWord ++ tailWord_4183160) baseStart_4183160 baseEnd_4183160 := by
    simpa [prefixWord, tailWord_4183160, baseEnd_4183160] using wordTrace_append hprefix tailTrace_4183160
  have hstable : (prefixWord ++ tailWord_4183160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183160).length < 2 ^ (prefixWord ++ tailWord_4183160).sum := by decide
  have hdescent : baseEnd_4183160 < baseStart_4183160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183177 : List Nat := [1, 2, 1, 1, 4, 4, 3, 2, 1, 3]
def baseStart_4183177 : Nat := 118140960795 + 4183177 * 2 ^ 59
def prefixEnd_4183177 : Nat := 4983230072969 + 3 ^ 40 * 4183177 * 2
def baseEnd_4183177 : Nat := 1431986975888723356299617

theorem tailTrace_4183177 : CollatzResearch.WordTrace tailWord_4183177 prefixEnd_4183177 1431986975888723356299617 := by
  unfold tailWord_4183177
  simp only [CollatzResearch.WordTrace]
  refine ⟨152572999566071633598051785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101715333044047755732034523 152572999566071633598051785)
  ·
    refine ⟨114429749674553725198538839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152572999566071633598051785 114429749674553725198538839)
    ·
      refine ⟨171644624511830587797808259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114429749674553725198538839 171644624511830587797808259)
      ·
        refine ⟨257466936767745881696712389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171644624511830587797808259 257466936767745881696712389)
        ·
          refine ⟨48275050643952352818133573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257466936767745881696712389 48275050643952352818133573)
          ·
            refine ⟨9051571995741066153400045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48275050643952352818133573 9051571995741066153400045)
            ·
              refine ⟨3394339498402899807525017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9051571995741066153400045 3394339498402899807525017)
              ·
                refine ⟨2545754623802174855643763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3394339498402899807525017 2545754623802174855643763)
                ·
                  refine ⟨3818631935703262283465645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2545754623802174855643763 3818631935703262283465645)
                  ·
                    refine ⟨1431986975888723356299617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3818631935703262283465645 1431986975888723356299617)
                    ·
                      rfl

theorem cell22_4183177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 1, 3].length) (baseStart_4183177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183177 prefixEnd_4183177 := by exact prefixLift 4183177
  have htrace : WordTrace (prefixWord ++ tailWord_4183177) baseStart_4183177 baseEnd_4183177 := by
    simpa [prefixWord, tailWord_4183177, baseEnd_4183177] using wordTrace_append hprefix tailTrace_4183177
  have hstable : (prefixWord ++ tailWord_4183177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183177).length < 2 ^ (prefixWord ++ tailWord_4183177).sum := by decide
  have hdescent : baseEnd_4183177 < baseStart_4183177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183201 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 8]
def baseStart_4183201 : Nat := 118140960795 + 4183201 * 2 ^ 59
def prefixEnd_4183201 : Nat := 4983230072969 + 3 ^ 40 * 4183201 * 2
def baseEnd_4183201 : Nat := 477331730526398431233181

theorem tailTrace_4183201 : CollatzResearch.WordTrace tailWord_4183201 prefixEnd_4183201 477331730526398431233181 := by
  unfold tailWord_4183201
  simp only [CollatzResearch.WordTrace]
  refine ⟨152573874917984685696925457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101715916611989790464616971 152573874917984685696925457)
  ·
    refine ⟨114430406188488514272694093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152573874917984685696925457 114430406188488514272694093)
    ·
      refine ⟨42911402320683192852260285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114430406188488514272694093 42911402320683192852260285)
      ·
        refine ⟨16091775870256197319597607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42911402320683192852260285 16091775870256197319597607)
        ·
          refine ⟨24137663805384295979396411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16091775870256197319597607 24137663805384295979396411)
          ·
            refine ⟨36206495708076443969094617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24137663805384295979396411 36206495708076443969094617)
            ·
              refine ⟨27154871781057332976820963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36206495708076443969094617 27154871781057332976820963)
              ·
                refine ⟨40732307671585999465231445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27154871781057332976820963 40732307671585999465231445)
                ·
                  refine ⟨477331730526398431233181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40732307671585999465231445 477331730526398431233181)
                  ·
                    rfl

theorem cell22_4183201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_4183201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183201 prefixEnd_4183201 := by exact prefixLift 4183201
  have htrace : WordTrace (prefixWord ++ tailWord_4183201) baseStart_4183201 baseEnd_4183201 := by
    simpa [prefixWord, tailWord_4183201, baseEnd_4183201] using wordTrace_append hprefix tailTrace_4183201
  have hstable : (prefixWord ++ tailWord_4183201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183201).length < 2 ^ (prefixWord ++ tailWord_4183201).sum := by decide
  have hdescent : baseEnd_4183201 < baseStart_4183201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183216 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 1, 5]
def baseStart_4183216 : Nat := 118140960795 + 4183216 * 2 ^ 59
def prefixEnd_4183216 : Nat := 4983230072969 + 3 ^ 40 * 4183216 * 2
def baseEnd_4183216 : Nat := 1432000326385740254574497

theorem tailTrace_4183216 : CollatzResearch.WordTrace tailWord_4183216 prefixEnd_4183216 1432000326385740254574497 := by
  unfold tailWord_4183216
  simp only [CollatzResearch.WordTrace]
  refine ⟨76287211006465171629360751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101716281341953562172481001 76287211006465171629360751)
  ·
    refine ⟨114430816509697757444041127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76287211006465171629360751 114430816509697757444041127)
    ·
      refine ⟨171646224764546636166061691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114430816509697757444041127 171646224764546636166061691)
      ·
        refine ⟨257469337146819954249092537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171646224764546636166061691 257469337146819954249092537)
        ·
          refine ⟨193102002860114965686819403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257469337146819954249092537 193102002860114965686819403)
          ·
            refine ⟨289653004290172448530229105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193102002860114965686819403 289653004290172448530229105)
            ·
              refine ⟨217239753217629336397671829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289653004290172448530229105 217239753217629336397671829)
              ·
                refine ⟨10183113432076375143640867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 217239753217629336397671829 10183113432076375143640867)
                ·
                  refine ⟨15274670148114562715461301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10183113432076375143640867 15274670148114562715461301)
                  ·
                    refine ⟨1432000326385740254574497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15274670148114562715461301 1432000326385740254574497)
                    ·
                      rfl

theorem cell22_4183216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_4183216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183216 prefixEnd_4183216 := by exact prefixLift 4183216
  have htrace : WordTrace (prefixWord ++ tailWord_4183216) baseStart_4183216 baseEnd_4183216 := by
    simpa [prefixWord, tailWord_4183216, baseEnd_4183216] using wordTrace_append hprefix tailTrace_4183216
  have hstable : (prefixWord ++ tailWord_4183216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183216).length < 2 ^ (prefixWord ++ tailWord_4183216).sum := by decide
  have hdescent : baseEnd_4183216 < baseStart_4183216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183250 : List Nat := [3, 2, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_4183250 : Nat := 118140960795 + 4183250 * 2 ^ 59
def prefixEnd_4183250 : Nat := 4983230072969 + 3 ^ 40 * 4183250 * 2
def baseEnd_4183250 : Nat := 1432011965280575499224393

theorem tailTrace_4183250 : CollatzResearch.WordTrace tailWord_4183250 prefixEnd_4183250 1432011965280575499224393 := by
  unfold tailWord_4183250
  simp only [CollatzResearch.WordTrace]
  refine ⟨38143915523701791766364801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101717108063204778043639469 38143915523701791766364801)
  ·
    refine ⟨28607936642776343824773601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38143915523701791766364801 28607936642776343824773601)
    ·
      refine ⟨21455952482082257868580201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28607936642776343824773601 21455952482082257868580201)
      ·
        refine ⟨16091964361561693401435151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21455952482082257868580201 16091964361561693401435151)
        ·
          refine ⟨24137946542342540102152727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16091964361561693401435151 24137946542342540102152727)
          ·
            refine ⟨36206919813513810153229091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24137946542342540102152727 36206919813513810153229091)
            ·
              refine ⟨54310379720270715229843637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36206919813513810153229091 54310379720270715229843637)
              ·
                refine ⟨5091598098775379552797841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54310379720270715229843637 5091598098775379552797841)
                ·
                  refine ⟨3818698574081534664598381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5091598098775379552797841 3818698574081534664598381)
                  ·
                    refine ⟨1432011965280575499224393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3818698574081534664598381 1432011965280575499224393)
                    ·
                      rfl

theorem cell22_4183250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_4183250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183250 prefixEnd_4183250 := by exact prefixLift 4183250
  have htrace : WordTrace (prefixWord ++ tailWord_4183250) baseStart_4183250 baseEnd_4183250 := by
    simpa [prefixWord, tailWord_4183250, baseEnd_4183250] using wordTrace_append hprefix tailTrace_4183250
  have hstable : (prefixWord ++ tailWord_4183250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183250).length < 2 ^ (prefixWord ++ tailWord_4183250).sum := by decide
  have hdescent : baseEnd_4183250 < baseStart_4183250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183265 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 2, 4]
def baseStart_4183265 : Nat := 118140960795 + 4183265 * 2 ^ 59
def prefixEnd_4183265 : Nat := 4983230072969 + 3 ^ 40 * 4183265 * 2
def baseEnd_4183265 : Nat := 1432017100087120460099347

theorem tailTrace_4183265 : CollatzResearch.WordTrace tailWord_4183265 prefixEnd_4183265 1432017100087120460099347 := by
  unfold tailWord_4183265
  simp only [CollatzResearch.WordTrace]
  refine ⟨152576209189752824627255249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101717472793168549751503499 152576209189752824627255249)
  ·
    refine ⟨114432156892314618470441437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152576209189752824627255249 114432156892314618470441437)
    ·
      refine ⟨42912058834617981926415539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114432156892314618470441437 42912058834617981926415539)
      ·
        refine ⟨64368088251926972889623309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42912058834617981926415539 64368088251926972889623309)
        ·
          refine ⟨24138033094472614833608741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64368088251926972889623309 24138033094472614833608741)
          ·
            refine ⟨4525881205213615281301639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24138033094472614833608741 4525881205213615281301639)
            ·
              refine ⟨6788821807820422921952459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4525881205213615281301639 6788821807820422921952459)
              ·
                refine ⟨10183232711730634382928689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6788821807820422921952459 10183232711730634382928689)
                ·
                  refine ⟨7637424533797975787196517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10183232711730634382928689 7637424533797975787196517)
                  ·
                    refine ⟨1432017100087120460099347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7637424533797975787196517 1432017100087120460099347)
                    ·
                      rfl

theorem cell22_4183265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_4183265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183265 prefixEnd_4183265 := by exact prefixLift 4183265
  have htrace : WordTrace (prefixWord ++ tailWord_4183265) baseStart_4183265 baseEnd_4183265 := by
    simpa [prefixWord, tailWord_4183265, baseEnd_4183265] using wordTrace_append hprefix tailTrace_4183265
  have hstable : (prefixWord ++ tailWord_4183265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183265).length < 2 ^ (prefixWord ++ tailWord_4183265).sum := by decide
  have hdescent : baseEnd_4183265 < baseStart_4183265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183295 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 3, 3]
def baseStart_4183295 : Nat := 118140960795 + 4183295 * 2 ^ 59
def prefixEnd_4183295 : Nat := 4983230072969 + 3 ^ 40 * 4183295 * 2
def baseEnd_4183295 : Nat := 1432027369700210381849255

theorem tailTrace_4183295 : CollatzResearch.WordTrace tailWord_4183295 prefixEnd_4183295 1432027369700210381849255 := by
  unfold tailWord_4183295
  simp only [CollatzResearch.WordTrace]
  refine ⟨152577303379644139750847339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101718202253096093167231559 152577303379644139750847339)
  ·
    refine ⟨228865955069466209626271009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152577303379644139750847339 228865955069466209626271009)
    ·
      refine ⟨171649466302099657219703257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228865955069466209626271009 171649466302099657219703257)
      ·
        refine ⟨128737099726574742914777443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171649466302099657219703257 128737099726574742914777443)
        ·
          refine ⟨193105649589862114372166165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128737099726574742914777443 193105649589862114372166165)
          ·
            refine ⟨9051827324524786611195289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 193105649589862114372166165 9051827324524786611195289)
            ·
              refine ⟨6788870493393589958396467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9051827324524786611195289 6788870493393589958396467)
              ·
                refine ⟨10183305740090384937594701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6788870493393589958396467 10183305740090384937594701)
                ·
                  refine ⟨3818739652533894351598013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10183305740090384937594701 3818739652533894351598013)
                  ·
                    refine ⟨1432027369700210381849255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3818739652533894351598013 1432027369700210381849255)
                    ·
                      rfl

theorem cell22_4183295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 3, 3].length) (baseStart_4183295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183295 prefixEnd_4183295 := by exact prefixLift 4183295
  have htrace : WordTrace (prefixWord ++ tailWord_4183295) baseStart_4183295 baseEnd_4183295 := by
    simpa [prefixWord, tailWord_4183295, baseEnd_4183295] using wordTrace_append hprefix tailTrace_4183295
  have hstable : (prefixWord ++ tailWord_4183295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183295).length < 2 ^ (prefixWord ++ tailWord_4183295).sum := by decide
  have hdescent : baseEnd_4183295 < baseStart_4183295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183314 : List Nat := [3, 2, 4, 2, 1, 2, 2, 6]
def baseStart_4183314 : Nat := 118140960795 + 4183314 * 2 ^ 59
def prefixEnd_4183314 : Nat := 4983230072969 + 3 ^ 40 * 4183314 * 2
def baseEnd_4183314 : Nat := 159114874865388962847133

theorem tailTrace_4183314 : CollatzResearch.WordTrace tailWord_4183314 prefixEnd_4183314 159114874865388962847133 := by
  unfold tailWord_4183314
  simp only [CollatzResearch.WordTrace]
  refine ⟨38144499091643826498947249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101718664244383537330525997 38144499091643826498947249)
  ·
    refine ⟨28608374318732869874210437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38144499091643826498947249 28608374318732869874210437)
    ·
      refine ⟨5364070184762413101414457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28608374318732869874210437 5364070184762413101414457)
      ·
        refine ⟨4023052638571809826060843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5364070184762413101414457 4023052638571809826060843)
        ·
          refine ⟨6034578957857714739091265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4023052638571809826060843 6034578957857714739091265)
          ·
            refine ⟨4525934218393286054318449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6034578957857714739091265 4525934218393286054318449)
            ·
              refine ⟨3394450663794964540738837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4525934218393286054318449 3394450663794964540738837)
              ·
                refine ⟨159114874865388962847133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3394450663794964540738837 159114874865388962847133)
                ·
                  rfl

theorem cell22_4183314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 6].length) (baseStart_4183314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183314 prefixEnd_4183314 := by exact prefixLift 4183314
  have htrace : WordTrace (prefixWord ++ tailWord_4183314) baseStart_4183314 baseEnd_4183314 := by
    simpa [prefixWord, tailWord_4183314, baseEnd_4183314] using wordTrace_append hprefix tailTrace_4183314
  have hstable : (prefixWord ++ tailWord_4183314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183314).length < 2 ^ (prefixWord ++ tailWord_4183314).sum := by decide
  have hdescent : baseEnd_4183314 < baseStart_4183314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183321 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 4, 8]
def baseStart_4183321 : Nat := 118140960795 + 4183321 * 2 ^ 59
def prefixEnd_4183321 : Nat := 4983230072969 + 3 ^ 40 * 4183321 * 2
def baseEnd_4183321 : Nat := 1432036270031554980699175

theorem tailTrace_4183321 : CollatzResearch.WordTrace tailWord_4183321 prefixEnd_4183321 1432036270031554980699175 := by
  unfold tailWord_4183321
  simp only [CollatzResearch.WordTrace]
  refine ⟨152578251677549946191293817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101718834451699964127529211 152578251677549946191293817)
  ·
    refine ⟨114433688758162459643470363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152578251677549946191293817 114433688758162459643470363)
    ·
      refine ⟨171650533137243689465205545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114433688758162459643470363 171650533137243689465205545)
      ·
        refine ⟨128737899852932767098904159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171650533137243689465205545 128737899852932767098904159)
        ·
          refine ⟨193106849779399150648356239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128737899852932767098904159 193106849779399150648356239)
          ·
            refine ⟨289660274669098725972534359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193106849779399150648356239 289660274669098725972534359)
            ·
              refine ⟨434490412003648088958801539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289660274669098725972534359 434490412003648088958801539)
              ·
                refine ⟨651735618005472133438202309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434490412003648088958801539 651735618005472133438202309)
                ·
                  refine ⟨122200428376026025019662933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 651735618005472133438202309 122200428376026025019662933)
                  ·
                    refine ⟨1432036270031554980699175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122200428376026025019662933 1432036270031554980699175)
                    ·
                      rfl

theorem cell22_4183321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_4183321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183321 prefixEnd_4183321 := by exact prefixLift 4183321
  have htrace : WordTrace (prefixWord ++ tailWord_4183321) baseStart_4183321 baseEnd_4183321 := by
    simpa [prefixWord, tailWord_4183321, baseEnd_4183321] using wordTrace_append hprefix tailTrace_4183321
  have hstable : (prefixWord ++ tailWord_4183321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183321).length < 2 ^ (prefixWord ++ tailWord_4183321).sum := by decide
  have hdescent : baseEnd_4183321 < baseStart_4183321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183368 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 1, 5]
def baseStart_4183368 : Nat := 118140960795 + 4183368 * 2 ^ 59
def prefixEnd_4183368 : Nat := 4983230072969 + 3 ^ 40 * 4183368 * 2
def baseEnd_4183368 : Nat := 1432052359092062524774031

theorem tailTrace_4183368 : CollatzResearch.WordTrace tailWord_4183368 prefixEnd_4183368 1432052359092062524774031 := by
  unfold tailWord_4183368
  simp only [CollatzResearch.WordTrace]
  refine ⟨76289982954189836609127379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101719977272253115478836505 76289982954189836609127379)
  ·
    refine ⟨114434974431284754913691069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76289982954189836609127379 114434974431284754913691069)
    ·
      refine ⟨42913115411731783092634151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114434974431284754913691069 42913115411731783092634151)
      ·
        refine ⟨64369673117597674638951227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42913115411731783092634151 64369673117597674638951227)
        ·
          refine ⟨96554509676396511958426841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64369673117597674638951227 96554509676396511958426841)
          ·
            refine ⟨72415882257297383968820131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96554509676396511958426841 72415882257297383968820131)
            ·
              refine ⟨108623823385946075953230197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72415882257297383968820131 108623823385946075953230197)
              ·
                refine ⟨10183483442432444620615331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108623823385946075953230197 10183483442432444620615331)
                ·
                  refine ⟨15275225163648666930922997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10183483442432444620615331 15275225163648666930922997)
                  ·
                    refine ⟨1432052359092062524774031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15275225163648666930922997 1432052359092062524774031)
                    ·
                      rfl

theorem cell22_4183368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_4183368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183368 prefixEnd_4183368 := by exact prefixLift 4183368
  have htrace : WordTrace (prefixWord ++ tailWord_4183368) baseStart_4183368 baseEnd_4183368 := by
    simpa [prefixWord, tailWord_4183368, baseEnd_4183368] using wordTrace_append hprefix tailTrace_4183368
  have hstable : (prefixWord ++ tailWord_4183368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183368).length < 2 ^ (prefixWord ++ tailWord_4183368).sum := by decide
  have hdescent : baseEnd_4183368 < baseStart_4183368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183372 : List Nat := [2, 2, 1, 3, 2, 4, 1, 2, 1, 4]
def baseStart_4183372 : Nat := 118140960795 + 4183372 * 2 ^ 59
def prefixEnd_4183372 : Nat := 4983230072969 + 3 ^ 40 * 4183372 * 2
def baseEnd_4183372 : Nat := 1432053728373807847674019

theorem tailTrace_4183372 : CollatzResearch.WordTrace tailWord_4183372 prefixEnd_4183372 1432053728373807847674019 := by
  unfold tailWord_4183372
  simp only [CollatzResearch.WordTrace]
  refine ⟨76290055900182590950700185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101720074533576787934266913 76290055900182590950700185)
  ·
    refine ⟨57217541925136943213025139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76290055900182590950700185 57217541925136943213025139)
    ·
      refine ⟨85826312887705414819537709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57217541925136943213025139 85826312887705414819537709)
      ·
        refine ⟨32184867332889530557326641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85826312887705414819537709 32184867332889530557326641)
        ·
          refine ⟨24138650499667147917994981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32184867332889530557326641 24138650499667147917994981)
          ·
            refine ⟨4525996968687590234624059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24138650499667147917994981 4525996968687590234624059)
            ·
              refine ⟨6788995453031385351936089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4525996968687590234624059 6788995453031385351936089)
              ·
                refine ⟨5091746589773539013952067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6788995453031385351936089 5091746589773539013952067)
                ·
                  refine ⟨7637619884660308520928101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091746589773539013952067 7637619884660308520928101)
                  ·
                    refine ⟨1432053728373807847674019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7637619884660308520928101 1432053728373807847674019)
                    ·
                      rfl

theorem cell22_4183372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_4183372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183372 prefixEnd_4183372 := by exact prefixLift 4183372
  have htrace : WordTrace (prefixWord ++ tailWord_4183372) baseStart_4183372 baseEnd_4183372 := by
    simpa [prefixWord, tailWord_4183372, baseEnd_4183372] using wordTrace_append hprefix tailTrace_4183372
  have hstable : (prefixWord ++ tailWord_4183372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183372).length < 2 ^ (prefixWord ++ tailWord_4183372).sum := by decide
  have hdescent : baseEnd_4183372 < baseStart_4183372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183404 : List Nat := [2, 2, 1, 1, 5, 3, 2, 2, 4]
def baseStart_4183404 : Nat := 118140960795 + 4183404 * 2 ^ 59
def prefixEnd_4183404 : Nat := 4983230072969 + 3 ^ 40 * 4183404 * 2
def baseEnd_4183404 : Nat := 477354894209256810291307

theorem tailTrace_4183404 : CollatzResearch.WordTrace tailWord_4183404 prefixEnd_4183404 477354894209256810291307 := by
  unfold tailWord_4183404
  simp only [CollatzResearch.WordTrace]
  refine ⟨76290639468124625683282633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101720852624166167577710177 76290639468124625683282633)
  ·
    refine ⟨57217979601093469262461975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76290639468124625683282633 57217979601093469262461975)
    ·
      refine ⟨85826969401640203893692963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57217979601093469262461975 85826969401640203893692963)
      ·
        refine ⟨128740454102460305840539445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85826969401640203893692963 128740454102460305840539445)
        ·
          refine ⟨12069417572105653672550573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128740454102460305840539445 12069417572105653672550573)
          ·
            refine ⟨4526031589539620127206465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12069417572105653672550573 4526031589539620127206465)
            ·
              refine ⟨3394523692154715095404849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4526031589539620127206465 3394523692154715095404849)
              ·
                refine ⟨2545892769116036321553637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3394523692154715095404849 2545892769116036321553637)
                ·
                  refine ⟨477354894209256810291307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2545892769116036321553637 477354894209256810291307)
                  ·
                    rfl

theorem cell22_4183404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_4183404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183404 prefixEnd_4183404 := by exact prefixLift 4183404
  have htrace : WordTrace (prefixWord ++ tailWord_4183404) baseStart_4183404 baseEnd_4183404 := by
    simpa [prefixWord, tailWord_4183404, baseEnd_4183404] using wordTrace_append hprefix tailTrace_4183404
  have hstable : (prefixWord ++ tailWord_4183404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183404).length < 2 ^ (prefixWord ++ tailWord_4183404).sum := by decide
  have hdescent : baseEnd_4183404 < baseStart_4183404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183541 : List Nat := [1, 3, 5, 1, 1, 3, 1, 2, 1, 4]
def baseStart_4183541 : Nat := 118140960795 + 4183541 * 2 ^ 59
def prefixEnd_4183541 : Nat := 4983230072969 + 3 ^ 40 * 4183541 * 2
def baseEnd_4183541 : Nat := 1432111580527547740198501

theorem tailTrace_4183541 : CollatzResearch.WordTrace tailWord_4183541 prefixEnd_4183541 1432111580527547740198501 := by
  unfold tailWord_4183541
  simp only [CollatzResearch.WordTrace]
  refine ⟨152586275736752923764302477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101724183824501949176201651 152586275736752923764302477)
  ·
    refine ⟨57219853401282346411613429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152586275736752923764302477 57219853401282346411613429)
    ·
      refine ⟨5364361256370219976088759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57219853401282346411613429 5364361256370219976088759)
      ·
        refine ⟨8046541884555329964133139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5364361256370219976088759 8046541884555329964133139)
        ·
          refine ⟨12069812826832994946199709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8046541884555329964133139 12069812826832994946199709)
          ·
            refine ⟨4526179810062373104824891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12069812826832994946199709 4526179810062373104824891)
            ·
              refine ⟨6789269715093559657237337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4526179810062373104824891 6789269715093559657237337)
              ·
                refine ⟨5091952286320169742928003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6789269715093559657237337 5091952286320169742928003)
                ·
                  refine ⟨7637928429480254614392005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5091952286320169742928003 7637928429480254614392005)
                  ·
                    refine ⟨1432111580527547740198501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7637928429480254614392005 1432111580527547740198501)
                    ·
                      rfl

theorem cell22_4183541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_4183541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183541 prefixEnd_4183541 := by exact prefixLift 4183541
  have htrace : WordTrace (prefixWord ++ tailWord_4183541) baseStart_4183541 baseEnd_4183541 := by
    simpa [prefixWord, tailWord_4183541, baseEnd_4183541] using wordTrace_append hprefix tailTrace_4183541
  have hstable : (prefixWord ++ tailWord_4183541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183541).length < 2 ^ (prefixWord ++ tailWord_4183541).sum := by decide
  have hdescent : baseEnd_4183541 < baseStart_4183541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183554 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_4183554 : Nat := 118140960795 + 4183554 * 2 ^ 59
def prefixEnd_4183554 : Nat := 4983230072969 + 3 ^ 40 * 4183554 * 2
def baseEnd_4183554 : Nat := 1432116030693220039623461

theorem tailTrace_4183554 : CollatzResearch.WordTrace tailWord_4183554 prefixEnd_4183554 1432116030693220039623461 := by
  unfold tailWord_4183554
  simp only [CollatzResearch.WordTrace]
  refine ⟨38146687471426456746131429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101724499923803884656350477 38146687471426456746131429)
  ·
    refine ⟨7152503900892460639899643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38146687471426456746131429 7152503900892460639899643)
    ·
      refine ⟨10728755851338690959849465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7152503900892460639899643 10728755851338690959849465)
      ·
        refine ⟨8046566888504018219887099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10728755851338690959849465 8046566888504018219887099)
        ·
          refine ⟨12069850332756027329830649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8046566888504018219887099 12069850332756027329830649)
          ·
            refine ⟨9052387749567020497372987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12069850332756027329830649 9052387749567020497372987)
            ·
              refine ⟨13578581624350530746059481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9052387749567020497372987 13578581624350530746059481)
              ·
                refine ⟨10183936218262898059544611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13578581624350530746059481 10183936218262898059544611)
                ·
                  refine ⟨15275904327394347089316917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10183936218262898059544611 15275904327394347089316917)
                  ·
                    refine ⟨1432116030693220039623461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15275904327394347089316917 1432116030693220039623461)
                    ·
                      rfl

theorem cell22_4183554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_4183554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183554 prefixEnd_4183554 := by exact prefixLift 4183554
  have htrace : WordTrace (prefixWord ++ tailWord_4183554) baseStart_4183554 baseEnd_4183554 := by
    simpa [prefixWord, tailWord_4183554, baseEnd_4183554] using wordTrace_append hprefix tailTrace_4183554
  have hstable : (prefixWord ++ tailWord_4183554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183554).length < 2 ^ (prefixWord ++ tailWord_4183554).sum := by decide
  have hdescent : baseEnd_4183554 < baseStart_4183554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183580 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 1, 8]
def baseStart_4183580 : Nat := 118140960795 + 4183580 * 2 ^ 59
def prefixEnd_4183580 : Nat := 4983230072969 + 3 ^ 40 * 4183580 * 2
def baseEnd_4183580 : Nat := 1432124931024564638473381

theorem tailTrace_4183580 : CollatzResearch.WordTrace tailWord_4183580 prefixEnd_4183580 1432124931024564638473381 := by
  unfold tailWord_4183580
  simp only [CollatzResearch.WordTrace]
  refine ⟨76293849091805816712486097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101725132122407755616648129 76293849091805816712486097)
  ·
    refine ⟨57220386818854362534364573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76293849091805816712486097 57220386818854362534364573)
    ·
      refine ⟨21457645057070385950386715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57220386818854362534364573 21457645057070385950386715)
      ·
        refine ⟨32186467585605578925580073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21457645057070385950386715 32186467585605578925580073)
        ·
          refine ⟨24139850689204184194185055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32186467585605578925580073 24139850689204184194185055)
          ·
            refine ⟨36209776033806276291277583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24139850689204184194185055 36209776033806276291277583)
            ·
              refine ⟨54314664050709414436916375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36209776033806276291277583 54314664050709414436916375)
              ·
                refine ⟨81471996076064121655374563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54314664050709414436916375 81471996076064121655374563)
                ·
                  refine ⟨122207994114096182483061845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81471996076064121655374563 122207994114096182483061845)
                  ·
                    refine ⟨1432124931024564638473381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122207994114096182483061845 1432124931024564638473381)
                    ·
                      rfl

theorem cell22_4183580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_4183580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183580 prefixEnd_4183580 := by exact prefixLift 4183580
  have htrace : WordTrace (prefixWord ++ tailWord_4183580) baseStart_4183580 baseEnd_4183580 := by
    simpa [prefixWord, tailWord_4183580, baseEnd_4183580] using wordTrace_append hprefix tailTrace_4183580
  have hstable : (prefixWord ++ tailWord_4183580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183580).length < 2 ^ (prefixWord ++ tailWord_4183580).sum := by decide
  have hdescent : baseEnd_4183580 < baseStart_4183580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183610 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_4183610 : Nat := 118140960795 + 4183610 * 2 ^ 59
def prefixEnd_4183610 : Nat := 4983230072969 + 3 ^ 40 * 4183610 * 2
def baseEnd_4183610 : Nat := 1432135200637654560223289

theorem tailTrace_4183610 : CollatzResearch.WordTrace tailWord_4183610 prefixEnd_4183610 1432135200637654560223289 := by
  unfold tailWord_4183610
  simp only [CollatzResearch.WordTrace]
  refine ⟨38147198093375737137141071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101725861582335299032376189 38147198093375737137141071)
  ·
    refine ⟨57220797140063605705711607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38147198093375737137141071 57220797140063605705711607)
    ·
      refine ⟨85831195710095408558567411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57220797140063605705711607 85831195710095408558567411)
      ·
        refine ⟨128746793565143112837851117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85831195710095408558567411 128746793565143112837851117)
        ·
          refine ⟨48280047586928667314194169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128746793565143112837851117 48280047586928667314194169)
          ·
            refine ⟨36210035690196500485645627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48280047586928667314194169 36210035690196500485645627)
            ·
              refine ⟨54315053535294750728468441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36210035690196500485645627 54315053535294750728468441)
              ·
                refine ⟨40736290151471063046351331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54315053535294750728468441 40736290151471063046351331)
                ·
                  refine ⟨61104435227206594569526997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40736290151471063046351331 61104435227206594569526997)
                  ·
                    refine ⟨1432135200637654560223289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61104435227206594569526997 1432135200637654560223289)
                    ·
                      rfl

theorem cell22_4183610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_4183610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183610 prefixEnd_4183610 := by exact prefixLift 4183610
  have htrace : WordTrace (prefixWord ++ tailWord_4183610) baseStart_4183610 baseEnd_4183610 := by
    simpa [prefixWord, tailWord_4183610, baseEnd_4183610] using wordTrace_append hprefix tailTrace_4183610
  have hstable : (prefixWord ++ tailWord_4183610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183610).length < 2 ^ (prefixWord ++ tailWord_4183610).sum := by decide
  have hdescent : baseEnd_4183610 < baseStart_4183610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183629 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 7]
def baseStart_4183629 : Nat := 118140960795 + 4183629 * 2 ^ 59
def prefixEnd_4183629 : Nat := 4983230072969 + 3 ^ 40 * 4183629 * 2
def baseEnd_4183629 : Nat := 477380568241981614666077

theorem tailTrace_4183629 : CollatzResearch.WordTrace tailWord_4183629 prefixEnd_4183629 477380568241981614666077 := by
  unfold tailWord_4183629
  simp only [CollatzResearch.WordTrace]
  refine ⟨152589485360434114793505941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101726323573622743195670627 152589485360434114793505941)
  ·
    refine ⟨7152632126270349130945591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152589485360434114793505941 7152632126270349130945591)
    ·
      refine ⟨10728948189405523696418387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7152632126270349130945591 10728948189405523696418387)
      ·
        refine ⟨16093422284108285544627581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10728948189405523696418387 16093422284108285544627581)
        ·
          refine ⟨6035033356540607079235343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16093422284108285544627581 6035033356540607079235343)
          ·
            refine ⟨9052550034810910618853015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6035033356540607079235343 9052550034810910618853015)
            ·
              refine ⟨13578825052216365928279523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9052550034810910618853015 13578825052216365928279523)
              ·
                refine ⟨20368237578324548892419285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13578825052216365928279523 20368237578324548892419285)
                ·
                  refine ⟨477380568241981614666077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20368237578324548892419285 477380568241981614666077)
                  ·
                    rfl

theorem cell22_4183629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_4183629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183629 prefixEnd_4183629 := by exact prefixLift 4183629
  have htrace : WordTrace (prefixWord ++ tailWord_4183629) baseStart_4183629 baseEnd_4183629 := by
    simpa [prefixWord, tailWord_4183629, baseEnd_4183629] using wordTrace_append hprefix tailTrace_4183629
  have hstable : (prefixWord ++ tailWord_4183629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183629).length < 2 ^ (prefixWord ++ tailWord_4183629).sum := by decide
  have hdescent : baseEnd_4183629 < baseStart_4183629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183687 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 4, 4]
def baseStart_4183687 : Nat := 118140960795 + 4183687 * 2 ^ 59
def prefixEnd_4183687 : Nat := 4983230072969 + 3 ^ 40 * 4183687 * 2
def baseEnd_4183687 : Nat := 1432161559311252026048053

theorem tailTrace_4183687 : CollatzResearch.WordTrace tailWord_4183687 prefixEnd_4183687 1432161559311252026048053 := by
  unfold tailWord_4183687
  simp only [CollatzResearch.WordTrace]
  refine ⟨152591600794223990699117315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101727733862815993799411543 152591600794223990699117315)
  ·
    refine ⟨228887401191335986048675973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152591600794223990699117315 228887401191335986048675973)
    ·
      refine ⟨42916387723375497384126745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228887401191335986048675973 42916387723375497384126745)
      ·
        refine ⟨32187290792531623038095059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42916387723375497384126745 32187290792531623038095059)
        ·
          refine ⟨48280936188797434557142589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32187290792531623038095059 48280936188797434557142589)
          ·
            refine ⟨18105351070799037958928471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48280936188797434557142589 18105351070799037958928471)
            ·
              refine ⟨27158026606198556938392707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18105351070799037958928471 27158026606198556938392707)
              ·
                refine ⟨40737039909297835407589061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27158026606198556938392707 40737039909297835407589061)
                ·
                  refine ⟨7638194982993344138922949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40737039909297835407589061 7638194982993344138922949)
                  ·
                    refine ⟨1432161559311252026048053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7638194982993344138922949 1432161559311252026048053)
                    ·
                      rfl

theorem cell22_4183687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_4183687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183687 prefixEnd_4183687 := by exact prefixLift 4183687
  have htrace : WordTrace (prefixWord ++ tailWord_4183687) baseStart_4183687 baseEnd_4183687 := by
    simpa [prefixWord, tailWord_4183687, baseEnd_4183687] using wordTrace_append hprefix tailTrace_4183687
  have hstable : (prefixWord ++ tailWord_4183687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183687).length < 2 ^ (prefixWord ++ tailWord_4183687).sum := by decide
  have hdescent : baseEnd_4183687 < baseStart_4183687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183751 : List Nat := [1, 1, 4, 1, 1, 1, 5, 4, 1, 3]
def baseStart_4183751 : Nat := 118140960795 + 4183751 * 2 ^ 59
def prefixEnd_4183751 : Nat := 4983230072969 + 3 ^ 40 * 4183751 * 2
def baseEnd_4183751 : Nat := 1432183467819177192447857

theorem tailTrace_4183751 : CollatzResearch.WordTrace tailWord_4183751 prefixEnd_4183751 1432183467819177192447857 := by
  unfold tailWord_4183751
  simp only [CollatzResearch.WordTrace]
  refine ⟨152593935065992129629447107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101729290043994753086298071 152593935065992129629447107)
  ·
    refine ⟨228890902598988194444170661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152593935065992129629447107 228890902598988194444170661)
    ·
      refine ⟨42917044237310286458281999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228890902598988194444170661 42917044237310286458281999)
      ·
        refine ⟨64375566355965429687422999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42917044237310286458281999 64375566355965429687422999)
        ·
          refine ⟨96563349533948144531134499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64375566355965429687422999 96563349533948144531134499)
          ·
            refine ⟨144845024300922216796701749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96563349533948144531134499 144845024300922216796701749)
            ·
              refine ⟨13579221028211457824690789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144845024300922216796701749 13579221028211457824690789)
              ·
                refine ⟨2546103942789648342129523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13579221028211457824690789 2546103942789648342129523)
                ·
                  refine ⟨3819155914184472513194285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546103942789648342129523 3819155914184472513194285)
                  ·
                    refine ⟨1432183467819177192447857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3819155914184472513194285 1432183467819177192447857)
                    ·
                      rfl

theorem cell22_4183751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_4183751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183751 prefixEnd_4183751 := by exact prefixLift 4183751
  have htrace : WordTrace (prefixWord ++ tailWord_4183751) baseStart_4183751 baseEnd_4183751 := by
    simpa [prefixWord, tailWord_4183751, baseEnd_4183751] using wordTrace_append hprefix tailTrace_4183751
  have hstable : (prefixWord ++ tailWord_4183751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183751).length < 2 ^ (prefixWord ++ tailWord_4183751).sum := by decide
  have hdescent : baseEnd_4183751 < baseStart_4183751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183807 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 3, 5]
def baseStart_4183807 : Nat := 118140960795 + 4183807 * 2 ^ 59
def prefixEnd_4183807 : Nat := 4983230072969 + 3 ^ 40 * 4183807 * 2
def baseEnd_4183807 : Nat := 1432202637763611713047685

theorem tailTrace_4183807 : CollatzResearch.WordTrace tailWord_4183807 prefixEnd_4183807 1432202637763611713047685 := by
  unfold tailWord_4183807
  simp only [CollatzResearch.WordTrace]
  refine ⟨152595977553789251193485675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101730651702526167462323783 152595977553789251193485675)
  ·
    refine ⟨228893966330683876790228513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152595977553789251193485675 228893966330683876790228513)
    ·
      refine ⟨171670474748012907592671385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228893966330683876790228513 171670474748012907592671385)
      ·
        refine ⟨128752856061009680694503539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171670474748012907592671385 128752856061009680694503539)
        ·
          refine ⟨193129284091514521041755309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128752856061009680694503539 193129284091514521041755309)
          ·
            refine ⟨72423481534317945390658241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193129284091514521041755309 72423481534317945390658241)
            ·
              refine ⟨54317611150738459042993681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72423481534317945390658241 54317611150738459042993681)
              ·
                refine ⟨40738208363053844282245261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54317611150738459042993681 40738208363053844282245261)
                ·
                  refine ⟨15276828136145191605841973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40738208363053844282245261 15276828136145191605841973)
                  ·
                    refine ⟨1432202637763611713047685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15276828136145191605841973 1432202637763611713047685)
                    ·
                      rfl

theorem cell22_4183807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_4183807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183807 prefixEnd_4183807 := by exact prefixLift 4183807
  have htrace : WordTrace (prefixWord ++ tailWord_4183807) baseStart_4183807 baseEnd_4183807 := by
    simpa [prefixWord, tailWord_4183807, baseEnd_4183807] using wordTrace_append hprefix tailTrace_4183807
  have hstable : (prefixWord ++ tailWord_4183807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183807).length < 2 ^ (prefixWord ++ tailWord_4183807).sum := by decide
  have hdescent : baseEnd_4183807 < baseStart_4183807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183826 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 6]
def baseStart_4183826 : Nat := 118140960795 + 4183826 * 2 ^ 59
def prefixEnd_4183826 : Nat := 4983230072969 + 3 ^ 40 * 4183826 * 2
def baseEnd_4183826 : Nat := 477403047283967332274209

theorem tailTrace_4183826 : CollatzResearch.WordTrace tailWord_4183826 prefixEnd_4183826 477403047283967332274209 := by
  unfold tailWord_4183826
  simp only [CollatzResearch.WordTrace]
  refine ⟨38149167635180104359606833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101731113693813611625618221 38149167635180104359606833)
  ·
    refine ⟨28611875726385078269705125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38149167635180104359606833 28611875726385078269705125)
    ·
      refine ⟨5364726698697202175569711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28611875726385078269705125 5364726698697202175569711)
      ·
        refine ⟨8047090048045803263354567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5364726698697202175569711 8047090048045803263354567)
        ·
          refine ⟨12070635072068704895031851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8047090048045803263354567 12070635072068704895031851)
          ·
            refine ⟨18105952608103057342547777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12070635072068704895031851 18105952608103057342547777)
            ·
              refine ⟨13579464456077293006910833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18105952608103057342547777 13579464456077293006910833)
              ·
                refine ⟨10184598342057969755183125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13579464456077293006910833 10184598342057969755183125)
                ·
                  refine ⟨477403047283967332274209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10184598342057969755183125 477403047283967332274209)
                  ·
                    rfl

theorem cell22_4183826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_4183826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183826 prefixEnd_4183826 := by exact prefixLift 4183826
  have htrace : WordTrace (prefixWord ++ tailWord_4183826) baseStart_4183826 baseEnd_4183826 := by
    simpa [prefixWord, tailWord_4183826, baseEnd_4183826] using wordTrace_append hprefix tailTrace_4183826
  have hstable : (prefixWord ++ tailWord_4183826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183826).length < 2 ^ (prefixWord ++ tailWord_4183826).sum := by decide
  have hdescent : baseEnd_4183826 < baseStart_4183826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183839 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 2, 4]
def baseStart_4183839 : Nat := 118140960795 + 4183839 * 2 ^ 59
def prefixEnd_4183839 : Nat := 4983230072969 + 3 ^ 40 * 4183839 * 2
def baseEnd_4183839 : Nat := 1432213592017574296247587

theorem tailTrace_4183839 : CollatzResearch.WordTrace tailWord_4183839 prefixEnd_4183839 1432213592017574296247587 := by
  unfold tailWord_4183839
  simp only [CollatzResearch.WordTrace]
  refine ⟨152597144689673320658650571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101731429793115547105767047 152597144689673320658650571)
  ·
    refine ⟨228895717034509980987975857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152597144689673320658650571 228895717034509980987975857)
    ·
      refine ⟨171671787775882485740981893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228895717034509980987975857 171671787775882485740981893)
      ·
        refine ⟨32188460207977966076434105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171671787775882485740981893 32188460207977966076434105)
        ·
          refine ⟨24141345155983474557325579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32188460207977966076434105 24141345155983474557325579)
          ·
            refine ⟨36212017733975211835988369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24141345155983474557325579 36212017733975211835988369)
            ·
              refine ⟨27159013300481408876991277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36212017733975211835988369 27159013300481408876991277)
              ·
                refine ⟨10184629987680528328871729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27159013300481408876991277 10184629987680528328871729)
                ·
                  refine ⟨7638472490760396246653797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10184629987680528328871729 7638472490760396246653797)
                  ·
                    refine ⟨1432213592017574296247587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7638472490760396246653797 1432213592017574296247587)
                    ·
                      rfl

theorem cell22_4183839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_4183839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183839 prefixEnd_4183839 := by exact prefixLift 4183839
  have htrace : WordTrace (prefixWord ++ tailWord_4183839) baseStart_4183839 baseEnd_4183839 := by
    simpa [prefixWord, tailWord_4183839, baseEnd_4183839] using wordTrace_append hprefix tailTrace_4183839
  have hstable : (prefixWord ++ tailWord_4183839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183839).length < 2 ^ (prefixWord ++ tailWord_4183839).sum := by decide
  have hdescent : baseEnd_4183839 < baseStart_4183839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183860 : List Nat := [2, 5, 1, 1, 2, 2, 3, 2, 4]
def baseStart_4183860 : Nat := 118140960795 + 4183860 * 2 ^ 59
def prefixEnd_4183860 : Nat := 4983230072969 + 3 ^ 40 * 4183860 * 2
def baseEnd_4183860 : Nat := 477406926915579080490841

theorem tailTrace_4183860 : CollatzResearch.WordTrace tailWord_4183860 prefixEnd_4183860 477406926915579080490841 := by
  unfold tailWord_4183860
  simp only [CollatzResearch.WordTrace]
  refine ⟨76298955311298620622582517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101731940415064827496776689 76298955311298620622582517)
  ·
    refine ⟨7153027060434245683367111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76298955311298620622582517 7153027060434245683367111)
    ·
      refine ⟨10729540590651368525050667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7153027060434245683367111 10729540590651368525050667)
      ·
        refine ⟨16094310885977052787576001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10729540590651368525050667 16094310885977052787576001)
        ·
          refine ⟨12070733164482789590682001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16094310885977052787576001 12070733164482789590682001)
          ·
            refine ⟨9053049873362092193011501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12070733164482789590682001 9053049873362092193011501)
            ·
              refine ⟨3394893702510784572379313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9053049873362092193011501 3394893702510784572379313)
              ·
                refine ⟨2546170276883088429284485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3394893702510784572379313 2546170276883088429284485)
                ·
                  refine ⟨477406926915579080490841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2546170276883088429284485 477406926915579080490841)
                  ·
                    rfl

theorem cell22_4183860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_4183860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183860 prefixEnd_4183860 := by exact prefixLift 4183860
  have htrace : WordTrace (prefixWord ++ tailWord_4183860) baseStart_4183860 baseEnd_4183860 := by
    simpa [prefixWord, tailWord_4183860, baseEnd_4183860] using wordTrace_append hprefix tailTrace_4183860
  have hstable : (prefixWord ++ tailWord_4183860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183860).length < 2 ^ (prefixWord ++ tailWord_4183860).sum := by decide
  have hdescent : baseEnd_4183860 < baseStart_4183860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183916 : List Nat := [2, 2, 1, 1, 4, 3, 2, 2, 5]
def baseStart_4183916 : Nat := 118140960795 + 4183916 * 2 ^ 59
def prefixEnd_4183916 : Nat := 4983230072969 + 3 ^ 40 * 4183916 * 2
def baseEnd_4183916 : Nat := 477413316897057254024117

theorem tailTrace_4183916 : CollatzResearch.WordTrace tailWord_4183916 prefixEnd_4183916 477413316897057254024117 := by
  unfold tailWord_4183916
  simp only [CollatzResearch.WordTrace]
  refine ⟨76299976555197181404601801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101733302073596241872802401 76299976555197181404601801)
  ·
    refine ⟨57224982416397886053451351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76299976555197181404601801 57224982416397886053451351)
    ·
      refine ⟨85837473624596829080177027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57224982416397886053451351 85837473624596829080177027)
      ·
        refine ⟨128756210436895243620265541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85837473624596829080177027 128756210436895243620265541)
        ·
          refine ⟨24141789456917858178799789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128756210436895243620265541 24141789456917858178799789)
          ·
            refine ⟨9053171046344196817049921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24141789456917858178799789 9053171046344196817049921)
            ·
              refine ⟨6789878284758147612787441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9053171046344196817049921 6789878284758147612787441)
              ·
                refine ⟨5092408713568610709590581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6789878284758147612787441 5092408713568610709590581)
                ·
                  refine ⟨477413316897057254024117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5092408713568610709590581 477413316897057254024117)
                  ·
                    rfl

theorem cell22_4183916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_4183916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183916 prefixEnd_4183916 := by exact prefixLift 4183916
  have htrace : WordTrace (prefixWord ++ tailWord_4183916) baseStart_4183916 baseEnd_4183916 := by
    simpa [prefixWord, tailWord_4183916, baseEnd_4183916] using wordTrace_append hprefix tailTrace_4183916
  have hstable : (prefixWord ++ tailWord_4183916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183916).length < 2 ^ (prefixWord ++ tailWord_4183916).sum := by decide
  have hdescent : baseEnd_4183916 < baseStart_4183916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183929 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 5, 4]
def baseStart_4183929 : Nat := 118140960795 + 4183929 * 2 ^ 59
def prefixEnd_4183929 : Nat := 4983230072969 + 3 ^ 40 * 4183929 * 2
def baseEnd_4183929 : Nat := 1432244400856844061497311

theorem tailTrace_4183929 : CollatzResearch.WordTrace tailWord_4183929 prefixEnd_4183929 1432244400856844061497311 := by
  unfold tailWord_4183929
  simp only [CollatzResearch.WordTrace]
  refine ⟨152600427259347266029426841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101733618172898177352951227 152600427259347266029426841)
  ·
    refine ⟨114450320444510449522070131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152600427259347266029426841 114450320444510449522070131)
    ·
      refine ⟨171675480666765674283105197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114450320444510449522070131 171675480666765674283105197)
      ·
        refine ⟨64378305250037127856164449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171675480666765674283105197 64378305250037127856164449)
        ·
          refine ⟨48283728937527845892123337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64378305250037127856164449 48283728937527845892123337)
          ·
            refine ⟨36212796703145884419092503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48283728937527845892123337 36212796703145884419092503)
            ·
              refine ⟨54319195054718826628638755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36212796703145884419092503 54319195054718826628638755)
              ·
                refine ⟨81478792582078239942958133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54319195054718826628638755 81478792582078239942958133)
                ·
                  refine ⟨7638636804569834994652325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81478792582078239942958133 7638636804569834994652325)
                  ·
                    refine ⟨1432244400856844061497311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7638636804569834994652325 1432244400856844061497311)
                    ·
                      rfl

theorem cell22_4183929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_4183929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183929 prefixEnd_4183929 := by exact prefixLift 4183929
  have htrace : WordTrace (prefixWord ++ tailWord_4183929) baseStart_4183929 baseEnd_4183929 := by
    simpa [prefixWord, tailWord_4183929, baseEnd_4183929] using wordTrace_append hprefix tailTrace_4183929
  have hstable : (prefixWord ++ tailWord_4183929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183929).length < 2 ^ (prefixWord ++ tailWord_4183929).sum := by decide
  have hdescent : baseEnd_4183929 < baseStart_4183929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4183961 : List Nat := [1, 2, 1, 2, 1, 3, 3, 5, 4]
def baseStart_4183961 : Nat := 118140960795 + 4183961 * 2 ^ 59
def prefixEnd_4183961 : Nat := 4983230072969 + 3 ^ 40 * 4183961 * 2
def baseEnd_4183961 : Nat := 477418451703602214899071

theorem tailTrace_4183961 : CollatzResearch.WordTrace tailWord_4183961 prefixEnd_4183961 477418451703602214899071 := by
  unfold tailWord_4183961
  simp only [CollatzResearch.WordTrace]
  refine ⟨152601594395231335494591737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101734396263487556996394491 152601594395231335494591737)
  ·
    refine ⟨114451195796423501620943803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152601594395231335494591737 114451195796423501620943803)
    ·
      refine ⟨171676793694635252431415705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114451195796423501620943803 171676793694635252431415705)
      ·
        refine ⟨128757595270976439323561779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171676793694635252431415705 128757595270976439323561779)
        ·
          refine ⟨193136392906464658985342669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128757595270976439323561779 193136392906464658985342669)
          ·
            refine ⟨72426147339924247119503501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193136392906464658985342669 72426147339924247119503501)
            ·
              refine ⟨27159805252471592669813813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72426147339924247119503501 27159805252471592669813813)
              ·
                refine ⟨2546231742419211812795045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27159805252471592669813813 2546231742419211812795045)
                ·
                  refine ⟨477418451703602214899071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2546231742419211812795045 477418451703602214899071)
                  ·
                    rfl

theorem cell22_4183961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 4].length) (baseStart_4183961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4183961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4183961 prefixEnd_4183961 := by exact prefixLift 4183961
  have htrace : WordTrace (prefixWord ++ tailWord_4183961) baseStart_4183961 baseEnd_4183961 := by
    simpa [prefixWord, tailWord_4183961, baseEnd_4183961] using wordTrace_append hprefix tailTrace_4183961
  have hstable : (prefixWord ++ tailWord_4183961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4183961).length < 2 ^ (prefixWord ++ tailWord_4183961).sum := by decide
  have hdescent : baseEnd_4183961 < baseStart_4183961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4183961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184162 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_4184162 : Nat := 118140960795 + 4184162 * 2 ^ 59
def prefixEnd_4184162 : Nat := 4983230072969 + 3 ^ 40 * 4184162 * 2
def baseEnd_4184162 : Nat := 1432324161518509120421597

theorem tailTrace_4184162 : CollatzResearch.WordTrace tailWord_4184162 prefixEnd_4184162 1432324161518509120421597 := by
  unfold tailWord_4184162
  simp only [CollatzResearch.WordTrace]
  refine ⟨38152231366875786705664685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101739283645002097881772493 38152231366875786705664685)
  ·
    refine ⟨14307086762578420014624257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38152231366875786705664685 14307086762578420014624257)
    ·
      refine ⟨10730315071933815010968193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14307086762578420014624257 10730315071933815010968193)
      ·
        refine ⟨8047736303950361258226145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10730315071933815010968193 8047736303950361258226145)
        ·
          refine ⟨6035802227962770943669609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8047736303950361258226145 6035802227962770943669609)
          ·
            refine ⟨4526851670972078207752207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6035802227962770943669609 4526851670972078207752207)
            ·
              refine ⟨6790277506458117311628311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4526851670972078207752207 6790277506458117311628311)
              ·
                refine ⟨10185416259687175967442467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6790277506458117311628311 10185416259687175967442467)
                ·
                  refine ⟨15278124389530763951163701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10185416259687175967442467 15278124389530763951163701)
                  ·
                    refine ⟨1432324161518509120421597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15278124389530763951163701 1432324161518509120421597)
                    ·
                      rfl

theorem cell22_4184162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_4184162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184162 prefixEnd_4184162 := by exact prefixLift 4184162
  have htrace : WordTrace (prefixWord ++ tailWord_4184162) baseStart_4184162 baseEnd_4184162 := by
    simpa [prefixWord, tailWord_4184162, baseEnd_4184162] using wordTrace_append hprefix tailTrace_4184162
  have hstable : (prefixWord ++ tailWord_4184162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184162).length < 2 ^ (prefixWord ++ tailWord_4184162).sum := by decide
  have hdescent : baseEnd_4184162 < baseStart_4184162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184258 : List Nat := [3, 5, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_4184258 : Nat := 118140960795 + 4184258 * 2 ^ 59
def prefixEnd_4184258 : Nat := 4983230072969 + 3 ^ 40 * 4184258 * 2
def baseEnd_4184258 : Nat := 1432357024280396870021303

theorem tailTrace_4184258 : CollatzResearch.WordTrace tailWord_4184258 prefixEnd_4184258 1432357024280396870021303 := by
  unfold tailWord_4184258
  simp only [CollatzResearch.WordTrace]
  refine ⟨38153106718788838804538357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101741617916770236812102285 38153106718788838804538357)
  ·
    refine ⟨3576853754886453637925471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38153106718788838804538357 3576853754886453637925471)
    ·
      refine ⟨5365280632329680456888207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3576853754886453637925471 5365280632329680456888207)
      ·
        refine ⟨8047920948494520685332311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5365280632329680456888207 8047920948494520685332311)
        ·
          refine ⟨12071881422741781027998467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8047920948494520685332311 12071881422741781027998467)
          ·
            refine ⟨18107822134112671541997701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12071881422741781027998467 18107822134112671541997701)
            ·
              refine ⟨3395216650146125914124569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18107822134112671541997701 3395216650146125914124569)
              ·
                refine ⟨2546412487609594435593427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395216650146125914124569 2546412487609594435593427)
                ·
                  refine ⟨3819618731414391653390141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546412487609594435593427 3819618731414391653390141)
                  ·
                    refine ⟨1432357024280396870021303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3819618731414391653390141 1432357024280396870021303)
                    ·
                      rfl

theorem cell22_4184258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_4184258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184258 prefixEnd_4184258 := by exact prefixLift 4184258
  have htrace : WordTrace (prefixWord ++ tailWord_4184258) baseStart_4184258 baseEnd_4184258 := by
    simpa [prefixWord, tailWord_4184258, baseEnd_4184258] using wordTrace_append hprefix tailTrace_4184258
  have hstable : (prefixWord ++ tailWord_4184258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184258).length < 2 ^ (prefixWord ++ tailWord_4184258).sum := by decide
  have hdescent : baseEnd_4184258 < baseStart_4184258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184280 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 1, 5]
def baseStart_4184280 : Nat := 118140960795 + 4184280 * 2 ^ 59
def prefixEnd_4184280 : Nat := 4983230072969 + 3 ^ 40 * 4184280 * 2
def baseEnd_4184280 : Nat := 1432364555329996145971235

theorem tailTrace_4184280 : CollatzResearch.WordTrace tailWord_4184280 prefixEnd_4184280 1432364555329996145971235 := by
  unfold tailWord_4184280
  simp only [CollatzResearch.WordTrace]
  refine ⟨76306614640537826487727147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101742152854050435316969529 76306614640537826487727147)
  ·
    refine ⟨114459921960806739731590721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76306614640537826487727147 114459921960806739731590721)
    ·
      refine ⟨85844941470605054798693041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114459921960806739731590721 85844941470605054798693041)
      ·
        refine ⟨64383706102953791099019781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85844941470605054798693041 64383706102953791099019781)
        ·
          refine ⟨12071944894303835831066209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64383706102953791099019781 12071944894303835831066209)
          ·
            refine ⟨9053958670727876873299657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12071944894303835831066209 9053958670727876873299657)
            ·
              refine ⟨6790469003045907654974743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9053958670727876873299657 6790469003045907654974743)
              ·
                refine ⟨10185703504568861482462115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6790469003045907654974743 10185703504568861482462115)
                ·
                  refine ⟨15278555256853292223693173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10185703504568861482462115 15278555256853292223693173)
                  ·
                    refine ⟨1432364555329996145971235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15278555256853292223693173 1432364555329996145971235)
                    ·
                      rfl

theorem cell22_4184280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_4184280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184280 prefixEnd_4184280 := by exact prefixLift 4184280
  have htrace : WordTrace (prefixWord ++ tailWord_4184280) baseStart_4184280 baseEnd_4184280 := by
    simpa [prefixWord, tailWord_4184280, baseEnd_4184280] using wordTrace_append hprefix tailTrace_4184280
  have hstable : (prefixWord ++ tailWord_4184280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184280).length < 2 ^ (prefixWord ++ tailWord_4184280).sum := by decide
  have hdescent : baseEnd_4184280 < baseStart_4184280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184295 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 1, 6]
def baseStart_4184295 : Nat := 118140960795 + 4184295 * 2 ^ 59
def prefixEnd_4184295 : Nat := 4983230072969 + 3 ^ 40 * 4184295 * 2
def baseEnd_4184295 : Nat := 1432369690136541106846189

theorem tailTrace_4184295 : CollatzResearch.WordTrace tailWord_4184295 prefixEnd_4184295 1432369690136541106846189 := by
  unfold tailWord_4184295
  simp only [CollatzResearch.WordTrace]
  refine ⟨152613776376021310537250339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101742517584014207024833559 152613776376021310537250339)
  ·
    refine ⟨228920664564031965805875509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152613776376021310537250339 228920664564031965805875509)
    ·
      refine ⟨21461312302877996794300829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 228920664564031965805875509 21461312302877996794300829)
      ·
        refine ⟨8047992113579248797862811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21461312302877996794300829 8047992113579248797862811)
        ·
          refine ⟨12071988170368873196794217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8047992113579248797862811 12071988170368873196794217)
          ·
            refine ⟨9053991127776654897595663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12071988170368873196794217 9053991127776654897595663)
            ·
              refine ⟨13580986691664982346393495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9053991127776654897595663 13580986691664982346393495)
              ·
                refine ⟨20371480037497473519590243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13580986691664982346393495 20371480037497473519590243)
                ·
                  refine ⟨30557220056246210279385365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20371480037497473519590243 30557220056246210279385365)
                  ·
                    refine ⟨1432369690136541106846189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30557220056246210279385365 1432369690136541106846189)
                    ·
                      rfl

theorem cell22_4184295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_4184295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184295 prefixEnd_4184295 := by exact prefixLift 4184295
  have htrace : WordTrace (prefixWord ++ tailWord_4184295) baseStart_4184295 baseEnd_4184295 := by
    simpa [prefixWord, tailWord_4184295, baseEnd_4184295] using wordTrace_append hprefix tailTrace_4184295
  have hstable : (prefixWord ++ tailWord_4184295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184295).length < 2 ^ (prefixWord ++ tailWord_4184295).sum := by decide
  have hdescent : baseEnd_4184295 < baseStart_4184295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184301 : List Nat := [1, 5, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_4184301 : Nat := 118140960795 + 4184301 * 2 ^ 59
def prefixEnd_4184301 : Nat := 4983230072969 + 3 ^ 40 * 4184301 * 2
def baseEnd_4184301 : Nat := 1432371744059159091196171

theorem tailTrace_4184301 : CollatzResearch.WordTrace tailWord_4184301 prefixEnd_4184301 1432371744059159091196171 := by
  unfold tailWord_4184301
  simp only [CollatzResearch.WordTrace]
  refine ⟨152613995213999573561968757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101742663475999715707979171 152613995213999573561968757)
  ·
    refine ⟨14307562051312460021434571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152613995213999573561968757 14307562051312460021434571)
    ·
      refine ⟨21461343076968690032151857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14307562051312460021434571 21461343076968690032151857)
      ·
        refine ⟨16096007307726517524113893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21461343076968690032151857 16096007307726517524113893)
        ·
          refine ⟨3018001370198722035771355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16096007307726517524113893 3018001370198722035771355)
          ·
            refine ⟨4527002055298083053657033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018001370198722035771355 4527002055298083053657033)
            ·
              refine ⟨3395251541473562290242775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4527002055298083053657033 3395251541473562290242775)
              ·
                refine ⟨5092877312210343435364163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395251541473562290242775 5092877312210343435364163)
                ·
                  refine ⟨7639315968315515153046245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5092877312210343435364163 7639315968315515153046245)
                  ·
                    refine ⟨1432371744059159091196171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7639315968315515153046245 1432371744059159091196171)
                    ·
                      rfl

theorem cell22_4184301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_4184301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184301 prefixEnd_4184301 := by exact prefixLift 4184301
  have htrace : WordTrace (prefixWord ++ tailWord_4184301) baseStart_4184301 baseEnd_4184301 := by
    simpa [prefixWord, tailWord_4184301, baseEnd_4184301] using wordTrace_append hprefix tailTrace_4184301
  have hstable : (prefixWord ++ tailWord_4184301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184301).length < 2 ^ (prefixWord ++ tailWord_4184301).sum := by decide
  have hdescent : baseEnd_4184301 < baseStart_4184301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184353 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 1, 7]
def baseStart_4184353 : Nat := 118140960795 + 4184353 * 2 ^ 59
def prefixEnd_4184353 : Nat := 4983230072969 + 3 ^ 40 * 4184353 * 2
def baseEnd_4184353 : Nat := 1432389544721848288896011

theorem tailTrace_4184353 : CollatzResearch.WordTrace tailWord_4184353 prefixEnd_4184353 1432389544721848288896011 := by
  unfold tailWord_4184353
  simp only [CollatzResearch.WordTrace]
  refine ⟨152615891809811186442861713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101743927873207457628574475 152615891809811186442861713)
  ·
    refine ⟨114461918857358389832146285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152615891809811186442861713 114461918857358389832146285)
    ·
      refine ⟨42923219571509396187054857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114461918857358389832146285 42923219571509396187054857)
      ·
        refine ⟨32192414678632047140291143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42923219571509396187054857 32192414678632047140291143)
        ·
          refine ⟨48288622017948070710436715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32192414678632047140291143 48288622017948070710436715)
          ·
            refine ⟨72432933026922106065655073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48288622017948070710436715 72432933026922106065655073)
            ·
              refine ⟨54324699770191579549241305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72432933026922106065655073 54324699770191579549241305)
              ·
                refine ⟨40743524827643684661930979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54324699770191579549241305 40743524827643684661930979)
                ·
                  refine ⟨61115287241465526992896469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40743524827643684661930979 61115287241465526992896469)
                  ·
                    refine ⟨1432389544721848288896011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61115287241465526992896469 1432389544721848288896011)
                    ·
                      rfl

theorem cell22_4184353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_4184353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184353 prefixEnd_4184353 := by exact prefixLift 4184353
  have htrace : WordTrace (prefixWord ++ tailWord_4184353) baseStart_4184353 baseEnd_4184353 := by
    simpa [prefixWord, tailWord_4184353, baseEnd_4184353] using wordTrace_append hprefix tailTrace_4184353
  have hstable : (prefixWord ++ tailWord_4184353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184353).length < 2 ^ (prefixWord ++ tailWord_4184353).sum := by decide
  have hdescent : baseEnd_4184353 < baseStart_4184353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184402 : List Nat := [3, 2, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_4184402 : Nat := 118140960795 + 4184402 * 2 ^ 59
def prefixEnd_4184402 : Nat := 4983230072969 + 3 ^ 40 * 4184402 * 2
def baseEnd_4184402 : Nat := 1432406318423228494420861

theorem tailTrace_4184402 : CollatzResearch.WordTrace tailWord_4184402 prefixEnd_4184402 1432406318423228494420861 := by
  unfold tailWord_4184402
  simp only [CollatzResearch.WordTrace]
  refine ⟨38154419746658416952848865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101745119324422445207596973 38154419746658416952848865)
  ·
    refine ⟨28615814809993812714636649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38154419746658416952848865 28615814809993812714636649)
    ·
      refine ⟨21461861107495359535977487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28615814809993812714636649 21461861107495359535977487)
      ·
        refine ⟨32192791661243039303966231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21461861107495359535977487 32192791661243039303966231)
        ·
          refine ⟨48289187491864558955949347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32192791661243039303966231 48289187491864558955949347)
          ·
            refine ⟨72433781237796838433924021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48289187491864558955949347 72433781237796838433924021)
            ·
              refine ⟨6790666991043453603180377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72433781237796838433924021 6790666991043453603180377)
              ·
                refine ⟨5093000243282590202385283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6790666991043453603180377 5093000243282590202385283)
                ·
                  refine ⟨7639500364923885303577925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093000243282590202385283 7639500364923885303577925)
                  ·
                    refine ⟨1432406318423228494420861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7639500364923885303577925 1432406318423228494420861)
                    ·
                      rfl

theorem cell22_4184402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_4184402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184402 prefixEnd_4184402 := by exact prefixLift 4184402
  have htrace : WordTrace (prefixWord ++ tailWord_4184402) baseStart_4184402 baseEnd_4184402 := by
    simpa [prefixWord, tailWord_4184402, baseEnd_4184402] using wordTrace_append hprefix tailTrace_4184402
  have hstable : (prefixWord ++ tailWord_4184402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184402).length < 2 ^ (prefixWord ++ tailWord_4184402).sum := by decide
  have hdescent : baseEnd_4184402 < baseStart_4184402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184415 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 6, 3]
def baseStart_4184415 : Nat := 118140960795 + 4184415 * 2 ^ 59
def prefixEnd_4184415 : Nat := 4983230072969 + 3 ^ 40 * 4184415 * 2
def baseEnd_4184415 : Nat := 1432410768588900793845821

theorem tailTrace_4184415 : CollatzResearch.WordTrace tailWord_4184415 prefixEnd_4184415 1432410768588900793845821 := by
  unfold tailWord_4184415
  simp only [CollatzResearch.WordTrace]
  refine ⟨152618153135586571031618699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101745435423724380687745799 152618153135586571031618699)
  ·
    refine ⟨228927229703379856547428049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152618153135586571031618699 228927229703379856547428049)
    ·
      refine ⟨171695422277534892410571037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228927229703379856547428049 171695422277534892410571037)
      ·
        refine ⟨64385783354075584653964139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171695422277534892410571037 64385783354075584653964139)
        ·
          refine ⟨96578675031113376980946209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64385783354075584653964139 96578675031113376980946209)
          ·
            refine ⟨72434006273335032735709657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96578675031113376980946209 72434006273335032735709657)
            ·
              refine ⟨54325504705001274551782243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72434006273335032735709657 54325504705001274551782243)
              ·
                refine ⟨81488257057501911827673365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54325504705001274551782243 81488257057501911827673365)
                ·
                  refine ⟨3819762049570402116922189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81488257057501911827673365 3819762049570402116922189)
                  ·
                    refine ⟨1432410768588900793845821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3819762049570402116922189 1432410768588900793845821)
                    ·
                      rfl

theorem cell22_4184415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 3].length) (baseStart_4184415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184415 prefixEnd_4184415 := by exact prefixLift 4184415
  have htrace : WordTrace (prefixWord ++ tailWord_4184415) baseStart_4184415 baseEnd_4184415 := by
    simpa [prefixWord, tailWord_4184415, baseEnd_4184415] using wordTrace_append hprefix tailTrace_4184415
  have hstable : (prefixWord ++ tailWord_4184415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184415).length < 2 ^ (prefixWord ++ tailWord_4184415).sum := by decide
  have hdescent : baseEnd_4184415 < baseStart_4184415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184428 : List Nat := [2, 2, 1, 1, 16]
def baseStart_4184428 : Nat := 118140960795 + 4184428 * 2 ^ 59
def prefixEnd_4184428 : Nat := 4983230072969 + 3 ^ 40 * 4184428 * 2
def baseEnd_4184428 : Nat := 5894712834380959231567

theorem tailTrace_4184428 : CollatzResearch.WordTrace tailWord_4184428 prefixEnd_4184428 5894712834380959231567 := by
  unfold tailWord_4184428
  simp only [CollatzResearch.WordTrace]
  refine ⟨76309313642269737125920969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101745751523026316167894625 76309313642269737125920969)
  ·
    refine ⟨57231985231702302844440727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76309313642269737125920969 57231985231702302844440727)
    ·
      refine ⟨85847977847553454266661091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57231985231702302844440727 85847977847553454266661091)
      ·
        refine ⟨128771966771330181399991637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85847977847553454266661091 128771966771330181399991637)
        ·
          refine ⟨5894712834380959231567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 128771966771330181399991637 5894712834380959231567)
          ·
            rfl

theorem cell22_4184428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 16].length) (baseStart_4184428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184428 prefixEnd_4184428 := by exact prefixLift 4184428
  have htrace : WordTrace (prefixWord ++ tailWord_4184428) baseStart_4184428 baseEnd_4184428 := by
    simpa [prefixWord, tailWord_4184428, baseEnd_4184428] using wordTrace_append hprefix tailTrace_4184428
  have hstable : (prefixWord ++ tailWord_4184428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184428).length < 2 ^ (prefixWord ++ tailWord_4184428).sum := by decide
  have hdescent : baseEnd_4184428 < baseStart_4184428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184432 : List Nat := [2, 1, 1, 1, 4, 3, 1, 4, 2, 3]
def baseStart_4184432 : Nat := 118140960795 + 4184432 * 2 ^ 59
def prefixEnd_4184432 : Nat := 4983230072969 + 3 ^ 40 * 4184432 * 2
def baseEnd_4184432 : Nat := 1432416588036318416170769

theorem tailTrace_4184432 : CollatzResearch.WordTrace tailWord_4184432 prefixEnd_4184432 1432416588036318416170769 := by
  unfold tailWord_4184432
  simp only [CollatzResearch.WordTrace]
  refine ⟨76309386588262491467493775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101745848784349988623325033 76309386588262491467493775)
  ·
    refine ⟨114464079882393737201240663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76309386588262491467493775 114464079882393737201240663)
    ·
      refine ⟨171696119823590605801860995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114464079882393737201240663 171696119823590605801860995)
      ·
        refine ⟨257544179735385908702791493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171696119823590605801860995 257544179735385908702791493)
        ·
          refine ⟨48289533700384857881773405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257544179735385908702791493 48289533700384857881773405)
          ·
            refine ⟨18108575137644321705665027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48289533700384857881773405 18108575137644321705665027)
            ·
              refine ⟨27162862706466482558497541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18108575137644321705665027 27162862706466482558497541)
              ·
                refine ⟨5093036757462465479718289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27162862706466482558497541 5093036757462465479718289)
                ·
                  refine ⟨3819777568096849109788717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5093036757462465479718289 3819777568096849109788717)
                  ·
                    refine ⟨1432416588036318416170769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3819777568096849109788717 1432416588036318416170769)
                    ·
                      rfl

theorem cell22_4184432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 2, 3].length) (baseStart_4184432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184432 prefixEnd_4184432 := by exact prefixLift 4184432
  have htrace : WordTrace (prefixWord ++ tailWord_4184432) baseStart_4184432 baseEnd_4184432 := by
    simpa [prefixWord, tailWord_4184432, baseEnd_4184432] using wordTrace_append hprefix tailTrace_4184432
  have hstable : (prefixWord ++ tailWord_4184432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184432).length < 2 ^ (prefixWord ++ tailWord_4184432).sum := by decide
  have hdescent : baseEnd_4184432 < baseStart_4184432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184434 : List Nat := [3, 2, 1, 2, 1, 3, 4, 2, 4]
def baseStart_4184434 : Nat := 118140960795 + 4184434 * 2 ^ 59
def prefixEnd_4184434 : Nat := 4983230072969 + 3 ^ 40 * 4184434 * 2
def baseEnd_4184434 : Nat := 477472424225730359206921

theorem tailTrace_4184434 : CollatzResearch.WordTrace tailWord_4184434 prefixEnd_4184434 477472424225730359206921 := by
  unfold tailWord_4184434
  simp only [CollatzResearch.WordTrace]
  refine ⟨38154711530629434319140089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101745897415011824851040237 38154711530629434319140089)
  ·
    refine ⟨28616033647972075739355067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38154711530629434319140089 28616033647972075739355067)
    ·
      refine ⟨42924050471958113609032601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28616033647972075739355067 42924050471958113609032601)
      ·
        refine ⟨32193037853968585206774451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42924050471958113609032601 32193037853968585206774451)
        ·
          refine ⟨48289556780952877810161677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32193037853968585206774451 48289556780952877810161677)
          ·
            refine ⟨18108583792857329178810629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48289556780952877810161677 18108583792857329178810629)
            ·
              refine ⟨3395359461160749221026993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18108583792857329178810629 3395359461160749221026993)
              ·
                refine ⟨2546519595870561915770245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395359461160749221026993 2546519595870561915770245)
                ·
                  refine ⟨477472424225730359206921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2546519595870561915770245 477472424225730359206921)
                  ·
                    rfl

theorem cell22_4184434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_4184434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184434 prefixEnd_4184434 := by exact prefixLift 4184434
  have htrace : WordTrace (prefixWord ++ tailWord_4184434) baseStart_4184434 baseEnd_4184434 := by
    simpa [prefixWord, tailWord_4184434, baseEnd_4184434] using wordTrace_append hprefix tailTrace_4184434
  have hstable : (prefixWord ++ tailWord_4184434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184434).length < 2 ^ (prefixWord ++ tailWord_4184434).sum := by decide
  have hdescent : baseEnd_4184434 < baseStart_4184434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184445 : List Nat := [1, 4, 1, 1, 2, 3, 3, 7]
def baseStart_4184445 : Nat := 118140960795 + 4184445 * 2 ^ 59
def prefixEnd_4184445 : Nat := 4983230072969 + 3 ^ 40 * 4184445 * 2
def baseEnd_4184445 : Nat := 159157893133554523955081

theorem tailTrace_4184445 : CollatzResearch.WordTrace tailWord_4184445 prefixEnd_4184445 159157893133554523955081 := by
  unfold tailWord_4184445
  simp only [CollatzResearch.WordTrace]
  refine ⟨152619247325477886155210789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101746164883651924103473859 152619247325477886155210789)
  ·
    refine ⟨28616108873527103654102023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152619247325477886155210789 28616108873527103654102023)
    ·
      refine ⟨42924163310290655481153035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28616108873527103654102023 42924163310290655481153035)
      ·
        refine ⟨64386244965435983221729553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42924163310290655481153035 64386244965435983221729553)
        ·
          refine ⟨48289683724076987416297165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64386244965435983221729553 48289683724076987416297165)
          ·
            refine ⟨18108631396528870281111437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48289683724076987416297165 18108631396528870281111437)
            ·
              refine ⟨6790736773698326355416789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18108631396528870281111437 6790736773698326355416789)
              ·
                refine ⟨159157893133554523955081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6790736773698326355416789 159157893133554523955081)
                ·
                  rfl

theorem cell22_4184445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 7].length) (baseStart_4184445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184445 prefixEnd_4184445 := by exact prefixLift 4184445
  have htrace : WordTrace (prefixWord ++ tailWord_4184445) baseStart_4184445 baseEnd_4184445 := by
    simpa [prefixWord, tailWord_4184445, baseEnd_4184445] using wordTrace_append hprefix tailTrace_4184445
  have hstable : (prefixWord ++ tailWord_4184445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184445).length < 2 ^ (prefixWord ++ tailWord_4184445).sum := by decide
  have hdescent : baseEnd_4184445 < baseStart_4184445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184449 : List Nat := [1, 2, 4, 3, 1, 1, 2, 3, 2, 3]
def baseStart_4184449 : Nat := 118140960795 + 4184449 * 2 ^ 59
def prefixEnd_4184449 : Nat := 4983230072969 + 3 ^ 40 * 4184449 * 2
def baseEnd_4184449 : Nat := 1432422407483736038495717

theorem tailTrace_4184449 : CollatzResearch.WordTrace tailWord_4184449 prefixEnd_4184449 1432422407483736038495717 := by
  unfold tailWord_4184449
  simp only [CollatzResearch.WordTrace]
  refine ⟨152619393217463394838356401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101746262144975596558904267 152619393217463394838356401)
  ·
    refine ⟨114464544913097546128767301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152619393217463394838356401 114464544913097546128767301)
    ·
      refine ⟨21462102171205789899143869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114464544913097546128767301 21462102171205789899143869)
      ·
        refine ⟨8048288314202171212178951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21462102171205789899143869 8048288314202171212178951)
        ·
          refine ⟨12072432471303256818268427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8048288314202171212178951 12072432471303256818268427)
          ·
            refine ⟨18108648706954885227402641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12072432471303256818268427 18108648706954885227402641)
            ·
              refine ⟨13581486530216163920551981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18108648706954885227402641 13581486530216163920551981)
              ·
                refine ⟨5093057448831061470206993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13581486530216163920551981 5093057448831061470206993)
                ·
                  refine ⟨3819793086623296102655245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5093057448831061470206993 3819793086623296102655245)
                  ·
                    refine ⟨1432422407483736038495717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3819793086623296102655245 1432422407483736038495717)
                    ·
                      rfl

theorem cell22_4184449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_4184449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184449 prefixEnd_4184449 := by exact prefixLift 4184449
  have htrace : WordTrace (prefixWord ++ tailWord_4184449) baseStart_4184449 baseEnd_4184449 := by
    simpa [prefixWord, tailWord_4184449, baseEnd_4184449] using wordTrace_append hprefix tailTrace_4184449
  have hstable : (prefixWord ++ tailWord_4184449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184449).length < 2 ^ (prefixWord ++ tailWord_4184449).sum := by decide
  have hdescent : baseEnd_4184449 < baseStart_4184449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184500 : List Nat := [2, 5, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_4184500 : Nat := 118140960795 + 4184500 * 2 ^ 59
def prefixEnd_4184500 : Nat := 4983230072969 + 3 ^ 40 * 4184500 * 2
def baseEnd_4184500 : Nat := 1432439865825988905470561

theorem tailTrace_4184500 : CollatzResearch.WordTrace tailWord_4184500 prefixEnd_4184500 1432439865825988905470561 := by
  unfold tailWord_4184500
  simp only [CollatzResearch.WordTrace]
  refine ⟨76310626670139315274231477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101747502226852420365641969 76310626670139315274231477)
  ·
    refine ⟨7154121250325560806959201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76310626670139315274231477 7154121250325560806959201)
    ·
      refine ⟨5365590937744170605219401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7154121250325560806959201 5365590937744170605219401)
      ·
        refine ⟨4024193203308127953914551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5365590937744170605219401 4024193203308127953914551)
        ·
          refine ⟨6036289804962191930871827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4024193203308127953914551 6036289804962191930871827)
          ·
            refine ⟨9054434707443287896307741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6036289804962191930871827 9054434707443287896307741)
            ·
              refine ⟨3395413015291232961115403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9054434707443287896307741 3395413015291232961115403)
              ·
                refine ⟨5093119522936849441673105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395413015291232961115403 5093119522936849441673105)
                ·
                  refine ⟨3819839642202637081254829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5093119522936849441673105 3819839642202637081254829)
                  ·
                    refine ⟨1432439865825988905470561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3819839642202637081254829 1432439865825988905470561)
                    ·
                      rfl

theorem cell22_4184500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_4184500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184500 prefixEnd_4184500 := by exact prefixLift 4184500
  have htrace : WordTrace (prefixWord ++ tailWord_4184500) baseStart_4184500 baseEnd_4184500 := by
    simpa [prefixWord, tailWord_4184500, baseEnd_4184500] using wordTrace_append hprefix tailTrace_4184500
  have hstable : (prefixWord ++ tailWord_4184500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184500).length < 2 ^ (prefixWord ++ tailWord_4184500).sum := by decide
  have hdescent : baseEnd_4184500 < baseStart_4184500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184513 : List Nat := [1, 2, 7, 1, 1, 2, 2, 6]
def baseStart_4184513 : Nat := 118140960795 + 4184513 * 2 ^ 59
def prefixEnd_4184513 : Nat := 4983230072969 + 3 ^ 40 * 4184513 * 2
def baseEnd_4184513 : Nat := 159160479554629022766169

theorem tailTrace_4184513 : CollatzResearch.WordTrace tailWord_4184513 prefixEnd_4184513 159160479554629022766169 := by
  unfold tailWord_4184513
  simp only [CollatzResearch.WordTrace]
  refine ⟨152621727489231533768686193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101747818326154355845790795 152621727489231533768686193)
  ·
    refine ⟨114466295616923650326514645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152621727489231533768686193 114466295616923650326514645)
    ·
      refine ⟨2682803803521648054527687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 114466295616923650326514645 2682803803521648054527687)
      ·
        refine ⟨4024205705282472081791531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2682803803521648054527687 4024205705282472081791531)
        ·
          refine ⟨6036308557923708122687297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4024205705282472081791531 6036308557923708122687297)
          ·
            refine ⟨4527231418442781092015473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6036308557923708122687297 4527231418442781092015473)
            ·
              refine ⟨3395423563832085819011605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4527231418442781092015473 3395423563832085819011605)
              ·
                refine ⟨159160479554629022766169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3395423563832085819011605 159160479554629022766169)
                ·
                  rfl

theorem cell22_4184513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 6].length) (baseStart_4184513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184513 prefixEnd_4184513 := by exact prefixLift 4184513
  have htrace : WordTrace (prefixWord ++ tailWord_4184513) baseStart_4184513 baseEnd_4184513 := by
    simpa [prefixWord, tailWord_4184513, baseEnd_4184513] using wordTrace_append hprefix tailTrace_4184513
  have hstable : (prefixWord ++ tailWord_4184513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184513).length < 2 ^ (prefixWord ++ tailWord_4184513).sum := by decide
  have hdescent : baseEnd_4184513 < baseStart_4184513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184537 : List Nat := [1, 2, 1, 2, 4, 1, 1, 5, 1, 4]
def baseStart_4184537 : Nat := 118140960795 + 4184537 * 2 ^ 59
def prefixEnd_4184537 : Nat := 4983230072969 + 3 ^ 40 * 4184537 * 2
def baseEnd_4184537 : Nat := 1432452531682133142295447

theorem tailTrace_4184537 : CollatzResearch.WordTrace tailWord_4184537 prefixEnd_4184537 1432452531682133142295447 := by
  unfold tailWord_4184537
  simp only [CollatzResearch.WordTrace]
  refine ⟨152622602841144585867559865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101748401894096390578373243 152622602841144585867559865)
  ·
    refine ⟨114466952130858439400669899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152622602841144585867559865 114466952130858439400669899)
    ·
      refine ⟨171700428196287659101004849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114466952130858439400669899 171700428196287659101004849)
      ·
        refine ⟨128775321147215744325753637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171700428196287659101004849 128775321147215744325753637)
        ·
          refine ⟨24145372715102952061078807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128775321147215744325753637 24145372715102952061078807)
          ·
            refine ⟨36218059072654428091618211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24145372715102952061078807 36218059072654428091618211)
            ·
              refine ⟨54327088608981642137427317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36218059072654428091618211 54327088608981642137427317)
              ·
                refine ⟨5093164557092028950383811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54327088608981642137427317 5093164557092028950383811)
                ·
                  refine ⟨7639746835638043425575717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5093164557092028950383811 7639746835638043425575717)
                  ·
                    refine ⟨1432452531682133142295447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7639746835638043425575717 1432452531682133142295447)
                    ·
                      rfl

theorem cell22_4184537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_4184537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184537 prefixEnd_4184537 := by exact prefixLift 4184537
  have htrace : WordTrace (prefixWord ++ tailWord_4184537) baseStart_4184537 baseEnd_4184537 := by
    simpa [prefixWord, tailWord_4184537, baseEnd_4184537] using wordTrace_append hprefix tailTrace_4184537
  have hstable : (prefixWord ++ tailWord_4184537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184537).length < 2 ^ (prefixWord ++ tailWord_4184537).sum := by decide
  have hdescent : baseEnd_4184537 < baseStart_4184537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184552 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 6]
def baseStart_4184552 : Nat := 118140960795 + 4184552 * 2 ^ 59
def prefixEnd_4184552 : Nat := 4983230072969 + 3 ^ 40 * 4184552 * 2
def baseEnd_4184552 : Nat := 477485888829559367723467

theorem tailTrace_4184552 : CollatzResearch.WordTrace tailWord_4184552 prefixEnd_4184552 477485888829559367723467 := by
  unfold tailWord_4184552
  simp only [CollatzResearch.WordTrace]
  refine ⟨76311574968045121714677955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101748766624060162286237273 76311574968045121714677955)
  ·
    refine ⟨114467362452067682572016933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76311574968045121714677955 114467362452067682572016933)
    ·
      refine ⟨21462630459762690482253175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114467362452067682572016933 21462630459762690482253175)
      ·
        refine ⟨32193945689644035723379763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21462630459762690482253175 32193945689644035723379763)
        ·
          refine ⟨48290918534466053585069645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32193945689644035723379763 48290918534466053585069645)
          ·
            refine ⟨18109094450424770094401117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48290918534466053585069645 18109094450424770094401117)
            ·
              refine ⟨6790910418909288785400419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18109094450424770094401117 6790910418909288785400419)
              ·
                refine ⟨10186365628363933178100629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6790910418909288785400419 10186365628363933178100629)
                ·
                  refine ⟨477485888829559367723467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10186365628363933178100629 477485888829559367723467)
                  ·
                    rfl

theorem cell22_4184552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 6].length) (baseStart_4184552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184552 prefixEnd_4184552 := by exact prefixLift 4184552
  have htrace : WordTrace (prefixWord ++ tailWord_4184552) baseStart_4184552 baseEnd_4184552 := by
    simpa [prefixWord, tailWord_4184552, baseEnd_4184552] using wordTrace_append hprefix tailTrace_4184552
  have hstable : (prefixWord ++ tailWord_4184552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184552).length < 2 ^ (prefixWord ++ tailWord_4184552).sum := by decide
  have hdescent : baseEnd_4184552 < baseStart_4184552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184629 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 3, 3]
def baseStart_4184629 : Nat := 118140960795 + 4184629 * 2 ^ 59
def prefixEnd_4184629 : Nat := 4983230072969 + 3 ^ 40 * 4184629 * 2
def baseEnd_4184629 : Nat := 1432484025162275568995165

theorem tailTrace_4184629 : CollatzResearch.WordTrace tailWord_4184629 prefixEnd_4184629 1432484025162275568995165 := by
  unfold tailWord_4184629
  simp only [CollatzResearch.WordTrace]
  refine ⟨152625958356811285579908941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101750638904540857053272627 152625958356811285579908941)
  ·
    refine ⟨57234734383804232092465853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152625958356811285579908941 57234734383804232092465853)
    ·
      refine ⟨21463025393926587034674695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57234734383804232092465853 21463025393926587034674695)
      ·
        refine ⟨32194538090889880552012043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21463025393926587034674695 32194538090889880552012043)
        ·
          refine ⟨48291807136334820828018065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32194538090889880552012043 48291807136334820828018065)
          ·
            refine ⟨36218855352251115621013549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48291807136334820828018065 36218855352251115621013549)
            ·
              refine ⟨13582070757094168357880081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36218855352251115621013549 13582070757094168357880081)
              ·
                refine ⟨10186553067820626268410061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13582070757094168357880081 10186553067820626268410061)
                ·
                  refine ⟨3819957400432734850653773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10186553067820626268410061 3819957400432734850653773)
                  ·
                    refine ⟨1432484025162275568995165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3819957400432734850653773 1432484025162275568995165)
                    ·
                      rfl

theorem cell22_4184629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_4184629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184629 prefixEnd_4184629 := by exact prefixLift 4184629
  have htrace : WordTrace (prefixWord ++ tailWord_4184629) baseStart_4184629 baseEnd_4184629 := by
    simpa [prefixWord, tailWord_4184629, baseEnd_4184629] using wordTrace_append hprefix tailTrace_4184629
  have hstable : (prefixWord ++ tailWord_4184629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184629).length < 2 ^ (prefixWord ++ tailWord_4184629).sum := by decide
  have hdescent : baseEnd_4184629 < baseStart_4184629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184657 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 2, 5]
def baseStart_4184657 : Nat := 118140960795 + 4184657 * 2 ^ 59
def prefixEnd_4184657 : Nat := 4983230072969 + 3 ^ 40 * 4184657 * 2
def baseEnd_4184657 : Nat := 1432493610134492829295079

theorem tailTrace_4184657 : CollatzResearch.WordTrace tailWord_4184657 prefixEnd_4184657 1432493610134492829295079 := by
  unfold tailWord_4184657
  simp only [CollatzResearch.WordTrace]
  refine ⟨152626979600709846361928225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101751319733806564241285483 152626979600709846361928225)
  ·
    refine ⟨114470234700532384771446169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152626979600709846361928225 114470234700532384771446169)
    ·
      refine ⟨85852676025399288578584627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114470234700532384771446169 85852676025399288578584627)
      ·
        refine ⟨128779014038098932867876941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85852676025399288578584627 128779014038098932867876941)
        ·
          refine ⟨48292130264287099825453853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128779014038098932867876941 48292130264287099825453853)
          ·
            refine ⟨18109548849107662434545195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48292130264287099825453853 18109548849107662434545195)
            ·
              refine ⟨27164323273661493651817793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18109548849107662434545195 27164323273661493651817793)
              ·
                refine ⟨20373242455246120238863345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27164323273661493651817793 20373242455246120238863345)
                ·
                  refine ⟨15279931841434590179147509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20373242455246120238863345 15279931841434590179147509)
                  ·
                    refine ⟨1432493610134492829295079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15279931841434590179147509 1432493610134492829295079)
                    ·
                      rfl

theorem cell22_4184657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_4184657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184657 prefixEnd_4184657 := by exact prefixLift 4184657
  have htrace : WordTrace (prefixWord ++ tailWord_4184657) baseStart_4184657 baseEnd_4184657 := by
    simpa [prefixWord, tailWord_4184657, baseEnd_4184657] using wordTrace_append hprefix tailTrace_4184657
  have hstable : (prefixWord ++ tailWord_4184657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184657).length < 2 ^ (prefixWord ++ tailWord_4184657).sum := by decide
  have hdescent : baseEnd_4184657 < baseStart_4184657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184672 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 5, 4]
def baseStart_4184672 : Nat := 118140960795 + 4184672 * 2 ^ 59
def prefixEnd_4184672 : Nat := 4983230072969 + 3 ^ 40 * 4184672 * 2
def baseEnd_4184672 : Nat := 1432498744941037790170033

theorem tailTrace_4184672 : CollatzResearch.WordTrace tailWord_4184672 prefixEnd_4184672 1432498744941037790170033 := by
  unfold tailWord_4184672
  simp only [CollatzResearch.WordTrace]
  refine ⟨76313763347827751961862135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101751684463770335949149513 76313763347827751961862135)
  ·
    refine ⟨114470645021741627942793203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76313763347827751961862135 114470645021741627942793203)
    ·
      refine ⟨171705967532612441914189805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114470645021741627942793203 171705967532612441914189805)
      ·
        refine ⟨64389737824729665717821177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171705967532612441914189805 64389737824729665717821177)
        ·
          refine ⟨48292303368547249288365883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64389737824729665717821177 48292303368547249288365883)
          ·
            refine ⟨72438455052820873932548825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48292303368547249288365883 72438455052820873932548825)
            ·
              refine ⟨54328841289615655449411619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72438455052820873932548825 54328841289615655449411619)
              ·
                refine ⟨81493261934423483174117429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54328841289615655449411619 81493261934423483174117429)
                ·
                  refine ⟨7639993306352201547573509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81493261934423483174117429 7639993306352201547573509)
                  ·
                    refine ⟨1432498744941037790170033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7639993306352201547573509 1432498744941037790170033)
                    ·
                      rfl

theorem cell22_4184672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_4184672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184672 prefixEnd_4184672 := by exact prefixLift 4184672
  have htrace : WordTrace (prefixWord ++ tailWord_4184672) baseStart_4184672 baseEnd_4184672 := by
    simpa [prefixWord, tailWord_4184672, baseEnd_4184672] using wordTrace_append hprefix tailTrace_4184672
  have hstable : (prefixWord ++ tailWord_4184672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184672).length < 2 ^ (prefixWord ++ tailWord_4184672).sum := by decide
  have hdescent : baseEnd_4184672 < baseStart_4184672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184687 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 6]
def baseStart_4184687 : Nat := 118140960795 + 4184687 * 2 ^ 59
def prefixEnd_4184687 : Nat := 4983230072969 + 3 ^ 40 * 4184687 * 2
def baseEnd_4184687 : Nat := 477501293249194250348329

theorem tailTrace_4184687 : CollatzResearch.WordTrace tailWord_4184687 prefixEnd_4184687 477501293249194250348329 := by
  unfold tailWord_4184687
  simp only [CollatzResearch.WordTrace]
  refine ⟨152628073790601161485520315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101752049193734107657013543 152628073790601161485520315)
  ·
    refine ⟨228942110685901742228280473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152628073790601161485520315 228942110685901742228280473)
    ·
      refine ⟨171706583014426306671210355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228942110685901742228280473 171706583014426306671210355)
      ·
        refine ⟨257559874521639460006815533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171706583014426306671210355 257559874521639460006815533)
        ·
          refine ⟨96584952945614797502555825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257559874521639460006815533 96584952945614797502555825)
          ·
            refine ⟨72438714709211098126916869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96584952945614797502555825 72438714709211098126916869)
            ·
              refine ⟨13582259007977080898796913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72438714709211098126916869 13582259007977080898796913)
              ·
                refine ⟨10186694255982810674097685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13582259007977080898796913 10186694255982810674097685)
                ·
                  refine ⟨477501293249194250348329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10186694255982810674097685 477501293249194250348329)
                  ·
                    rfl

theorem cell22_4184687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 6].length) (baseStart_4184687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184687 prefixEnd_4184687 := by exact prefixLift 4184687
  have htrace : WordTrace (prefixWord ++ tailWord_4184687) baseStart_4184687 baseEnd_4184687 := by
    simpa [prefixWord, tailWord_4184687, baseEnd_4184687] using wordTrace_append hprefix tailTrace_4184687
  have hstable : (prefixWord ++ tailWord_4184687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184687).length < 2 ^ (prefixWord ++ tailWord_4184687).sum := by decide
  have hdescent : baseEnd_4184687 < baseStart_4184687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184749 : List Nat := [1, 5, 2, 1, 1, 2, 2, 8]
def baseStart_4184749 : Nat := 118140960795 + 4184749 * 2 ^ 59
def prefixEnd_4184749 : Nat := 4983230072969 + 3 ^ 40 * 4184749 * 2
def baseEnd_4184749 : Nat := 159169455957181695110533

theorem tailTrace_4184749 : CollatzResearch.WordTrace tailWord_4184749 prefixEnd_4184749 159169455957181695110533 := by
  unfold tailWord_4184749
  simp only [CollatzResearch.WordTrace]
  refine ⟨152630335116376546074277301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101753556744251030716184867 152630335116376546074277301)
  ·
    refine ⟨14309093917160301194463497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152630335116376546074277301 14309093917160301194463497)
    ·
      refine ⟨10731820437870225895847623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14309093917160301194463497 10731820437870225895847623)
      ·
        refine ⟨16097730656805338843771435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10731820437870225895847623 16097730656805338843771435)
        ·
          refine ⟨24146595985208008265657153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16097730656805338843771435 24146595985208008265657153)
          ·
            refine ⟨18109946988906006199242865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24146595985208008265657153 18109946988906006199242865)
            ·
              refine ⟨13582460241679504649432149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18109946988906006199242865 13582460241679504649432149)
              ·
                refine ⟨159169455957181695110533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13582460241679504649432149 159169455957181695110533)
                ·
                  rfl

theorem cell22_4184749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 8].length) (baseStart_4184749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184749 prefixEnd_4184749 := by exact prefixLift 4184749
  have htrace : WordTrace (prefixWord ++ tailWord_4184749) baseStart_4184749 baseEnd_4184749 := by
    simpa [prefixWord, tailWord_4184749, baseEnd_4184749] using wordTrace_append hprefix tailTrace_4184749
  have hstable : (prefixWord ++ tailWord_4184749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184749).length < 2 ^ (prefixWord ++ tailWord_4184749).sum := by decide
  have hdescent : baseEnd_4184749 < baseStart_4184749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184794 : List Nat := [3, 1, 1, 2, 2, 2, 1, 5, 5]
def baseStart_4184794 : Nat := 118140960795 + 4184794 * 2 ^ 59
def prefixEnd_4184794 : Nat := 4983230072969 + 3 ^ 40 * 4184794 * 2
def baseEnd_4184794 : Nat := 477513502678090046206553

theorem tailTrace_4184794 : CollatzResearch.WordTrace tailWord_4184794 prefixEnd_4184794 477513502678090046206553 := by
  unfold tailWord_4184794
  simp only [CollatzResearch.WordTrace]
  refine ⟨38157994100303379689916359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101754650934142345839776957 38157994100303379689916359)
  ·
    refine ⟨57236991150455069534874539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38157994100303379689916359 57236991150455069534874539)
    ·
      refine ⟨85855486725682604302311809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57236991150455069534874539 85855486725682604302311809)
      ·
        refine ⟨64391615044261953226733857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85855486725682604302311809 64391615044261953226733857)
        ·
          refine ⟨48293711283196464920050393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64391615044261953226733857 48293711283196464920050393)
          ·
            refine ⟨36220283462397348690037795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48293711283196464920050393 36220283462397348690037795)
            ·
              refine ⟨54330425193596023035056693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36220283462397348690037795 54330425193596023035056693)
              ·
                refine ⟨5093477361899627159536565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54330425193596023035056693 5093477361899627159536565)
                ·
                  refine ⟨477513502678090046206553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5093477361899627159536565 477513502678090046206553)
                  ·
                    rfl

theorem cell22_4184794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_4184794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184794 prefixEnd_4184794 := by exact prefixLift 4184794
  have htrace : WordTrace (prefixWord ++ tailWord_4184794) baseStart_4184794 baseEnd_4184794 := by
    simpa [prefixWord, tailWord_4184794, baseEnd_4184794] using wordTrace_append hprefix tailTrace_4184794
  have hstable : (prefixWord ++ tailWord_4184794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184794).length < 2 ^ (prefixWord ++ tailWord_4184794).sum := by decide
  have hdescent : baseEnd_4184794 < baseStart_4184794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184869 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_4184869 : Nat := 118140960795 + 4184869 * 2 ^ 59
def prefixEnd_4184869 : Nat := 4983230072969 + 3 ^ 40 * 4184869 * 2
def baseEnd_4184869 : Nat := 1432566182066994942994429

theorem tailTrace_4184869 : CollatzResearch.WordTrace tailWord_4184869 prefixEnd_4184869 1432566182066994942994429 := by
  unfold tailWord_4184869
  simp only [CollatzResearch.WordTrace]
  refine ⟨152634711875941806568645661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101756474583961204379097107 152634711875941806568645661)
  ·
    refine ⟨57238016953478177463242123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152634711875941806568645661 57238016953478177463242123)
    ·
      refine ⟨85857025430217266194863185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57238016953478177463242123 85857025430217266194863185)
      ·
        refine ⟨64392769072662949646147389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85857025430217266194863185 64392769072662949646147389)
        ·
          refine ⟨24147288402248606117305271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64392769072662949646147389 24147288402248606117305271)
          ·
            refine ⟨36220932603372909175957907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24147288402248606117305271 36220932603372909175957907)
            ·
              refine ⟨54331398905059363763936861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36220932603372909175957907 54331398905059363763936861)
              ·
                refine ⟨20374274589397261411476323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54331398905059363763936861 20374274589397261411476323)
                ·
                  refine ⟨30561411884095892117214485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20374274589397261411476323 30561411884095892117214485)
                  ·
                    refine ⟨1432566182066994942994429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30561411884095892117214485 1432566182066994942994429)
                    ·
                      rfl

theorem cell22_4184869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_4184869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184869 prefixEnd_4184869 := by exact prefixLift 4184869
  have htrace : WordTrace (prefixWord ++ tailWord_4184869) baseStart_4184869 baseEnd_4184869 := by
    simpa [prefixWord, tailWord_4184869, baseEnd_4184869] using wordTrace_append hprefix tailTrace_4184869
  have hstable : (prefixWord ++ tailWord_4184869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184869).length < 2 ^ (prefixWord ++ tailWord_4184869).sum := by decide
  have hdescent : baseEnd_4184869 < baseStart_4184869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184890 : List Nat := [3, 1, 1, 1, 6, 1, 3, 2, 4]
def baseStart_4184890 : Nat := 118140960795 + 4184890 * 2 ^ 59
def prefixEnd_4184890 : Nat := 4983230072969 + 3 ^ 40 * 4184890 * 2
def baseEnd_4184890 : Nat := 477524456932052629406455

theorem tailTrace_4184890 : CollatzResearch.WordTrace tailWord_4184890 prefixEnd_4184890 477524456932052629406455 := by
  unfold tailWord_4184890
  simp only [CollatzResearch.WordTrace]
  refine ⟨38158869452216431788790031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101756985205910484770106749 38158869452216431788790031)
  ·
    refine ⟨57238304178324647683185047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38158869452216431788790031 57238304178324647683185047)
    ·
      refine ⟨85857456267486971524777571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57238304178324647683185047 85857456267486971524777571)
      ·
        refine ⟨128786184401230457287166357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85857456267486971524777571 128786184401230457287166357)
        ·
          refine ⟨6036852393807677685335923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128786184401230457287166357 6036852393807677685335923)
          ·
            refine ⟨9055278590711516528003885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6036852393807677685335923 9055278590711516528003885)
            ·
              refine ⟨3395729471516818698001457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9055278590711516528003885 3395729471516818698001457)
              ·
                refine ⟨2546797103637614023501093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395729471516818698001457 2546797103637614023501093)
                ·
                  refine ⟨477524456932052629406455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2546797103637614023501093 477524456932052629406455)
                  ·
                    rfl

theorem cell22_4184890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_4184890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184890 prefixEnd_4184890 := by exact prefixLift 4184890
  have htrace : WordTrace (prefixWord ++ tailWord_4184890) baseStart_4184890 baseEnd_4184890 := by
    simpa [prefixWord, tailWord_4184890, baseEnd_4184890] using wordTrace_append hprefix tailTrace_4184890
  have hstable : (prefixWord ++ tailWord_4184890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184890).length < 2 ^ (prefixWord ++ tailWord_4184890).sum := by decide
  have hdescent : baseEnd_4184890 < baseStart_4184890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184905 : List Nat := [1, 2, 1, 1, 2, 7, 2, 1, 2, 3]
def baseStart_4184905 : Nat := 118140960795 + 4184905 * 2 ^ 59
def prefixEnd_4184905 : Nat := 4983230072969 + 3 ^ 40 * 4184905 * 2
def baseEnd_4184905 : Nat := 1432578505602702849094319

theorem tailTrace_4184905 : CollatzResearch.WordTrace tailWord_4184905 prefixEnd_4184905 1432578505602702849094319 := by
  unfold tailWord_4184905
  simp only [CollatzResearch.WordTrace]
  refine ⟨152636024903811384716956169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101757349935874256477970779 152636024903811384716956169)
  ·
    refine ⟨114477018677858538537717127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152636024903811384716956169 114477018677858538537717127)
    ·
      refine ⟨171715528016787807806575691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114477018677858538537717127 171715528016787807806575691)
      ·
        refine ⟨257573292025181711709863537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171715528016787807806575691 257573292025181711709863537)
        ·
          refine ⟨193179969018886283782397653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257573292025181711709863537 193179969018886283782397653)
          ·
            refine ⟨4527655523880147276149945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 193179969018886283782397653 4527655523880147276149945)
            ·
              refine ⟨3395741642910110457112459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4527655523880147276149945 3395741642910110457112459)
              ·
                refine ⟨5093612464365165685668689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3395741642910110457112459 5093612464365165685668689)
                ·
                  refine ⟨3820209348273874264251517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5093612464365165685668689 3820209348273874264251517)
                  ·
                    refine ⟨1432578505602702849094319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3820209348273874264251517 1432578505602702849094319)
                    ·
                      rfl

theorem cell22_4184905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 2, 3].length) (baseStart_4184905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184905 prefixEnd_4184905 := by exact prefixLift 4184905
  have htrace : WordTrace (prefixWord ++ tailWord_4184905) baseStart_4184905 baseEnd_4184905 := by
    simpa [prefixWord, tailWord_4184905, baseEnd_4184905] using wordTrace_append hprefix tailTrace_4184905
  have hstable : (prefixWord ++ tailWord_4184905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184905).length < 2 ^ (prefixWord ++ tailWord_4184905).sum := by decide
  have hdescent : baseEnd_4184905 < baseStart_4184905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184929 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 7]
def baseStart_4184929 : Nat := 118140960795 + 4184929 * 2 ^ 59
def prefixEnd_4184929 : Nat := 4983230072969 + 3 ^ 40 * 4184929 * 2
def baseEnd_4184929 : Nat := 477528907097724928831415

theorem tailTrace_4184929 : CollatzResearch.WordTrace tailWord_4184929 prefixEnd_4184929 477528907097724928831415 := by
  unfold tailWord_4184929
  simp only [CollatzResearch.WordTrace]
  refine ⟨152636900255724436815829841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101757933503816291210553227 152636900255724436815829841)
  ·
    refine ⟨114477675191793327611872381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152636900255724436815829841 114477675191793327611872381)
    ·
      refine ⟨42929128196922497854452143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114477675191793327611872381 42929128196922497854452143)
      ·
        refine ⟨64393692295383746781678215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42929128196922497854452143 64393692295383746781678215)
        ·
          refine ⟨96590538443075620172517323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64393692295383746781678215 96590538443075620172517323)
          ·
            refine ⟨144885807664613430258775985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96590538443075620172517323 144885807664613430258775985)
            ·
              refine ⟨108664355748460072694081989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144885807664613430258775985 108664355748460072694081989)
              ·
                refine ⟨20374566702836263630140373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108664355748460072694081989 20374566702836263630140373)
                ·
                  refine ⟨477528907097724928831415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20374566702836263630140373 477528907097724928831415)
                  ·
                    rfl

theorem cell22_4184929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_4184929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184929 prefixEnd_4184929 := by exact prefixLift 4184929
  have htrace : WordTrace (prefixWord ++ tailWord_4184929) baseStart_4184929 baseEnd_4184929 := by
    simpa [prefixWord, tailWord_4184929, baseEnd_4184929] using wordTrace_append hprefix tailTrace_4184929
  have hstable : (prefixWord ++ tailWord_4184929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184929).length < 2 ^ (prefixWord ++ tailWord_4184929).sum := by decide
  have hdescent : baseEnd_4184929 < baseStart_4184929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4184946 : List Nat := [3, 2, 1, 2, 1, 1, 3, 4, 5]
def baseStart_4184946 : Nat := 118140960795 + 4184946 * 2 ^ 59
def prefixEnd_4184946 : Nat := 4983230072969 + 3 ^ 40 * 4184946 * 2
def baseEnd_4184946 : Nat := 477530846913530802939731

theorem tailTrace_4184946 : CollatzResearch.WordTrace tailWord_4184946 prefixEnd_4184946 477530846913530802939731 := by
  unfold tailWord_4184946
  simp only [CollatzResearch.WordTrace]
  refine ⟨38159380074165712179799673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101758346864441899146132461 38159380074165712179799673)
  ·
    refine ⟨28619535055624284134849755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38159380074165712179799673 28619535055624284134849755)
    ·
      refine ⟨42929302583436426202274633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28619535055624284134849755 42929302583436426202274633)
      ·
        refine ⟨32196976937577319651705975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42929302583436426202274633 32196976937577319651705975)
        ·
          refine ⟨48295465406365979477558963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32196976937577319651705975 48295465406365979477558963)
          ·
            refine ⟨72443198109548969216338445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48295465406365979477558963 72443198109548969216338445)
            ·
              refine ⟨27166199291080863456126917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72443198109548969216338445 27166199291080863456126917)
              ·
                refine ⟨5093662367077661898023797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27166199291080863456126917 5093662367077661898023797)
                ·
                  refine ⟨477530846913530802939731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5093662367077661898023797 477530846913530802939731)
                  ·
                    rfl

theorem cell22_4184946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_4184946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4184946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4184946 prefixEnd_4184946 := by exact prefixLift 4184946
  have htrace : WordTrace (prefixWord ++ tailWord_4184946) baseStart_4184946 baseEnd_4184946 := by
    simpa [prefixWord, tailWord_4184946, baseEnd_4184946] using wordTrace_append hprefix tailTrace_4184946
  have hstable : (prefixWord ++ tailWord_4184946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4184946).length < 2 ^ (prefixWord ++ tailWord_4184946).sum := by decide
  have hdescent : baseEnd_4184946 < baseStart_4184946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4184946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185036 : List Nat := [2, 2, 1, 4, 1, 1, 3, 8]
def baseStart_4185036 : Nat := 118140960795 + 4185036 * 2 ^ 59
def prefixEnd_4185036 : Nat := 4983230072969 + 3 ^ 40 * 4185036 * 2
def baseEnd_4185036 : Nat := 159180372175540241563213

theorem tailTrace_4185036 : CollatzResearch.WordTrace tailWord_4185036 prefixEnd_4185036 159180372175540241563213 := by
  unfold tailWord_4185036
  simp only [CollatzResearch.WordTrace]
  refine ⟨76320401433168397044987481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101760535244224529393316641 76320401433168397044987481)
  ·
    refine ⟨57240301074876297783740611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76320401433168397044987481 57240301074876297783740611)
    ·
      refine ⟨85860451612314446675610917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57240301074876297783740611 85860451612314446675610917)
      ·
        refine ⟨16098834677308958751677047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85860451612314446675610917 16098834677308958751677047)
        ·
          refine ⟨24148252015963438127515571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16098834677308958751677047 24148252015963438127515571)
          ·
            refine ⟨36222378023945157191273357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24148252015963438127515571 36222378023945157191273357)
            ·
              refine ⟨13583391758979433946727509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36222378023945157191273357 13583391758979433946727509)
              ·
                refine ⟨159180372175540241563213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13583391758979433946727509 159180372175540241563213)
                ·
                  rfl

theorem cell22_4185036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 8].length) (baseStart_4185036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185036 prefixEnd_4185036 := by exact prefixLift 4185036
  have htrace : WordTrace (prefixWord ++ tailWord_4185036) baseStart_4185036 baseEnd_4185036 := by
    simpa [prefixWord, tailWord_4185036, baseEnd_4185036] using wordTrace_append hprefix tailTrace_4185036
  have hstable : (prefixWord ++ tailWord_4185036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185036).length < 2 ^ (prefixWord ++ tailWord_4185036).sum := by decide
  have hdescent : baseEnd_4185036 < baseStart_4185036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185042 : List Nat := [3, 2, 2, 3, 1, 3, 1, 3, 4]
def baseStart_4185042 : Nat := 118140960795 + 4185042 * 2 ^ 59
def prefixEnd_4185042 : Nat := 4983230072969 + 3 ^ 40 * 4185042 * 2
def baseEnd_4185042 : Nat := 477541801167493386139633

theorem tailTrace_4185042 : CollatzResearch.WordTrace tailWord_4185042 prefixEnd_4185042 477541801167493386139633 := by
  unfold tailWord_4185042
  simp only [CollatzResearch.WordTrace]
  refine ⟨38160255426078764278673345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101760681136210038076462253 38160255426078764278673345)
  ·
    refine ⟨28620191569559073209005009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38160255426078764278673345 28620191569559073209005009)
    ·
      refine ⟨21465143677169304906753757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28620191569559073209005009 21465143677169304906753757)
      ·
        refine ⟨8049428878938489340032659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21465143677169304906753757 8049428878938489340032659)
        ·
          refine ⟨12074143318407734010048989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8049428878938489340032659 12074143318407734010048989)
          ·
            refine ⟨4527803744402900253768371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12074143318407734010048989 4527803744402900253768371)
            ·
              refine ⟨6791705616604350380652557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4527803744402900253768371 6791705616604350380652557)
              ·
                refine ⟨2546889606226631392744709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6791705616604350380652557 2546889606226631392744709)
                ·
                  refine ⟨477541801167493386139633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2546889606226631392744709 477541801167493386139633)
                  ·
                    rfl

theorem cell22_4185042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_4185042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185042 prefixEnd_4185042 := by exact prefixLift 4185042
  have htrace : WordTrace (prefixWord ++ tailWord_4185042) baseStart_4185042 baseEnd_4185042 := by
    simpa [prefixWord, tailWord_4185042, baseEnd_4185042] using wordTrace_append hprefix tailTrace_4185042
  have hstable : (prefixWord ++ tailWord_4185042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185042).length < 2 ^ (prefixWord ++ tailWord_4185042).sum := by decide
  have hdescent : baseEnd_4185042 < baseStart_4185042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185053 : List Nat := [1, 4, 3, 1, 2, 3, 8]
def baseStart_4185053 : Nat := 118140960795 + 4185053 * 2 ^ 59
def prefixEnd_4185053 : Nat := 4983230072969 + 3 ^ 40 * 4185053 * 2
def baseEnd_4185053 : Nat := 53060339593602955421995

theorem tailTrace_4185053 : CollatzResearch.WordTrace tailWord_4185053 prefixEnd_4185053 53060339593602955421995 := by
  unfold tailWord_4185053
  simp only [CollatzResearch.WordTrace]
  refine ⟨152641422907275205993343813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101760948604850137328895875 152641422907275205993343813)
  ·
    refine ⟨28620266795114101123751965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152641422907275205993343813 28620266795114101123751965)
    ·
      refine ⟨10732600048167787921406987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28620266795114101123751965 10732600048167787921406987)
      ·
        refine ⟨16098900072251681882110481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10732600048167787921406987 16098900072251681882110481)
        ·
          refine ⟨12074175054188761411582861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16098900072251681882110481 12074175054188761411582861)
          ·
            refine ⟨4527815645320785529343573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12074175054188761411582861 4527815645320785529343573)
            ·
              refine ⟨53060339593602955421995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4527815645320785529343573 53060339593602955421995)
              ·
                rfl

theorem cell22_4185053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 8].length) (baseStart_4185053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185053 prefixEnd_4185053 := by exact prefixLift 4185053
  have htrace : WordTrace (prefixWord ++ tailWord_4185053) baseStart_4185053 baseEnd_4185053 := by
    simpa [prefixWord, tailWord_4185053, baseEnd_4185053] using wordTrace_append hprefix tailTrace_4185053
  have hstable : (prefixWord ++ tailWord_4185053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185053).length < 2 ^ (prefixWord ++ tailWord_4185053).sum := by decide
  have hdescent : baseEnd_4185053 < baseStart_4185053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185119 : List Nat := [1, 1, 2, 4, 1, 5, 2, 2, 1, 3]
def baseStart_4185119 : Nat := 118140960795 + 4185119 * 2 ^ 59
def prefixEnd_4185119 : Nat := 4983230072969 + 3 ^ 40 * 4185119 * 2
def baseEnd_4185119 : Nat := 1432651762176077624243663

theorem tailTrace_4185119 : CollatzResearch.WordTrace tailWord_4185119 prefixEnd_4185119 1432651762176077624243663 := by
  unfold tailWord_4185119
  simp only [CollatzResearch.WordTrace]
  refine ⟨152643830125036099265246411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101762553416690732843497607 152643830125036099265246411)
  ·
    refine ⟨228965745187554148897869617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152643830125036099265246411 228965745187554148897869617)
    ·
      refine ⟨171724308890665611673402213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 228965745187554148897869617 171724308890665611673402213)
      ·
        refine ⟨32198307916999802188762915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171724308890665611673402213 32198307916999802188762915)
        ·
          refine ⟨48297461875499703283144373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32198307916999802188762915 48297461875499703283144373)
          ·
            refine ⟨4527887050828097182794785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48297461875499703283144373 4527887050828097182794785)
            ·
              refine ⟨3395915288121072887096089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4527887050828097182794785 3395915288121072887096089)
              ·
                refine ⟨2546936466090804665322067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3395915288121072887096089 2546936466090804665322067)
                ·
                  refine ⟨3820404699136206997983101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2546936466090804665322067 3820404699136206997983101)
                  ·
                    refine ⟨1432651762176077624243663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3820404699136206997983101 1432651762176077624243663)
                    ·
                      rfl

theorem cell22_4185119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 1, 3].length) (baseStart_4185119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185119 prefixEnd_4185119 := by exact prefixLift 4185119
  have htrace : WordTrace (prefixWord ++ tailWord_4185119) baseStart_4185119 baseEnd_4185119 := by
    simpa [prefixWord, tailWord_4185119, baseEnd_4185119] using wordTrace_append hprefix tailTrace_4185119
  have hstable : (prefixWord ++ tailWord_4185119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185119).length < 2 ^ (prefixWord ++ tailWord_4185119).sum := by decide
  have hdescent : baseEnd_4185119 < baseStart_4185119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185130 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 2, 5]
def baseStart_4185130 : Nat := 118140960795 + 4185130 * 2 ^ 59
def prefixEnd_4185130 : Nat := 4983230072969 + 3 ^ 40 * 4185130 * 2
def baseEnd_4185130 : Nat := 1432655527700877262218629

theorem tailTrace_4185130 : CollatzResearch.WordTrace tailWord_4185130 prefixEnd_4185130 1432655527700877262218629 := by
  unfold tailWord_4185130
  simp only [CollatzResearch.WordTrace]
  refine ⟨38161057831999062035974211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101762820885330832095931229 38161057831999062035974211)
  ·
    refine ⟨57241586747998593053961317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38161057831999062035974211 57241586747998593053961317)
    ·
      refine ⟨10732797515249736197617747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57241586747998593053961317 10732797515249736197617747)
      ·
        refine ⟨16099196272874604296426621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10732797515249736197617747 16099196272874604296426621)
        ·
          refine ⟨6037198602327976611159983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16099196272874604296426621 6037198602327976611159983)
          ·
            refine ⟨9055797903491964916739975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037198602327976611159983 9055797903491964916739975)
            ·
              refine ⟨13583696855237947375109963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9055797903491964916739975 13583696855237947375109963)
              ·
                refine ⟨20375545282856921062664945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13583696855237947375109963 20375545282856921062664945)
                ·
                  refine ⟨15281658962142690796998709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20375545282856921062664945 15281658962142690796998709)
                  ·
                    refine ⟨1432655527700877262218629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15281658962142690796998709 1432655527700877262218629)
                    ·
                      rfl

theorem cell22_4185130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_4185130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185130 prefixEnd_4185130 := by exact prefixLift 4185130
  have htrace : WordTrace (prefixWord ++ tailWord_4185130) baseStart_4185130 baseEnd_4185130 := by
    simpa [prefixWord, tailWord_4185130, baseEnd_4185130] using wordTrace_append hprefix tailTrace_4185130
  have hstable : (prefixWord ++ tailWord_4185130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185130).length < 2 ^ (prefixWord ++ tailWord_4185130).sum := by decide
  have hdescent : baseEnd_4185130 < baseStart_4185130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185160 : List Nat := [2, 1, 3, 1, 1, 1, 6, 3, 4]
def baseStart_4185160 : Nat := 118140960795 + 4185160 * 2 ^ 59
def prefixEnd_4185160 : Nat := 4983230072969 + 3 ^ 40 * 4185160 * 2
def baseEnd_4185160 : Nat := 477555265771322394656179

theorem tailTrace_4185160 : CollatzResearch.WordTrace tailWord_4185160 prefixEnd_4185160 477555265771322394656179 := by
  unfold tailWord_4185160
  simp only [CollatzResearch.WordTrace]
  refine ⟨76322662758943781633744467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101763550345258375511659289 76322662758943781633744467)
  ·
    refine ⟨114483994138415672450616701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76322662758943781633744467 114483994138415672450616701)
    ·
      refine ⟨42931497801905877168981263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114483994138415672450616701 42931497801905877168981263)
      ·
        refine ⟨64397246702858815753471895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42931497801905877168981263 64397246702858815753471895)
        ·
          refine ⟨96595870054288223630207843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64397246702858815753471895 96595870054288223630207843)
          ·
            refine ⟨144893805081432335445311765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96595870054288223630207843 144893805081432335445311765)
            ·
              refine ⟨6791897113192140723998989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144893805081432335445311765 6791897113192140723998989)
              ·
                refine ⟨2546961417447052771499621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6791897113192140723998989 2546961417447052771499621)
                ·
                  refine ⟨477555265771322394656179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2546961417447052771499621 477555265771322394656179)
                  ·
                    rfl

theorem cell22_4185160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 4].length) (baseStart_4185160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185160 prefixEnd_4185160 := by exact prefixLift 4185160
  have htrace : WordTrace (prefixWord ++ tailWord_4185160) baseStart_4185160 baseEnd_4185160 := by
    simpa [prefixWord, tailWord_4185160, baseEnd_4185160] using wordTrace_append hprefix tailTrace_4185160
  have hstable : (prefixWord ++ tailWord_4185160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185160).length < 2 ^ (prefixWord ++ tailWord_4185160).sum := by decide
  have hdescent : baseEnd_4185160 < baseStart_4185160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185173 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_4185173 : Nat := 118140960795 + 4185173 * 2 ^ 59
def prefixEnd_4185173 : Nat := 4983230072969 + 3 ^ 40 * 4185173 * 2
def baseEnd_4185173 : Nat := 1432670247479639483393497

theorem tailTrace_4185173 : CollatzResearch.WordTrace tailWord_4185173 prefixEnd_4185173 1432670247479639483393497 := by
  unfold tailWord_4185173
  simp only [CollatzResearch.WordTrace]
  refine ⟨152645799666840466487712173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101763866444560310991808115 152645799666840466487712173)
  ·
    refine ⟨57242174875065174932892065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152645799666840466487712173 57242174875065174932892065)
    ·
      refine ⟨42931631156298881199669049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57242174875065174932892065 42931631156298881199669049)
      ·
        refine ⟨32198723367224160899751787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42931631156298881199669049 32198723367224160899751787)
        ·
          refine ⟨48298085050836241349627681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32198723367224160899751787 48298085050836241349627681)
          ·
            refine ⟨36223563788127181012220761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48298085050836241349627681 36223563788127181012220761)
            ·
              refine ⟨27167672841095385759165571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36223563788127181012220761 27167672841095385759165571)
              ·
                refine ⟨40751509261643078638748357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27167672841095385759165571 40751509261643078638748357)
                ·
                  refine ⟨7640907986558077244765317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40751509261643078638748357 7640907986558077244765317)
                  ·
                    refine ⟨1432670247479639483393497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7640907986558077244765317 1432670247479639483393497)
                    ·
                      rfl

theorem cell22_4185173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_4185173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185173 prefixEnd_4185173 := by exact prefixLift 4185173
  have htrace : WordTrace (prefixWord ++ tailWord_4185173) baseStart_4185173 baseEnd_4185173 := by
    simpa [prefixWord, tailWord_4185173, baseEnd_4185173] using wordTrace_append hprefix tailTrace_4185173
  have hstable : (prefixWord ++ tailWord_4185173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185173).length < 2 ^ (prefixWord ++ tailWord_4185173).sum := by decide
  have hdescent : baseEnd_4185173 < baseStart_4185173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185248 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 1, 7]
def baseStart_4185248 : Nat := 118140960795 + 4185248 * 2 ^ 59
def prefixEnd_4185248 : Nat := 4983230072969 + 3 ^ 40 * 4185248 * 2
def baseEnd_4185248 : Nat := 1432695921512364287768267

theorem tailTrace_4185248 : CollatzResearch.WordTrace tailWord_4185248 prefixEnd_4185248 1432695921512364287768267 := by
  unfold tailWord_4185248
  simp only [CollatzResearch.WordTrace]
  refine ⟨76324267570784377148346199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101765690094379169531128265 76324267570784377148346199)
  ·
    refine ⟨114486401356176565722519299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76324267570784377148346199 114486401356176565722519299)
    ·
      refine ⟨171729602034264848583778949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114486401356176565722519299 171729602034264848583778949)
      ·
        refine ⟨32199300381424659109458553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171729602034264848583778949 32199300381424659109458553)
        ·
          refine ⟨24149475286068494332093915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32199300381424659109458553 24149475286068494332093915)
          ·
            refine ⟨36224212929102741498140873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24149475286068494332093915 36224212929102741498140873)
            ·
              refine ⟨27168159696827056123605655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36224212929102741498140873 27168159696827056123605655)
              ·
                refine ⟨40752239545240584185408483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27168159696827056123605655 40752239545240584185408483)
                ·
                  refine ⟨61128359317860876278112725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40752239545240584185408483 61128359317860876278112725)
                  ·
                    refine ⟨1432695921512364287768267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61128359317860876278112725 1432695921512364287768267)
                    ·
                      rfl

theorem cell22_4185248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_4185248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185248 prefixEnd_4185248 := by exact prefixLift 4185248
  have htrace : WordTrace (prefixWord ++ tailWord_4185248) baseStart_4185248 baseEnd_4185248 := by
    simpa [prefixWord, tailWord_4185248, baseEnd_4185248] using wordTrace_append hprefix tailTrace_4185248
  have hstable : (prefixWord ++ tailWord_4185248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185248).length < 2 ^ (prefixWord ++ tailWord_4185248).sum := by decide
  have hdescent : baseEnd_4185248 < baseStart_4185248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185340 : List Nat := [2, 2, 2, 1, 5, 1, 9]
def baseStart_4185340 : Nat := 118140960795 + 4185340 * 2 ^ 59
def prefixEnd_4185340 : Nat := 4983230072969 + 3 ^ 40 * 4185340 * 2
def baseEnd_4185340 : Nat := 53063978333055804239555

theorem tailTrace_4185340 : CollatzResearch.WordTrace tailWord_4185340 prefixEnd_4185340 53063978333055804239555 := by
  unfold tailWord_4185340
  simp only [CollatzResearch.WordTrace]
  refine ⟨76325945328617727004520737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101767927104823636006027649 76325945328617727004520737)
  ·
    refine ⟨57244458996463295253390553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76325945328617727004520737 57244458996463295253390553)
    ·
      refine ⟨42933344247347471440042915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57244458996463295253390553 42933344247347471440042915)
      ·
        refine ⟨64400016371021207160064373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42933344247347471440042915 64400016371021207160064373)
        ·
          refine ⟨6037501534783238171256035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64400016371021207160064373 6037501534783238171256035)
          ·
            refine ⟨9056252302174857256884053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037501534783238171256035 9056252302174857256884053)
            ·
              refine ⟨53063978333055804239555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9056252302174857256884053 53063978333055804239555)
              ·
                rfl

theorem cell22_4185340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 9].length) (baseStart_4185340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185340 prefixEnd_4185340 := by exact prefixLift 4185340
  have htrace : WordTrace (prefixWord ++ tailWord_4185340) baseStart_4185340 baseEnd_4185340 := by
    simpa [prefixWord, tailWord_4185340, baseEnd_4185340] using wordTrace_append hprefix tailTrace_4185340
  have hstable : (prefixWord ++ tailWord_4185340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185340).length < 2 ^ (prefixWord ++ tailWord_4185340).sum := by decide
  have hdescent : baseEnd_4185340 < baseStart_4185340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185372 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 3, 3]
def baseStart_4185372 : Nat := 118140960795 + 4185372 * 2 ^ 59
def prefixEnd_4185372 : Nat := 4983230072969 + 3 ^ 40 * 4185372 * 2
def baseEnd_4185372 : Nat := 1432738369246469297667887

theorem tailTrace_4185372 : CollatzResearch.WordTrace tailWord_4185372 prefixEnd_4185372 1432738369246469297667887 := by
  unfold tailWord_4185372
  simp only [CollatzResearch.WordTrace]
  refine ⟨76326528896559761737103185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101768705195413015649470913 76326528896559761737103185)
  ·
    refine ⟨57244896672419821302827389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76326528896559761737103185 57244896672419821302827389)
    ·
      refine ⟨21466836252157432988560271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57244896672419821302827389 21466836252157432988560271)
      ·
        refine ⟨32200254378236149482840407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21466836252157432988560271 32200254378236149482840407)
        ·
          refine ⟨48300381567354224224260611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32200254378236149482840407 48300381567354224224260611)
          ·
            refine ⟨72450572351031336336390917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48300381567354224224260611 72450572351031336336390917)
            ·
              refine ⟨13584482315818375563073297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72450572351031336336390917 13584482315818375563073297)
              ·
                refine ⟨10188361736863781672304973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13584482315818375563073297 10188361736863781672304973)
                ·
                  refine ⟨3820635651323918127114365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10188361736863781672304973 3820635651323918127114365)
                  ·
                    refine ⟨1432738369246469297667887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3820635651323918127114365 1432738369246469297667887)
                    ·
                      rfl

theorem cell22_4185372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_4185372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185372 prefixEnd_4185372 := by exact prefixLift 4185372
  have htrace : WordTrace (prefixWord ++ tailWord_4185372) baseStart_4185372 baseEnd_4185372 := by
    simpa [prefixWord, tailWord_4185372, baseEnd_4185372] using wordTrace_append hprefix tailTrace_4185372
  have hstable : (prefixWord ++ tailWord_4185372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185372).length < 2 ^ (prefixWord ++ tailWord_4185372).sum := by decide
  have hdescent : baseEnd_4185372 < baseStart_4185372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185374 : List Nat := [4, 3, 2, 1, 2, 1, 1, 8]
def baseStart_4185374 : Nat := 118140960795 + 4185374 * 2 ^ 59
def prefixEnd_4185374 : Nat := 4983230072969 + 3 ^ 40 * 4185374 * 2
def baseEnd_4185374 : Nat := 159193228209704662124209

theorem tailTrace_4185374 : CollatzResearch.WordTrace tailWord_4185374 prefixEnd_4185374 159193228209704662124209 := by
  unfold tailWord_4185374
  simp only [CollatzResearch.WordTrace]
  refine ⟨19081641342389034726972397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101768753826074851877186117 19081641342389034726972397)
  ·
    refine ⟨7155615503395888022614649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19081641342389034726972397 7155615503395888022614649)
    ·
      refine ⟨5366711627546916016960987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7155615503395888022614649 5366711627546916016960987)
      ·
        refine ⟨8050067441320374025441481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5366711627546916016960987 8050067441320374025441481)
        ·
          refine ⟨6037550580990280519081111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8050067441320374025441481 6037550580990280519081111)
          ·
            refine ⟨9056325871485420778621667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037550580990280519081111 9056325871485420778621667)
            ·
              refine ⟨13584488807228131167932501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9056325871485420778621667 13584488807228131167932501)
              ·
                refine ⟨159193228209704662124209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13584488807228131167932501 159193228209704662124209)
                ·
                  rfl

theorem cell22_4185374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_4185374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185374 prefixEnd_4185374 := by exact prefixLift 4185374
  have htrace : WordTrace (prefixWord ++ tailWord_4185374) baseStart_4185374 baseEnd_4185374 := by
    simpa [prefixWord, tailWord_4185374, baseEnd_4185374] using wordTrace_append hprefix tailTrace_4185374
  have hstable : (prefixWord ++ tailWord_4185374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185374).length < 2 ^ (prefixWord ++ tailWord_4185374).sum := by decide
  have hdescent : baseEnd_4185374 < baseStart_4185374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185479 : List Nat := [1, 1, 4, 2, 2, 2, 2, 3, 2, 3]
def baseStart_4185479 : Nat := 118140960795 + 4185479 * 2 ^ 59
def prefixEnd_4185479 : Nat := 4983230072969 + 3 ^ 40 * 4185479 * 2
def baseEnd_4185479 : Nat := 1432774997533156685242559

theorem tailTrace_4185479 : CollatzResearch.WordTrace tailWord_4185479 prefixEnd_4185479 1432774997533156685242559 := by
  unfold tailWord_4185479
  simp only [CollatzResearch.WordTrace]
  refine ⟨152656960403731880748351491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101771306935821253832234327 152656960403731880748351491)
  ·
    refine ⟨228985440605597821122527237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152656960403731880748351491 228985440605597821122527237)
    ·
      refine ⟨42934770113549591460473857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228985440605597821122527237 42934770113549591460473857)
      ·
        refine ⟨32201077585162193595355393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42934770113549591460473857 32201077585162193595355393)
        ·
          refine ⟨24150808188871645196516545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32201077585162193595355393 24150808188871645196516545)
          ·
            refine ⟨18113106141653733897387409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24150808188871645196516545 18113106141653733897387409)
            ·
              refine ⟨13584829606240300423040557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18113106141653733897387409 13584829606240300423040557)
              ·
                refine ⟨5094311102340112658640209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13584829606240300423040557 5094311102340112658640209)
                ·
                  refine ⟨3820733326755084493980157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5094311102340112658640209 3820733326755084493980157)
                  ·
                    refine ⟨1432774997533156685242559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3820733326755084493980157 1432774997533156685242559)
                    ·
                      rfl

theorem cell22_4185479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_4185479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185479 prefixEnd_4185479 := by exact prefixLift 4185479
  have htrace : WordTrace (prefixWord ++ tailWord_4185479) baseStart_4185479 baseEnd_4185479 := by
    simpa [prefixWord, tailWord_4185479, baseEnd_4185479] using wordTrace_append hprefix tailTrace_4185479
  have hstable : (prefixWord ++ tailWord_4185479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185479).length < 2 ^ (prefixWord ++ tailWord_4185479).sum := by decide
  have hdescent : baseEnd_4185479 < baseStart_4185479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185500 : List Nat := [2, 2, 3, 4, 2, 1, 2, 1, 1, 4]
def baseStart_4185500 : Nat := 118140960795 + 4185500 * 2 ^ 59
def prefixEnd_4185500 : Nat := 4983230072969 + 3 ^ 40 * 4185500 * 2
def baseEnd_4185500 : Nat := 1432782186262319630467495

theorem tailTrace_4185500 : CollatzResearch.WordTrace tailWord_4185500 prefixEnd_4185500 1432782186262319630467495 := by
  unfold tailWord_4185500
  simp only [CollatzResearch.WordTrace]
  refine ⟨76328863168327900667432977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101771817557770534223243969 76328863168327900667432977)
  ·
    refine ⟨57246647376245925500574733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76328863168327900667432977 57246647376245925500574733)
    ·
      refine ⟨21467492766092222062715525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57246647376245925500574733 21467492766092222062715525)
      ·
        refine ⟨4025154893642291636759161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21467492766092222062715525 4025154893642291636759161)
        ·
          refine ⟨3018866170231718727569371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4025154893642291636759161 3018866170231718727569371)
          ·
            refine ⟨4528299255347578091354057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3018866170231718727569371 4528299255347578091354057)
            ·
              refine ⟨3396224441510683568515543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4528299255347578091354057 3396224441510683568515543)
              ·
                refine ⟨5094336662266025352773315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3396224441510683568515543 5094336662266025352773315)
                ·
                  refine ⟨7641504993399038029159973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5094336662266025352773315 7641504993399038029159973)
                  ·
                    refine ⟨1432782186262319630467495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7641504993399038029159973 1432782186262319630467495)
                    ·
                      rfl

theorem cell22_4185500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_4185500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185500 prefixEnd_4185500 := by exact prefixLift 4185500
  have htrace : WordTrace (prefixWord ++ tailWord_4185500) baseStart_4185500 baseEnd_4185500 := by
    simpa [prefixWord, tailWord_4185500, baseEnd_4185500] using wordTrace_append hprefix tailTrace_4185500
  have hstable : (prefixWord ++ tailWord_4185500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185500).length < 2 ^ (prefixWord ++ tailWord_4185500).sum := by decide
  have hdescent : baseEnd_4185500 < baseStart_4185500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185507 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 5, 3]
def baseStart_4185507 : Nat := 118140960795 + 4185507 * 2 ^ 59
def prefixEnd_4185507 : Nat := 4983230072969 + 3 ^ 40 * 4185507 * 2
def baseEnd_4185507 : Nat := 1432784582505373945542473

theorem tailTrace_4185507 : CollatzResearch.WordTrace tailWord_4185507 prefixEnd_4185507 1432784582505373945542473 := by
  unfold tailWord_4185507
  simp only [CollatzResearch.WordTrace]
  refine ⟨152657981647630441530370775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101771987765086961020247183 152657981647630441530370775)
  ·
    refine ⟨228986972471445662295556163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152657981647630441530370775 228986972471445662295556163)
    ·
      refine ⟨343480458707168493443334245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228986972471445662295556163 343480458707168493443334245)
      ·
        refine ⟨64402586007594092520625171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343480458707168493443334245 64402586007594092520625171)
        ·
          refine ⟨96603879011391138780937757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64402586007594092520625171 96603879011391138780937757)
          ·
            refine ⟨36226454629271677042851659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96603879011391138780937757 36226454629271677042851659)
            ·
              refine ⟨54339681943907515564277489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36226454629271677042851659 54339681943907515564277489)
              ·
                refine ⟨40754761457930636673208117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54339681943907515564277489 40754761457930636673208117)
                ·
                  refine ⟨3820758886680997188113261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40754761457930636673208117 3820758886680997188113261)
                  ·
                    refine ⟨1432784582505373945542473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3820758886680997188113261 1432784582505373945542473)
                    ·
                      rfl

theorem cell22_4185507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 3].length) (baseStart_4185507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185507 prefixEnd_4185507 := by exact prefixLift 4185507
  have htrace : WordTrace (prefixWord ++ tailWord_4185507) baseStart_4185507 baseEnd_4185507 := by
    simpa [prefixWord, tailWord_4185507, baseEnd_4185507] using wordTrace_append hprefix tailTrace_4185507
  have hstable : (prefixWord ++ tailWord_4185507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185507).length < 2 ^ (prefixWord ++ tailWord_4185507).sum := by decide
  have hdescent : baseEnd_4185507 < baseStart_4185507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185629 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_4185629 : Nat := 118140960795 + 4185629 * 2 ^ 59
def prefixEnd_4185629 : Nat := 4983230072969 + 3 ^ 40 * 4185629 * 2
def baseEnd_4185629 : Nat := 1432826345598606293992099

theorem tailTrace_4185629 : CollatzResearch.WordTrace tailWord_4185629 prefixEnd_4185629 1432826345598606293992099 := by
  unfold tailWord_4185629
  simp only [CollatzResearch.WordTrace]
  refine ⟨152662431353188456366311941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101774954235458970910874627 152662431353188456366311941)
  ·
    refine ⟨28624205878722835568683489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152662431353188456366311941 28624205878722835568683489)
    ·
      refine ⟨21468154409042126676512617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28624205878722835568683489 21468154409042126676512617)
      ·
        refine ⟨16101115806781595007384463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21468154409042126676512617 16101115806781595007384463)
        ·
          refine ⟨24151673710172392511076695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16101115806781595007384463 24151673710172392511076695)
          ·
            refine ⟨36227510565258588766615043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24151673710172392511076695 36227510565258588766615043)
            ·
              refine ⟨54341265847887883149922565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36227510565258588766615043 54341265847887883149922565)
              ·
                refine ⟨10188987346478978090610481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54341265847887883149922565 10188987346478978090610481)
                ·
                  refine ⟨7641740509859233567957861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10188987346478978090610481 7641740509859233567957861)
                  ·
                    refine ⟨1432826345598606293992099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7641740509859233567957861 1432826345598606293992099)
                    ·
                      rfl

theorem cell22_4185629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_4185629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185629 prefixEnd_4185629 := by exact prefixLift 4185629
  have htrace : WordTrace (prefixWord ++ tailWord_4185629) baseStart_4185629 baseEnd_4185629 := by
    simpa [prefixWord, tailWord_4185629, baseEnd_4185629] using wordTrace_append hprefix tailTrace_4185629
  have hstable : (prefixWord ++ tailWord_4185629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185629).length < 2 ^ (prefixWord ++ tailWord_4185629).sum := by decide
  have hdescent : baseEnd_4185629 < baseStart_4185629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185633 : List Nat := [1, 2, 3, 2, 2, 4, 2, 2, 4]
def baseStart_4185633 : Nat := 118140960795 + 4185633 * 2 ^ 59
def prefixEnd_4185633 : Nat := 4983230072969 + 3 ^ 40 * 4185633 * 2
def baseEnd_4185633 : Nat := 477609238293450538964029

theorem tailTrace_4185633 : CollatzResearch.WordTrace tailWord_4185633 prefixEnd_4185633 477609238293450538964029 := by
  unfold tailWord_4185633
  simp only [CollatzResearch.WordTrace]
  refine ⟨152662577245173965049457553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101775051496782643366305035 152662577245173965049457553)
  ·
    refine ⟨114496932933880473787093165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152662577245173965049457553 114496932933880473787093165)
    ·
      refine ⟨42936349850205177670159937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114496932933880473787093165 42936349850205177670159937)
      ·
        refine ⟨32202262387653883252619953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42936349850205177670159937 32202262387653883252619953)
        ·
          refine ⟨24151696790740412439464965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32202262387653883252619953 24151696790740412439464965)
          ·
            refine ⟨4528443148263827332399681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24151696790740412439464965 4528443148263827332399681)
            ·
              refine ⟨3396332361197870499299761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4528443148263827332399681 3396332361197870499299761)
              ·
                refine ⟨2547249270898402874474821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3396332361197870499299761 2547249270898402874474821)
                ·
                  refine ⟨477609238293450538964029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2547249270898402874474821 477609238293450538964029)
                  ·
                    rfl

theorem cell22_4185633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 4].length) (baseStart_4185633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185633 prefixEnd_4185633 := by exact prefixLift 4185633
  have htrace : WordTrace (prefixWord ++ tailWord_4185633) baseStart_4185633 baseEnd_4185633 := by
    simpa [prefixWord, tailWord_4185633, baseEnd_4185633] using wordTrace_append hprefix tailTrace_4185633
  have hstable : (prefixWord ++ tailWord_4185633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185633).length < 2 ^ (prefixWord ++ tailWord_4185633).sum := by decide
  have hdescent : baseEnd_4185633 < baseStart_4185633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185661 : List Nat := [1, 4, 1, 3, 3, 1, 3, 6]
def baseStart_4185661 : Nat := 118140960795 + 4185661 * 2 ^ 59
def prefixEnd_4185661 : Nat := 4983230072969 + 3 ^ 40 * 4185661 * 2
def baseEnd_4185661 : Nat := 159204144428063208576889

theorem tailTrace_4185661 : CollatzResearch.WordTrace tailWord_4185661 prefixEnd_4185661 159204144428063208576889 := by
  unfold tailWord_4185661
  simp only [CollatzResearch.WordTrace]
  refine ⟨152663598489072525831476837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101775732326048350554317891 152663598489072525831476837)
  ·
    refine ⟨28624424716701098593401907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152663598489072525831476837 28624424716701098593401907)
    ·
      refine ⟨42936637075051647890102861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28624424716701098593401907 42936637075051647890102861)
      ·
        refine ⟨16101238903144367958788573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42936637075051647890102861 16101238903144367958788573)
        ·
          refine ⟨6037964588679137984545715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16101238903144367958788573 6037964588679137984545715)
          ·
            refine ⟨9056946883018706976818573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6037964588679137984545715 9056946883018706976818573)
            ·
              refine ⟨3396355081132015116306965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9056946883018706976818573 3396355081132015116306965)
              ·
                refine ⟨159204144428063208576889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3396355081132015116306965 159204144428063208576889)
                ·
                  rfl

theorem cell22_4185661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 6].length) (baseStart_4185661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185661 prefixEnd_4185661 := by exact prefixLift 4185661
  have htrace : WordTrace (prefixWord ++ tailWord_4185661) baseStart_4185661 baseEnd_4185661 := by
    simpa [prefixWord, tailWord_4185661, baseEnd_4185661] using wordTrace_append hprefix tailTrace_4185661
  have hstable : (prefixWord ++ tailWord_4185661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185661).length < 2 ^ (prefixWord ++ tailWord_4185661).sum := by decide
  have hdescent : baseEnd_4185661 < baseStart_4185661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185751 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 6]
def baseStart_4185751 : Nat := 118140960795 + 4185751 * 2 ^ 59
def prefixEnd_4185751 : Nat := 4983230072969 + 3 ^ 40 * 4185751 * 2
def baseEnd_4185751 : Nat := 477622702897279547480575

theorem tailTrace_4185751 : CollatzResearch.WordTrace tailWord_4185751 prefixEnd_4185751 477622702897279547480575 := by
  unfold tailWord_4185751
  simp only [CollatzResearch.WordTrace]
  refine ⟨152666881058746471202253107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101777920705830980801502071 152666881058746471202253107)
  ·
    refine ⟨229000321588119706803379661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152666881058746471202253107 229000321588119706803379661)
    ·
      refine ⟨85875120595544890051267373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229000321588119706803379661 85875120595544890051267373)
      ·
        refine ⟨32203170223329333769225265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85875120595544890051267373 32203170223329333769225265)
        ·
          refine ⟨24152377667497000326918949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32203170223329333769225265 24152377667497000326918949)
          ·
            refine ⟨4528570812655687561297303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24152377667497000326918949 4528570812655687561297303)
            ·
              refine ⟨6792856218983531341945955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4528570812655687561297303 6792856218983531341945955)
              ·
                refine ⟨10189284328475297012918933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792856218983531341945955 10189284328475297012918933)
                ·
                  refine ⟨477622702897279547480575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10189284328475297012918933 477622702897279547480575)
                  ·
                    rfl

theorem cell22_4185751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 6].length) (baseStart_4185751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185751 prefixEnd_4185751 := by exact prefixLift 4185751
  have htrace : WordTrace (prefixWord ++ tailWord_4185751) baseStart_4185751 baseEnd_4185751 := by
    simpa [prefixWord, tailWord_4185751, baseEnd_4185751] using wordTrace_append hprefix tailTrace_4185751
  have hstable : (prefixWord ++ tailWord_4185751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185751).length < 2 ^ (prefixWord ++ tailWord_4185751).sum := by decide
  have hdescent : baseEnd_4185751 < baseStart_4185751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185802 : List Nat := [3, 1, 2, 1, 6, 1, 2, 2, 4]
def baseStart_4185802 : Nat := 118140960795 + 4185802 * 2 ^ 59
def prefixEnd_4185802 : Nat := 4983230072969 + 3 ^ 40 * 4185802 * 2
def baseEnd_4185802 : Nat := 477628522344697169805523

theorem tailTrace_4185802 : CollatzResearch.WordTrace tailWord_4185802 prefixEnd_4185802 477628522344697169805523 := by
  unfold tailWord_4185802
  simp only [CollatzResearch.WordTrace]
  refine ⟨38167185295390426728089915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101779160787707804608239773 38167185295390426728089915)
  ·
    refine ⟨57250777943085640092134873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38167185295390426728089915 57250777943085640092134873)
    ·
      refine ⟨42938083457314230069101155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57250777943085640092134873 42938083457314230069101155)
      ·
        refine ⟨64407125185971345103651733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42938083457314230069101155 64407125185971345103651733)
        ·
          refine ⟨3019083993092406801733675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64407125185971345103651733 3019083993092406801733675)
          ·
            refine ⟨4528625989638610202600513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019083993092406801733675 4528625989638610202600513)
            ·
              refine ⟨3396469492228957651950385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4528625989638610202600513 3396469492228957651950385)
              ·
                refine ⟨2547352119171718238962789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3396469492228957651950385 2547352119171718238962789)
                ·
                  refine ⟨477628522344697169805523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2547352119171718238962789 477628522344697169805523)
                  ·
                    rfl

theorem cell22_4185802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_4185802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185802 prefixEnd_4185802 := by exact prefixLift 4185802
  have htrace : WordTrace (prefixWord ++ tailWord_4185802) baseStart_4185802 baseEnd_4185802 := by
    simpa [prefixWord, tailWord_4185802, baseEnd_4185802] using wordTrace_append hprefix tailTrace_4185802
  have hstable : (prefixWord ++ tailWord_4185802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185802).length < 2 ^ (prefixWord ++ tailWord_4185802).sum := by decide
  have hdescent : baseEnd_4185802 < baseStart_4185802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185809 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 2, 6]
def baseStart_4185809 : Nat := 118140960795 + 4185809 * 2 ^ 59
def prefixEnd_4185809 : Nat := 4983230072969 + 3 ^ 40 * 4185809 * 2
def baseEnd_4185809 : Nat := 1432887963277145824491547

theorem tailTrace_4185809 : CollatzResearch.WordTrace tailWord_4185809 prefixEnd_4185809 1432887963277145824491547 := by
  unfold tailWord_4185809
  simp only [CollatzResearch.WordTrace]
  refine ⟨152668996492536347107864481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101779330995024231405242987 152668996492536347107864481)
  ·
    refine ⟨114501747369402260330898361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152668996492536347107864481 114501747369402260330898361)
    ·
      refine ⟨85876310527051695248173771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114501747369402260330898361 85876310527051695248173771)
      ·
        refine ⟨128814465790577542872260657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85876310527051695248173771 128814465790577542872260657)
        ·
          refine ⟨96610849342933157154195493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128814465790577542872260657 96610849342933157154195493)
          ·
            refine ⟨18114534251799966966411655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96610849342933157154195493 18114534251799966966411655)
            ·
              refine ⟨27171801377699950449617483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18114534251799966966411655 27171801377699950449617483)
              ·
                refine ⟨40757702066549925674426225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27171801377699950449617483 40757702066549925674426225)
                ·
                  refine ⟨30568276549912444255819669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40757702066549925674426225 30568276549912444255819669)
                  ·
                    refine ⟨1432887963277145824491547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30568276549912444255819669 1432887963277145824491547)
                    ·
                      rfl

theorem cell22_4185809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_4185809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185809 prefixEnd_4185809 := by exact prefixLift 4185809
  have htrace : WordTrace (prefixWord ++ tailWord_4185809) baseStart_4185809 baseEnd_4185809 := by
    simpa [prefixWord, tailWord_4185809, baseEnd_4185809] using wordTrace_append hprefix tailTrace_4185809
  have hstable : (prefixWord ++ tailWord_4185809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185809).length < 2 ^ (prefixWord ++ tailWord_4185809).sum := by decide
  have hdescent : baseEnd_4185809 < baseStart_4185809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185839 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 1, 7]
def baseStart_4185839 : Nat := 118140960795 + 4185839 * 2 ^ 59
def prefixEnd_4185839 : Nat := 4983230072969 + 3 ^ 40 * 4185839 * 2
def baseEnd_4185839 : Nat := 1432898232890235746241455

theorem tailTrace_4185839 : CollatzResearch.WordTrace tailWord_4185839 prefixEnd_4185839 1432898232890235746241455 := by
  unfold tailWord_4185839
  simp only [CollatzResearch.WordTrace]
  refine ⟨152670090682427662231456571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101780060454951774820971047 152670090682427662231456571)
  ·
    refine ⟨229005136023641493347184857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152670090682427662231456571 229005136023641493347184857)
    ·
      refine ⟨171753852017731120010388643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229005136023641493347184857 171753852017731120010388643)
      ·
        refine ⟨257630778026596680015582965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171753852017731120010388643 257630778026596680015582965)
        ·
          refine ⟨24152885439993438751460903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257630778026596680015582965 24152885439993438751460903)
          ·
            refine ⟨36229328159990158127191355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24152885439993438751460903 36229328159990158127191355)
            ·
              refine ⟨54343992239985237190787033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36229328159990158127191355 54343992239985237190787033)
              ·
                refine ⟨40757994179988927893090275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54343992239985237190787033 40757994179988927893090275)
                ·
                  refine ⟨61136991269983391839635413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40757994179988927893090275 61136991269983391839635413)
                  ·
                    refine ⟨1432898232890235746241455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61136991269983391839635413 1432898232890235746241455)
                    ·
                      rfl

theorem cell22_4185839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_4185839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185839 prefixEnd_4185839 := by exact prefixLift 4185839
  have htrace : WordTrace (prefixWord ++ tailWord_4185839) baseStart_4185839 baseEnd_4185839 := by
    simpa [prefixWord, tailWord_4185839, baseEnd_4185839] using wordTrace_append hprefix tailTrace_4185839
  have hstable : (prefixWord ++ tailWord_4185839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185839).length < 2 ^ (prefixWord ++ tailWord_4185839).sum := by decide
  have hdescent : baseEnd_4185839 < baseStart_4185839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185888 : List Nat := [2, 1, 1, 5, 1, 1, 4, 2, 1, 4]
def baseStart_4185888 : Nat := 118140960795 + 4185888 * 2 ^ 59
def prefixEnd_4185888 : Nat := 4983230072969 + 3 ^ 40 * 4185888 * 2
def baseEnd_4185888 : Nat := 1432915006591615951766305

theorem tailTrace_4185888 : CollatzResearch.WordTrace tailWord_4185888 prefixEnd_4185888 1432915006591615951766305 := by
  unfold tailWord_4185888
  simp only [CollatzResearch.WordTrace]
  refine ⟨76335938929625071799995159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101781251906166762399993545 76335938929625071799995159)
  ·
    refine ⟨114503908394437607699992739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76335938929625071799995159 114503908394437607699992739)
    ·
      refine ⟨171755862591656411549989109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114503908394437607699992739 171755862591656411549989109)
      ·
        refine ⟨16102112117967788582811479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171755862591656411549989109 16102112117967788582811479)
        ·
          refine ⟨24153168176951682874217219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16102112117967788582811479 24153168176951682874217219)
          ·
            refine ⟨36229752265427524311325829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24153168176951682874217219 36229752265427524311325829)
            ·
              refine ⟨6793078549767660808373593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36229752265427524311325829 6793078549767660808373593)
              ·
                refine ⟨5094808912325745606280195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6793078549767660808373593 5094808912325745606280195)
                ·
                  refine ⟨7642213368488618409420293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5094808912325745606280195 7642213368488618409420293)
                  ·
                    refine ⟨1432915006591615951766305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7642213368488618409420293 1432915006591615951766305)
                    ·
                      rfl

theorem cell22_4185888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_4185888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185888 prefixEnd_4185888 := by exact prefixLift 4185888
  have htrace : WordTrace (prefixWord ++ tailWord_4185888) baseStart_4185888 baseEnd_4185888 := by
    simpa [prefixWord, tailWord_4185888, baseEnd_4185888] using wordTrace_append hprefix tailTrace_4185888
  have hstable : (prefixWord ++ tailWord_4185888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185888).length < 2 ^ (prefixWord ++ tailWord_4185888).sum := by decide
  have hdescent : baseEnd_4185888 < baseStart_4185888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185899 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 5, 6]
def baseStart_4185899 : Nat := 118140960795 + 4185899 * 2 ^ 59
def prefixEnd_4185899 : Nat := 4983230072969 + 3 ^ 40 * 4185899 * 2
def baseEnd_4185899 : Nat := 1432918772116415589741271

theorem tailTrace_4185899 : CollatzResearch.WordTrace tailWord_4185899 prefixEnd_4185899 1432918772116415589741271 := by
  unfold tailWord_4185899
  simp only [CollatzResearch.WordTrace]
  refine ⟨152672279062210292478640751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101781519374806861652427167 152672279062210292478640751)
  ·
    refine ⟨229008418593315438717961127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152672279062210292478640751 229008418593315438717961127)
    ·
      refine ⟨343512627889973158076941691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229008418593315438717961127 343512627889973158076941691)
      ·
        refine ⟨515268941834959737115412537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343512627889973158076941691 515268941834959737115412537)
        ·
          refine ⟨386451706376219802836559403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515268941834959737115412537 386451706376219802836559403)
          ·
            refine ⟨579677559564329704254839105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386451706376219802836559403 579677559564329704254839105)
            ·
              refine ⟨434758169673247278191129329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579677559564329704254839105 434758169673247278191129329)
              ·
                refine ⟨326068627254935458643346997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 434758169673247278191129329 326068627254935458643346997)
                ·
                  refine ⟨30568933805150199247813781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 326068627254935458643346997 30568933805150199247813781)
                  ·
                    refine ⟨1432918772116415589741271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30568933805150199247813781 1432918772116415589741271)
                    ·
                      rfl

theorem cell22_4185899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 6].length) (baseStart_4185899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185899 prefixEnd_4185899 := by exact prefixLift 4185899
  have htrace : WordTrace (prefixWord ++ tailWord_4185899) baseStart_4185899 baseEnd_4185899 := by
    simpa [prefixWord, tailWord_4185899, baseEnd_4185899] using wordTrace_append hprefix tailTrace_4185899
  have hstable : (prefixWord ++ tailWord_4185899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185899).length < 2 ^ (prefixWord ++ tailWord_4185899).sum := by decide
  have hdescent : baseEnd_4185899 < baseStart_4185899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4185916 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_4185916 : Nat := 118140960795 + 4185916 * 2 ^ 59
def prefixEnd_4185916 : Nat := 4983230072969 + 3 ^ 40 * 4185916 * 2
def baseEnd_4185916 : Nat := 1432924591563833212066219

theorem tailTrace_4185916 : CollatzResearch.WordTrace tailWord_4185916 prefixEnd_4185916 1432924591563833212066219 := by
  unfold tailWord_4185916
  simp only [CollatzResearch.WordTrace]
  refine ⟨76336449551574352191004801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101781932735432469588006401 76336449551574352191004801)
  ·
    refine ⟨57252337163680764143253601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76336449551574352191004801 57252337163680764143253601)
    ·
      refine ⟨42939252872760573107440201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57252337163680764143253601 42939252872760573107440201)
      ·
        refine ⟨32204439654570429830580151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42939252872760573107440201 32204439654570429830580151)
        ·
          refine ⟨48306659481855644745870227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32204439654570429830580151 48306659481855644745870227)
          ·
            refine ⟨72459989222783467118805341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48306659481855644745870227 72459989222783467118805341)
            ·
              refine ⟨27172495958543800169552003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72459989222783467118805341 27172495958543800169552003)
              ·
                refine ⟨40758743937815700254328005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27172495958543800169552003 40758743937815700254328005)
                ·
                  refine ⟨7642264488340443797686501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40758743937815700254328005 7642264488340443797686501)
                  ·
                    refine ⟨1432924591563833212066219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7642264488340443797686501 1432924591563833212066219)
                    ·
                      rfl

theorem cell22_4185916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_4185916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4185916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4185916 prefixEnd_4185916 := by exact prefixLift 4185916
  have htrace : WordTrace (prefixWord ++ tailWord_4185916) baseStart_4185916 baseEnd_4185916 := by
    simpa [prefixWord, tailWord_4185916, baseEnd_4185916] using wordTrace_append hprefix tailTrace_4185916
  have hstable : (prefixWord ++ tailWord_4185916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4185916).length < 2 ^ (prefixWord ++ tailWord_4185916).sum := by decide
  have hdescent : baseEnd_4185916 < baseStart_4185916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4185916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186068 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_4186068 : Nat := 118140960795 + 4186068 * 2 ^ 59
def prefixEnd_4186068 : Nat := 4983230072969 + 3 ^ 40 * 4186068 * 2
def baseEnd_4186068 : Nat := 1432976624270155482265753

theorem tailTrace_4186068 : CollatzResearch.WordTrace tailWord_4186068 prefixEnd_4186068 1432976624270155482265753 := by
  unfold tailWord_4186068
  simp only [CollatzResearch.WordTrace]
  refine ⟨76339221499299017170771429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101785628665732022894361905 76339221499299017170771429)
  ·
    refine ⟨14313604031118565719519643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76339221499299017170771429 14313604031118565719519643)
    ·
      refine ⟨21470406046677848579279465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14313604031118565719519643 21470406046677848579279465)
      ·
        refine ⟨16102804535008386434459599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21470406046677848579279465 16102804535008386434459599)
        ·
          refine ⟨24154206802512579651689399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16102804535008386434459599 24154206802512579651689399)
          ·
            refine ⟨36231310203768869477534099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24154206802512579651689399 36231310203768869477534099)
            ·
              refine ⟨54346965305653304216301149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36231310203768869477534099 54346965305653304216301149)
              ·
                refine ⟨20380111989619989081112931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54346965305653304216301149 20380111989619989081112931)
                ·
                  refine ⟨30570167984429983621669397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20380111989619989081112931 30570167984429983621669397)
                  ·
                    refine ⟨1432976624270155482265753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30570167984429983621669397 1432976624270155482265753)
                    ·
                      rfl

theorem cell22_4186068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_4186068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186068 prefixEnd_4186068 := by exact prefixLift 4186068
  have htrace : WordTrace (prefixWord ++ tailWord_4186068) baseStart_4186068 baseEnd_4186068 := by
    simpa [prefixWord, tailWord_4186068, baseEnd_4186068] using wordTrace_append hprefix tailTrace_4186068
  have hstable : (prefixWord ++ tailWord_4186068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186068).length < 2 ^ (prefixWord ++ tailWord_4186068).sum := by decide
  have hdescent : baseEnd_4186068 < baseStart_4186068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186083 : List Nat := [1, 1, 1, 6, 1, 4, 8]
def baseStart_4186083 : Nat := 118140960795 + 4186083 * 2 ^ 59
def prefixEnd_4186083 : Nat := 4983230072969 + 3 ^ 40 * 4186083 * 2
def baseEnd_4186083 : Nat := 53073398484322238634841

theorem tailTrace_4186083 : CollatzResearch.WordTrace tailWord_4186083 prefixEnd_4186083 53073398484322238634841 := by
  unfold tailWord_4186083
  simp only [CollatzResearch.WordTrace]
  refine ⟨152678990093543691903338903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101785993395695794602225935 152678990093543691903338903)
  ·
    refine ⟨229018485140315537855008355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152678990093543691903338903 229018485140315537855008355)
    ·
      refine ⟨343527727710473306782512533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229018485140315537855008355 343527727710473306782512533)
      ·
        refine ⟨16102862236428436255430275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 343527727710473306782512533 16102862236428436255430275)
        ·
          refine ⟨24154293354642654383145413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16102862236428436255430275 24154293354642654383145413)
          ·
            refine ⟨4528930003995497696839765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24154293354642654383145413 4528930003995497696839765)
            ·
              refine ⟨53073398484322238634841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4528930003995497696839765 53073398484322238634841)
              ·
                rfl

theorem cell22_4186083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 8].length) (baseStart_4186083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186083 prefixEnd_4186083 := by exact prefixLift 4186083
  have htrace : WordTrace (prefixWord ++ tailWord_4186083) baseStart_4186083 baseEnd_4186083 := by
    simpa [prefixWord, tailWord_4186083, baseEnd_4186083] using wordTrace_append hprefix tailTrace_4186083
  have hstable : (prefixWord ++ tailWord_4186083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186083).length < 2 ^ (prefixWord ++ tailWord_4186083).sum := by decide
  have hdescent : baseEnd_4186083 < baseStart_4186083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186143 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 2, 5]
def baseStart_4186143 : Nat := 118140960795 + 4186143 * 2 ^ 59
def prefixEnd_4186143 : Nat := 4983230072969 + 3 ^ 40 * 4186143 * 2
def baseEnd_4186143 : Nat := 1433002298302880286640523

theorem tailTrace_4186143 : CollatzResearch.WordTrace tailWord_4186143 prefixEnd_4186143 1433002298302880286640523 := by
  unfold tailWord_4186143
  simp only [CollatzResearch.WordTrace]
  refine ⟨152681178473326322150523083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101787452315550881433682055 152681178473326322150523083)
  ·
    refine ⟨229021767709989483225784625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152681178473326322150523083 229021767709989483225784625)
    ·
      refine ⟨171766325782492112419338469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229021767709989483225784625 171766325782492112419338469)
      ·
        refine ⟨32206186084217271078625963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171766325782492112419338469 32206186084217271078625963)
        ·
          refine ⟨48309279126325906617938945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32206186084217271078625963 48309279126325906617938945)
          ·
            refine ⟨36231959344744429963454209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48309279126325906617938945 36231959344744429963454209)
            ·
              refine ⟨27173969508558322472590657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36231959344744429963454209 27173969508558322472590657)
              ·
                refine ⟨20380477131418741854442993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27173969508558322472590657 20380477131418741854442993)
                ·
                  refine ⟨15285357848564056390832245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20380477131418741854442993 15285357848564056390832245)
                  ·
                    refine ⟨1433002298302880286640523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15285357848564056390832245 1433002298302880286640523)
                    ·
                      rfl

theorem cell22_4186143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_4186143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186143 prefixEnd_4186143 := by exact prefixLift 4186143
  have htrace : WordTrace (prefixWord ++ tailWord_4186143) baseStart_4186143 baseEnd_4186143 := by
    simpa [prefixWord, tailWord_4186143, baseEnd_4186143] using wordTrace_append hprefix tailTrace_4186143
  have hstable : (prefixWord ++ tailWord_4186143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186143).length < 2 ^ (prefixWord ++ tailWord_4186143).sum := by decide
  have hdescent : baseEnd_4186143 < baseStart_4186143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186149 : List Nat := [1, 3, 1, 2, 2, 3, 4, 2, 1, 3]
def baseStart_4186149 : Nat := 118140960795 + 4186149 * 2 ^ 59
def prefixEnd_4186149 : Nat := 4983230072969 + 3 ^ 40 * 4186149 * 2
def baseEnd_4186149 : Nat := 1433004352225498270990505

theorem tailTrace_4186149 : CollatzResearch.WordTrace tailWord_4186149 prefixEnd_4186149 1433004352225498270990505 := by
  unfold tailWord_4186149
  simp only [CollatzResearch.WordTrace]
  refine ⟨152681397311304585175241501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101787598207536390116827667 152681397311304585175241501)
  ·
    refine ⟨57255523991739219440715563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152681397311304585175241501 57255523991739219440715563)
    ·
      refine ⟨85883285987608829161073345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57255523991739219440715563 85883285987608829161073345)
      ·
        refine ⟨64412464490706621870805009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85883285987608829161073345 64412464490706621870805009)
        ·
          refine ⟨48309348368029966403103757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64412464490706621870805009 48309348368029966403103757)
          ·
            refine ⟨18116005638011237401163909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48309348368029966403103757 18116005638011237401163909)
            ·
              refine ⟨3396751057127107012718233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18116005638011237401163909 3396751057127107012718233)
              ·
                refine ⟨2547563292845330259538675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3396751057127107012718233 2547563292845330259538675)
                ·
                  refine ⟨3821344939267995389308013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2547563292845330259538675 3821344939267995389308013)
                  ·
                    refine ⟨1433004352225498270990505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3821344939267995389308013 1433004352225498270990505)
                    ·
                      rfl

theorem cell22_4186149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_4186149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186149 prefixEnd_4186149 := by exact prefixLift 4186149
  have htrace : WordTrace (prefixWord ++ tailWord_4186149) baseStart_4186149 baseEnd_4186149 := by
    simpa [prefixWord, tailWord_4186149, baseEnd_4186149] using wordTrace_append hprefix tailTrace_4186149
  have hstable : (prefixWord ++ tailWord_4186149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186149).length < 2 ^ (prefixWord ++ tailWord_4186149).sum := by decide
  have hdescent : baseEnd_4186149 < baseStart_4186149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186241 : List Nat := [1, 2, 4, 2, 4, 1, 1, 3, 4]
def baseStart_4186241 : Nat := 118140960795 + 4186241 * 2 ^ 59
def prefixEnd_4186241 : Nat := 4983230072969 + 3 ^ 40 * 4186241 * 2
def baseEnd_4186241 : Nat := 477678615235213565896741

theorem tailTrace_4186241 : CollatzResearch.WordTrace tailWord_4186241 prefixEnd_4186241 477678615235213565896741 := by
  unfold tailWord_4186241
  simp only [CollatzResearch.WordTrace]
  refine ⟨152684752826971284887590577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101789835217980856591727051 152684752826971284887590577)
  ·
    refine ⟨114513564620228463665692933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152684752826971284887590577 114513564620228463665692933)
    ·
      refine ⟨21471293366292836937317425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114513564620228463665692933 21471293366292836937317425)
      ·
        refine ⟨16103470024719627702988069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21471293366292836937317425 16103470024719627702988069)
        ·
          refine ⟨3019400629634930194310263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16103470024719627702988069 3019400629634930194310263)
          ·
            refine ⟨4529100944452395291465395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3019400629634930194310263 4529100944452395291465395)
            ·
              refine ⟨6793651416678592937198093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529100944452395291465395 6793651416678592937198093)
              ·
                refine ⟨2547619281254472351449285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6793651416678592937198093 2547619281254472351449285)
                ·
                  refine ⟨477678615235213565896741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2547619281254472351449285 477678615235213565896741)
                  ·
                    rfl

theorem cell22_4186241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 4].length) (baseStart_4186241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186241 prefixEnd_4186241 := by exact prefixLift 4186241
  have htrace : WordTrace (prefixWord ++ tailWord_4186241) baseStart_4186241 baseEnd_4186241 := by
    simpa [prefixWord, tailWord_4186241, baseEnd_4186241] using wordTrace_append hprefix tailTrace_4186241
  have hstable : (prefixWord ++ tailWord_4186241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186241).length < 2 ^ (prefixWord ++ tailWord_4186241).sum := by decide
  have hdescent : baseEnd_4186241 < baseStart_4186241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186318 : List Nat := [4, 1, 1, 1, 4, 3, 2, 2, 1, 3]
def baseStart_4186318 : Nat := 118140960795 + 4186318 * 2 ^ 59
def prefixEnd_4186318 : Nat := 4983230072969 + 3 ^ 40 * 4186318 * 2
def baseEnd_4186318 : Nat := 1433062204379238163514987

theorem tailTrace_4186318 : CollatzResearch.WordTrace tailWord_4186318 prefixEnd_4186318 1433062204379238163514987 := by
  unfold tailWord_4186318
  simp only [CollatzResearch.WordTrace]
  refine ⟨19085945155961540879767951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101791707498461551358762405 19085945155961540879767951)
  ·
    refine ⟨28628917733942311319651927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19085945155961540879767951 28628917733942311319651927)
    ·
      refine ⟨42943376600913466979477891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28628917733942311319651927 42943376600913466979477891)
      ·
        refine ⟨64415064901370200469216837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42943376600913466979477891 64415064901370200469216837)
        ·
          refine ⟨12077824669006912587978157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64415064901370200469216837 12077824669006912587978157)
          ·
            refine ⟨4529184250877592220491809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12077824669006912587978157 4529184250877592220491809)
            ·
              refine ⟨3396888188158194165368857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4529184250877592220491809 3396888188158194165368857)
              ·
                refine ⟨2547666141118645624026643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3396888188158194165368857 2547666141118645624026643)
                ·
                  refine ⟨3821499211677968436039965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2547666141118645624026643 3821499211677968436039965)
                  ·
                    refine ⟨1433062204379238163514987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3821499211677968436039965 1433062204379238163514987)
                    ·
                      rfl

theorem cell22_4186318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_4186318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186318 prefixEnd_4186318 := by exact prefixLift 4186318
  have htrace : WordTrace (prefixWord ++ tailWord_4186318) baseStart_4186318 baseEnd_4186318 := by
    simpa [prefixWord, tailWord_4186318, baseEnd_4186318] using wordTrace_append hprefix tailTrace_4186318
  have hstable : (prefixWord ++ tailWord_4186318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186318).length < 2 ^ (prefixWord ++ tailWord_4186318).sum := by decide
  have hdescent : baseEnd_4186318 < baseStart_4186318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186355 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 1, 6]
def baseStart_4186355 : Nat := 118140960795 + 4186355 * 2 ^ 59
def prefixEnd_4186355 : Nat := 4983230072969 + 3 ^ 40 * 4186355 * 2
def baseEnd_4186355 : Nat := 1433074870235382400339873

theorem tailTrace_4186355 : CollatzResearch.WordTrace tailWord_4186355 prefixEnd_4186355 1433074870235382400339873 := by
  unfold tailWord_4186355
  simp only [CollatzResearch.WordTrace]
  refine ⟨152688910748558282357240519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101792607165705521571493679 152688910748558282357240519)
  ·
    refine ⟨229033366122837423535860779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152688910748558282357240519 229033366122837423535860779)
    ·
      refine ⟨343550049184256135303791169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229033366122837423535860779 343550049184256135303791169)
      ·
        refine ⟨257662536888192101477843377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343550049184256135303791169 257662536888192101477843377)
        ·
          refine ⟨193246902666144076108382533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257662536888192101477843377 193246902666144076108382533)
          ·
            refine ⟨36233794249902014270321725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193246902666144076108382533 36233794249902014270321725)
            ·
              refine ⟨13587672843713255351370647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36233794249902014270321725 13587672843713255351370647)
              ·
                refine ⟨20381509265569883027055971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13587672843713255351370647 20381509265569883027055971)
                ·
                  refine ⟨30572263898354824540583957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20381509265569883027055971 30572263898354824540583957)
                  ·
                    refine ⟨1433074870235382400339873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30572263898354824540583957 1433074870235382400339873)
                    ·
                      rfl

theorem cell22_4186355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 6].length) (baseStart_4186355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186355 prefixEnd_4186355 := by exact prefixLift 4186355
  have htrace : WordTrace (prefixWord ++ tailWord_4186355) baseStart_4186355 baseEnd_4186355 := by
    simpa [prefixWord, tailWord_4186355, baseEnd_4186355] using wordTrace_append hprefix tailTrace_4186355
  have hstable : (prefixWord ++ tailWord_4186355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186355).length < 2 ^ (prefixWord ++ tailWord_4186355).sum := by decide
  have hdescent : baseEnd_4186355 < baseStart_4186355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186391 : List Nat := [1, 1, 3, 4, 1, 3, 3, 1, 2, 3]
def baseStart_4186391 : Nat := 118140960795 + 4186391 * 2 ^ 59
def prefixEnd_4186391 : Nat := 4983230072969 + 3 ^ 40 * 4186391 * 2
def baseEnd_4186391 : Nat := 1433087193771090306439763

theorem tailTrace_4186391 : CollatzResearch.WordTrace tailWord_4186391 prefixEnd_4186391 1433087193771090306439763 := by
  unfold tailWord_4186391
  simp only [CollatzResearch.WordTrace]
  refine ⟨152690223776427860505551027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101793482517618573670367351 152690223776427860505551027)
  ·
    refine ⟨229035335664641790758326541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152690223776427860505551027 229035335664641790758326541)
    ·
      refine ⟨85888250874240671534372453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229035335664641790758326541 85888250874240671534372453)
      ·
        refine ⟨16104047038920125912694835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85888250874240671534372453 16104047038920125912694835)
        ·
          refine ⟨24156070558380188869042253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16104047038920125912694835 24156070558380188869042253)
          ·
            refine ⟨9058526459392570825890845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24156070558380188869042253 9058526459392570825890845)
            ·
              refine ⟨3396947422272214059709067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9058526459392570825890845 3396947422272214059709067)
              ·
                refine ⟨5095421133408321089563601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3396947422272214059709067 5095421133408321089563601)
                ·
                  refine ⟨3821565850056240817172701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5095421133408321089563601 3821565850056240817172701)
                  ·
                    refine ⟨1433087193771090306439763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3821565850056240817172701 1433087193771090306439763)
                    ·
                      rfl

theorem cell22_4186391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_4186391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186391 prefixEnd_4186391 := by exact prefixLift 4186391
  have htrace : WordTrace (prefixWord ++ tailWord_4186391) baseStart_4186391 baseEnd_4186391 := by
    simpa [prefixWord, tailWord_4186391, baseEnd_4186391] using wordTrace_append hprefix tailTrace_4186391
  have hstable : (prefixWord ++ tailWord_4186391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186391).length < 2 ^ (prefixWord ++ tailWord_4186391).sum := by decide
  have hdescent : baseEnd_4186391 < baseStart_4186391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186404 : List Nat := [2, 3, 1, 3, 1, 4, 2, 6]
def baseStart_4186404 : Nat := 118140960795 + 4186404 * 2 ^ 59
def prefixEnd_4186404 : Nat := 4983230072969 + 3 ^ 40 * 4186404 * 2
def baseEnd_4186404 : Nat := 159232404881862511762747

theorem tailTrace_4186404 : CollatzResearch.WordTrace tailWord_4186404 prefixEnd_4186404 159232404881862511762747 := by
  unfold tailWord_4186404
  simp only [CollatzResearch.WordTrace]
  refine ⟨76345348962690381862887133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101793798616920509150516177 76345348962690381862887133)
  ·
    refine ⟨28629505861008893198582675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76345348962690381862887133 28629505861008893198582675)
    ·
      refine ⟨42944258791513339797874013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28629505861008893198582675 42944258791513339797874013)
      ·
        refine ⟨16104097046817502424202755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42944258791513339797874013 16104097046817502424202755)
        ·
          refine ⟨24156145570226253636304133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16104097046817502424202755 24156145570226253636304133)
          ·
            refine ⟨4529277294417422556807025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24156145570226253636304133 4529277294417422556807025)
            ·
              refine ⟨3396957970813066917605269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4529277294417422556807025 3396957970813066917605269)
              ·
                refine ⟨159232404881862511762747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3396957970813066917605269 159232404881862511762747)
                ·
                  rfl

theorem cell22_4186404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 6].length) (baseStart_4186404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186404 prefixEnd_4186404 := by exact prefixLift 4186404
  have htrace : WordTrace (prefixWord ++ tailWord_4186404) baseStart_4186404 baseEnd_4186404 := by
    simpa [prefixWord, tailWord_4186404, baseEnd_4186404] using wordTrace_append hprefix tailTrace_4186404
  have hstable : (prefixWord ++ tailWord_4186404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186404).length < 2 ^ (prefixWord ++ tailWord_4186404).sum := by decide
  have hdescent : baseEnd_4186404 < baseStart_4186404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186415 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 7]
def baseStart_4186415 : Nat := 118140960795 + 4186415 * 2 ^ 59
def prefixEnd_4186415 : Nat := 4983230072969 + 3 ^ 40 * 4186415 * 2
def baseEnd_4186415 : Nat := 477698469820520747946563

theorem tailTrace_4186415 : CollatzResearch.WordTrace tailWord_4186415 prefixEnd_4186415 477698469820520747946563 := by
  unfold tailWord_4186415
  simp only [CollatzResearch.WordTrace]
  refine ⟨152691099128340912604424699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101794066085560608402949799 152691099128340912604424699)
  ·
    refine ⟨229036648692511368906637049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152691099128340912604424699 229036648692511368906637049)
    ·
      refine ⟨171777486519383526679977787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229036648692511368906637049 171777486519383526679977787)
      ·
        refine ⟨257666229779075290019966681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171777486519383526679977787 257666229779075290019966681)
        ·
          refine ⟨193249672334306467514975011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257666229779075290019966681 193249672334306467514975011)
          ·
            refine ⟨289874508501459701272462517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193249672334306467514975011 289874508501459701272462517)
            ·
              refine ⟨27175735172011846994293361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 289874508501459701272462517 27175735172011846994293361)
              ·
                refine ⟨20381801379008885245720021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27175735172011846994293361 20381801379008885245720021)
                ·
                  refine ⟨477698469820520747946563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20381801379008885245720021 477698469820520747946563)
                  ·
                    rfl

theorem cell22_4186415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 7].length) (baseStart_4186415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186415 prefixEnd_4186415 := by exact prefixLift 4186415
  have htrace : WordTrace (prefixWord ++ tailWord_4186415) baseStart_4186415 baseEnd_4186415 := by
    simpa [prefixWord, tailWord_4186415, baseEnd_4186415] using wordTrace_append hprefix tailTrace_4186415
  have hstable : (prefixWord ++ tailWord_4186415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186415).length < 2 ^ (prefixWord ++ tailWord_4186415).sum := by decide
  have hdescent : baseEnd_4186415 < baseStart_4186415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186449 : List Nat := [1, 2, 2, 1, 4, 2, 4, 1, 5]
def baseStart_4186449 : Nat := 118140960795 + 4186449 * 2 ^ 59
def prefixEnd_4186449 : Nat := 4983230072969 + 3 ^ 40 * 4186449 * 2
def baseEnd_4186449 : Nat := 477702349452132496163195

theorem tailTrace_4186449 : CollatzResearch.WordTrace tailWord_4186449 prefixEnd_4186449 477702349452132496163195 := by
  unfold tailWord_4186449
  simp only [CollatzResearch.WordTrace]
  refine ⟨152692339210217736411162401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101794892806811824274108267 152692339210217736411162401)
  ·
    refine ⟨114519254407663302308371801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152692339210217736411162401 114519254407663302308371801)
    ·
      refine ⟨85889440805747476731278851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114519254407663302308371801 85889440805747476731278851)
      ·
        refine ⟨128834161208621215096918277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85889440805747476731278851 128834161208621215096918277)
        ·
          refine ⟨24156405226616477830672177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128834161208621215096918277 24156405226616477830672177)
          ·
            refine ⟨18117303919962358373004133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24156405226616477830672177 18117303919962358373004133)
            ·
              refine ⟨3396994484992942194938275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18117303919962358373004133 3396994484992942194938275)
              ·
                refine ⟨5095491727489413292407413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3396994484992942194938275 5095491727489413292407413)
                ·
                  refine ⟨477702349452132496163195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5095491727489413292407413 477702349452132496163195)
                  ·
                    rfl

theorem cell22_4186449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 5].length) (baseStart_4186449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186449 prefixEnd_4186449 := by exact prefixLift 4186449
  have htrace : WordTrace (prefixWord ++ tailWord_4186449) baseStart_4186449 baseEnd_4186449 := by
    simpa [prefixWord, tailWord_4186449, baseEnd_4186449] using wordTrace_append hprefix tailTrace_4186449
  have hstable : (prefixWord ++ tailWord_4186449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186449).length < 2 ^ (prefixWord ++ tailWord_4186449).sum := by decide
  have hdescent : baseEnd_4186449 < baseStart_4186449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186526 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_4186526 : Nat := 118140960795 + 4186526 * 2 ^ 59
def prefixEnd_4186526 : Nat := 4983230072969 + 3 ^ 40 * 4186526 * 2
def baseEnd_4186526 : Nat := 1433133407029994954314349

theorem tailTrace_4186526 : CollatzResearch.WordTrace tailWord_4186526 prefixEnd_4186526 1433133407029994954314349 := by
  unfold tailWord_4186526
  simp only [CollatzResearch.WordTrace]
  refine ⟨19086893453867347320214429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101796765087292519041143621 19086893453867347320214429)
  ·
    refine ⟨7157585045200255245080411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19086893453867347320214429 7157585045200255245080411)
    ·
      refine ⟨10736377567800382867620617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7157585045200255245080411 10736377567800382867620617)
      ·
        refine ⟨8052283175850287150715463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10736377567800382867620617 8052283175850287150715463)
        ·
          refine ⟨12078424763775430726073195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8052283175850287150715463 12078424763775430726073195)
          ·
            refine ⟨18117637145663146089109793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12078424763775430726073195 18117637145663146089109793)
            ·
              refine ⟨13588227859247359566832345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18117637145663146089109793 13588227859247359566832345)
              ·
                refine ⟨10191170894435519675124259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13588227859247359566832345 10191170894435519675124259)
                ·
                  refine ⟨15286756341653279512686389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10191170894435519675124259 15286756341653279512686389)
                  ·
                    refine ⟨1433133407029994954314349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15286756341653279512686389 1433133407029994954314349)
                    ·
                      rfl

theorem cell22_4186526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_4186526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186526 prefixEnd_4186526 := by exact prefixLift 4186526
  have htrace : WordTrace (prefixWord ++ tailWord_4186526) baseStart_4186526 baseEnd_4186526 := by
    simpa [prefixWord, tailWord_4186526, baseEnd_4186526] using wordTrace_append hprefix tailTrace_4186526
  have hstable : (prefixWord ++ tailWord_4186526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186526).length < 2 ^ (prefixWord ++ tailWord_4186526).sum := by decide
  have hdescent : baseEnd_4186526 < baseStart_4186526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186631 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 3, 4]
def baseStart_4186631 : Nat := 118140960795 + 4186631 * 2 ^ 59
def prefixEnd_4186631 : Nat := 4983230072969 + 3 ^ 40 * 4186631 * 2
def baseEnd_4186631 : Nat := 1433169350675809680439027

theorem tailTrace_4186631 : CollatzResearch.WordTrace tailWord_4186631 prefixEnd_4186631 1433169350675809680439027 := by
  unfold tailWord_4186631
  simp only [CollatzResearch.WordTrace]
  refine ⟨152698977295558381494287747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101799318197038920996191831 152698977295558381494287747)
  ·
    refine ⟨229048465943337572241431621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152698977295558381494287747 229048465943337572241431621)
    ·
      refine ⟨42946587364375794795268429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229048465943337572241431621 42946587364375794795268429)
      ·
        refine ⟨16104970261640923048225661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42946587364375794795268429 16104970261640923048225661)
        ·
          refine ⟨6039363848115346143084623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16104970261640923048225661 6039363848115346143084623)
          ·
            refine ⟨9059045772173019214626935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6039363848115346143084623 9059045772173019214626935)
            ·
              refine ⟨13588568658259528821940403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9059045772173019214626935 13588568658259528821940403)
              ·
                refine ⟨20382852987389293232910605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13588568658259528821940403 20382852987389293232910605)
                ·
                  refine ⟨7643569870270984962341477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20382852987389293232910605 7643569870270984962341477)
                  ·
                    refine ⟨1433169350675809680439027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7643569870270984962341477 1433169350675809680439027)
                    ·
                      rfl

theorem cell22_4186631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_4186631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186631 prefixEnd_4186631 := by exact prefixLift 4186631
  have htrace : WordTrace (prefixWord ++ tailWord_4186631) baseStart_4186631 baseEnd_4186631 := by
    simpa [prefixWord, tailWord_4186631, baseEnd_4186631] using wordTrace_append hprefix tailTrace_4186631
  have hstable : (prefixWord ++ tailWord_4186631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186631).length < 2 ^ (prefixWord ++ tailWord_4186631).sum := by decide
  have hdescent : baseEnd_4186631 < baseStart_4186631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186648 : List Nat := [2, 1, 2, 3, 3, 2, 3, 1, 1, 4]
def baseStart_4186648 : Nat := 118140960795 + 4186648 * 2 ^ 59
def prefixEnd_4186648 : Nat := 4983230072969 + 3 ^ 40 * 4186648 * 2
def baseEnd_4186648 : Nat := 1433175170123227302763975

theorem tailTrace_4186648 : CollatzResearch.WordTrace tailWord_4186648 prefixEnd_4186648 1433175170123227302763975 := by
  unfold tailWord_4186648
  simp only [CollatzResearch.WordTrace]
  refine ⟨76349798668248396698828299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101799731557664528931771065 76349798668248396698828299)
  ·
    refine ⟨114524698002372595048242449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76349798668248396698828299 114524698002372595048242449)
    ·
      refine ⟨85893523501779446286181837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114524698002372595048242449 85893523501779446286181837)
      ·
        refine ⟨32210071313167292357318189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85893523501779446286181837 32210071313167292357318189)
        ·
          refine ⟨12078776742437734633994321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32210071313167292357318189 12078776742437734633994321)
          ·
            refine ⟨9059082556828300975495741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12078776742437734633994321 9059082556828300975495741)
            ·
              refine ⟨3397155958810612865810903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9059082556828300975495741 3397155958810612865810903)
              ·
                refine ⟨5095733938215919298716355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3397155958810612865810903 5095733938215919298716355)
                ·
                  refine ⟨7643600907323878948074533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5095733938215919298716355 7643600907323878948074533)
                  ·
                    refine ⟨1433175170123227302763975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7643600907323878948074533 1433175170123227302763975)
                    ·
                      rfl

theorem cell22_4186648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_4186648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186648 prefixEnd_4186648 := by exact prefixLift 4186648
  have htrace : WordTrace (prefixWord ++ tailWord_4186648) baseStart_4186648 baseEnd_4186648 := by
    simpa [prefixWord, tailWord_4186648, baseEnd_4186648] using wordTrace_append hprefix tailTrace_4186648
  have hstable : (prefixWord ++ tailWord_4186648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186648).length < 2 ^ (prefixWord ++ tailWord_4186648).sum := by decide
  have hdescent : baseEnd_4186648 < baseStart_4186648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186661 : List Nat := [1, 3, 1, 2, 2, 1, 3, 4, 2, 3]
def baseStart_4186661 : Nat := 118140960795 + 4186661 * 2 ^ 59
def prefixEnd_4186661 : Nat := 4983230072969 + 3 ^ 40 * 4186661 * 2
def baseEnd_4186661 : Nat := 1433179620288899602188935

theorem tailTrace_4186661 : CollatzResearch.WordTrace tailWord_4186661 prefixEnd_4186661 1433179620288899602188935 := by
  unfold tailWord_4186661
  simp only [CollatzResearch.WordTrace]
  refine ⟨152700071485449696617879837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101800047656966464411919891 152700071485449696617879837)
  ·
    refine ⟨57262526807043636231704939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152700071485449696617879837 57262526807043636231704939)
    ·
      refine ⟨85893790210565454347557409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57262526807043636231704939 85893790210565454347557409)
      ·
        refine ⟨64420342657924090760668057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85893790210565454347557409 64420342657924090760668057)
        ·
          refine ⟨48315256993443068070501043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64420342657924090760668057 48315256993443068070501043)
          ·
            refine ⟨72472885490164602105751565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48315256993443068070501043 72472885490164602105751565)
            ·
              refine ⟨27177332058811725789656837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72472885490164602105751565 27177332058811725789656837)
              ·
                refine ⟨5095749761027198585560657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27177332058811725789656837 5095749761027198585560657)
                ·
                  refine ⟨3821812320770398939170493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5095749761027198585560657 3821812320770398939170493)
                  ·
                    refine ⟨1433179620288899602188935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3821812320770398939170493 1433179620288899602188935)
                    ·
                      rfl

theorem cell22_4186661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_4186661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186661 prefixEnd_4186661 := by exact prefixLift 4186661
  have htrace : WordTrace (prefixWord ++ tailWord_4186661) baseStart_4186661 baseEnd_4186661 := by
    simpa [prefixWord, tailWord_4186661, baseEnd_4186661] using wordTrace_append hprefix tailTrace_4186661
  have hstable : (prefixWord ++ tailWord_4186661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186661).length < 2 ^ (prefixWord ++ tailWord_4186661).sum := by decide
  have hdescent : baseEnd_4186661 < baseStart_4186661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186674 : List Nat := [3, 2, 1, 1, 2, 1, 5, 7]
def baseStart_4186674 : Nat := 118140960795 + 4186674 * 2 ^ 59
def prefixEnd_4186674 : Nat := 4983230072969 + 3 ^ 40 * 4186674 * 2
def baseEnd_4186674 : Nat := 159242674494952433512655

theorem tailTrace_4186674 : CollatzResearch.WordTrace tailWord_4186674 prefixEnd_4186674 159242674494952433512655 := by
  unfold tailWord_4186674
  simp only [CollatzResearch.WordTrace]
  refine ⟨38175136408600649959525769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101800363756268399892068717 38175136408600649959525769)
  ·
    refine ⟨28631352306450487469644327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38175136408600649959525769 28631352306450487469644327)
    ·
      refine ⟨42947028459675731204466491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28631352306450487469644327 42947028459675731204466491)
      ·
        refine ⟨64420542689513596806699737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42947028459675731204466491 64420542689513596806699737)
        ·
          refine ⟨48315407017135197605024803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64420542689513596806699737 48315407017135197605024803)
          ·
            refine ⟨72473110525702796407537205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48315407017135197605024803 72473110525702796407537205)
            ·
              refine ⟨6794354111784637163206613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72473110525702796407537205 6794354111784637163206613)
              ·
                refine ⟨159242674494952433512655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6794354111784637163206613 159242674494952433512655)
                ·
                  rfl

theorem cell22_4186674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_4186674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186674 prefixEnd_4186674 := by exact prefixLift 4186674
  have htrace : WordTrace (prefixWord ++ tailWord_4186674) baseStart_4186674 baseEnd_4186674 := by
    simpa [prefixWord, tailWord_4186674, baseEnd_4186674] using wordTrace_append hprefix tailTrace_4186674
  have hstable : (prefixWord ++ tailWord_4186674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186674).length < 2 ^ (prefixWord ++ tailWord_4186674).sum := by decide
  have hdescent : baseEnd_4186674 < baseStart_4186674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186678 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_4186678 : Nat := 118140960795 + 4186678 * 2 ^ 59
def prefixEnd_4186678 : Nat := 4983230072969 + 3 ^ 40 * 4186678 * 2
def baseEnd_4186678 : Nat := 1433185439736317224513883

theorem tailTrace_4186678 : CollatzResearch.WordTrace tailWord_4186678 prefixEnd_4186678 1433185439736317224513883 := by
  unfold tailWord_4186678
  simp only [CollatzResearch.WordTrace]
  refine ⟨9543793220399256782578043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101800461017592072347499125 9543793220399256782578043)
  ·
    refine ⟨14315689830598885173867065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9543793220399256782578043 14315689830598885173867065)
    ·
      refine ⟨10736767372949163880400299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14315689830598885173867065 10736767372949163880400299)
      ·
        refine ⟨16105151059423745820600449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10736767372949163880400299 16105151059423745820600449)
        ·
          refine ⟨12078863294567809365450337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16105151059423745820600449 12078863294567809365450337)
          ·
            refine ⟨9059147470925857024087753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12078863294567809365450337 9059147470925857024087753)
            ·
              refine ⟨6794360603194392768065815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9059147470925857024087753 6794360603194392768065815)
              ·
                refine ⟨10191540904791589152098723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6794360603194392768065815 10191540904791589152098723)
                ·
                  refine ⟨15287311357187383728148085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10191540904791589152098723 15287311357187383728148085)
                  ·
                    refine ⟨1433185439736317224513883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15287311357187383728148085 1433185439736317224513883)
                    ·
                      rfl

theorem cell22_4186678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_4186678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186678 prefixEnd_4186678 := by exact prefixLift 4186678
  have htrace : WordTrace (prefixWord ++ tailWord_4186678) baseStart_4186678 baseEnd_4186678 := by
    simpa [prefixWord, tailWord_4186678, baseEnd_4186678] using wordTrace_append hprefix tailTrace_4186678
  have hstable : (prefixWord ++ tailWord_4186678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186678).length < 2 ^ (prefixWord ++ tailWord_4186678).sum := by decide
  have hdescent : baseEnd_4186678 < baseStart_4186678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186706 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_4186706 : Nat := 118140960795 + 4186706 * 2 ^ 59
def prefixEnd_4186706 : Nat := 4983230072969 + 3 ^ 40 * 4186706 * 2
def baseEnd_4186706 : Nat := 1433195024708534484813797

theorem tailTrace_4186706 : CollatzResearch.WordTrace tailWord_4186706 prefixEnd_4186706 1433195024708534484813797 := by
  unfold tailWord_4186706
  simp only [CollatzResearch.WordTrace]
  refine ⟨38175428192571667325816993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101801141846857779535511981 38175428192571667325816993)
  ·
    refine ⟨28631571144428750494362745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38175428192571667325816993 28631571144428750494362745)
    ·
      refine ⟨21473678358321562870772059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28631571144428750494362745 21473678358321562870772059)
      ·
        refine ⟨32210517537482344306158089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21473678358321562870772059 32210517537482344306158089)
        ·
          refine ⟨24157888153111758229618567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32210517537482344306158089 24157888153111758229618567)
          ·
            refine ⟨36236832229667637344427851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24157888153111758229618567 36236832229667637344427851)
            ·
              refine ⟨54355248344501456016641777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36236832229667637344427851 54355248344501456016641777)
              ·
                refine ⟨40766436258376092012481333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54355248344501456016641777 40766436258376092012481333)
                ·
                  refine ⟨3821853399222758626170125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40766436258376092012481333 3821853399222758626170125)
                  ·
                    refine ⟨1433195024708534484813797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3821853399222758626170125 1433195024708534484813797)
                    ·
                      rfl

theorem cell22_4186706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_4186706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186706 prefixEnd_4186706 := by exact prefixLift 4186706
  have htrace : WordTrace (prefixWord ++ tailWord_4186706) baseStart_4186706 baseEnd_4186706 := by
    simpa [prefixWord, tailWord_4186706, baseEnd_4186706] using wordTrace_append hprefix tailTrace_4186706
  have hstable : (prefixWord ++ tailWord_4186706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186706).length < 2 ^ (prefixWord ++ tailWord_4186706).sum := by decide
  have hdescent : baseEnd_4186706 < baseStart_4186706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186723 : List Nat := [1, 1, 1, 5, 1, 2, 1, 6, 1, 3]
def baseStart_4186723 : Nat := 118140960795 + 4186723 * 2 ^ 59
def prefixEnd_4186723 : Nat := 4983230072969 + 3 ^ 40 * 4186723 * 2
def baseEnd_4186723 : Nat := 1433200844155952107138745

theorem tailTrace_4186723 : CollatzResearch.WordTrace tailWord_4186723 prefixEnd_4186723 1433200844155952107138745 := by
  unfold tailWord_4186723
  simp only [CollatzResearch.WordTrace]
  refine ⟨152702332811225081206636823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101801555207483387471091215 152702332811225081206636823)
  ·
    refine ⟨229053499216837621809955235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152702332811225081206636823 229053499216837621809955235)
    ·
      refine ⟨343580248825256432714932853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229053499216837621809955235 343580248825256432714932853)
      ·
        refine ⟨32210648327367790567024955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 343580248825256432714932853 32210648327367790567024955)
        ·
          refine ⟨48315972491051685850537433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32210648327367790567024955 48315972491051685850537433)
          ·
            refine ⟨36236979368288764387903075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48315972491051685850537433 36236979368288764387903075)
            ·
              refine ⟨54355469052433146581854613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36236979368288764387903075 54355469052433146581854613)
              ·
                refine ⟨2547912611832803746024435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54355469052433146581854613 2547912611832803746024435)
                ·
                  refine ⟨3821868917749205619036653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2547912611832803746024435 3821868917749205619036653)
                  ·
                    refine ⟨1433200844155952107138745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3821868917749205619036653 1433200844155952107138745)
                    ·
                      rfl

theorem cell22_4186723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 1, 3].length) (baseStart_4186723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186723 prefixEnd_4186723 := by exact prefixLift 4186723
  have htrace : WordTrace (prefixWord ++ tailWord_4186723) baseStart_4186723 baseEnd_4186723 := by
    simpa [prefixWord, tailWord_4186723, baseEnd_4186723] using wordTrace_append hprefix tailTrace_4186723
  have hstable : (prefixWord ++ tailWord_4186723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186723).length < 2 ^ (prefixWord ++ tailWord_4186723).sum := by decide
  have hdescent : baseEnd_4186723 < baseStart_4186723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186781 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 6]
def baseStart_4186781 : Nat := 118140960795 + 4186781 * 2 ^ 59
def prefixEnd_4186781 : Nat := 4983230072969 + 3 ^ 40 * 4186781 * 2
def baseEnd_4186781 : Nat := 477740232913753096396189

theorem tailTrace_4186781 : CollatzResearch.WordTrace tailWord_4186781 prefixEnd_4186781 477740232913753096396189 := by
  unfold tailWord_4186781
  simp only [CollatzResearch.WordTrace]
  refine ⟨152704448245014957112248197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101802965496676638074832131 152704448245014957112248197)
  ·
    refine ⟨28632084045940304458546537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152704448245014957112248197 28632084045940304458546537)
    ·
      refine ⟨21474063034455228343909903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28632084045940304458546537 21474063034455228343909903)
      ·
        refine ⟨32211094551682842515864855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21474063034455228343909903 32211094551682842515864855)
        ·
          refine ⟨48316641827524263773797283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32211094551682842515864855 48316641827524263773797283)
          ·
            refine ⟨72474962741286395660695925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48316641827524263773797283 72474962741286395660695925)
            ·
              refine ⟨6794527756995599593190243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72474962741286395660695925 6794527756995599593190243)
              ·
                refine ⟨10191791635493399389785365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6794527756995599593190243 10191791635493399389785365)
                ·
                  refine ⟨477740232913753096396189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10191791635493399389785365 477740232913753096396189)
                  ·
                    rfl

theorem cell22_4186781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_4186781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186781 prefixEnd_4186781 := by exact prefixLift 4186781
  have htrace : WordTrace (prefixWord ++ tailWord_4186781) baseStart_4186781 baseEnd_4186781 := by
    simpa [prefixWord, tailWord_4186781, baseEnd_4186781] using wordTrace_append hprefix tailTrace_4186781
  have hstable : (prefixWord ++ tailWord_4186781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186781).length < 2 ^ (prefixWord ++ tailWord_4186781).sum := by decide
  have hdescent : baseEnd_4186781 < baseStart_4186781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186828 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_4186828 : Nat := 118140960795 + 4186828 * 2 ^ 59
def prefixEnd_4186828 : Nat := 4983230072969 + 3 ^ 40 * 4186828 * 2
def baseEnd_4186828 : Nat := 1433236787801766833263423

theorem tailTrace_4186828 : CollatzResearch.WordTrace tailWord_4186828 prefixEnd_4186828 1433236787801766833263423 := by
  unfold tailWord_4186828
  simp only [CollatzResearch.WordTrace]
  refine ⟨76353081237922342069604569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101804108317229789426139425 76353081237922342069604569)
  ·
    refine ⟨57264810928441756552203427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76353081237922342069604569 57264810928441756552203427)
    ·
      refine ⟨85897216392662634828305141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57264810928441756552203427 85897216392662634828305141)
      ·
        refine ⟨8052864036812122015153607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85897216392662634828305141 8052864036812122015153607)
        ·
          refine ⟨12079296055218183022730411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8052864036812122015153607 12079296055218183022730411)
          ·
            refine ⟨18118944082827274534095617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12079296055218183022730411 18118944082827274534095617)
            ·
              refine ⟨13589208062120455900571713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18118944082827274534095617 13589208062120455900571713)
              ·
                refine ⟨10191906046590341925428785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13589208062120455900571713 10191906046590341925428785)
                ·
                  refine ⟨7643929534942756444071589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10191906046590341925428785 7643929534942756444071589)
                  ·
                    refine ⟨1433236787801766833263423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7643929534942756444071589 1433236787801766833263423)
                    ·
                      rfl

theorem cell22_4186828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_4186828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186828 prefixEnd_4186828 := by exact prefixLift 4186828
  have htrace : WordTrace (prefixWord ++ tailWord_4186828) baseStart_4186828 baseEnd_4186828 := by
    simpa [prefixWord, tailWord_4186828, baseEnd_4186828] using wordTrace_append hprefix tailTrace_4186828
  have hstable : (prefixWord ++ tailWord_4186828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186828).length < 2 ^ (prefixWord ++ tailWord_4186828).sum := by decide
  have hdescent : baseEnd_4186828 < baseStart_4186828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186830 : List Nat := [4, 1, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_4186830 : Nat := 118140960795 + 4186830 * 2 ^ 59
def prefixEnd_4186830 : Nat := 4983230072969 + 3 ^ 40 * 4186830 * 2
def baseEnd_4186830 : Nat := 1433237472442639494713417

theorem tailTrace_4186830 : CollatzResearch.WordTrace tailWord_4186830 prefixEnd_4186830 1433237472442639494713417 := by
  unfold tailWord_4186830
  simp only [CollatzResearch.WordTrace]
  refine ⟨19088279427729679810097743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101804156947891625653854629 19088279427729679810097743)
  ·
    refine ⟨28632419141594519715146615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19088279427729679810097743 28632419141594519715146615)
    ·
      refine ⟨42948628712391779572719923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28632419141594519715146615 42948628712391779572719923)
      ·
        refine ⟨64422943068587669359079885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42948628712391779572719923 64422943068587669359079885)
        ·
          refine ⟨24158603650720376009654957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64422943068587669359079885 24158603650720376009654957)
          ·
            refine ⟨9059476369020141003620609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24158603650720376009654957 9059476369020141003620609)
            ·
              refine ⟨6794607276765105752715457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9059476369020141003620609 6794607276765105752715457)
              ·
                refine ⟨5095955457573829314536593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6794607276765105752715457 5095955457573829314536593)
                ·
                  refine ⟨3821966593180371985902445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5095955457573829314536593 3821966593180371985902445)
                  ·
                    refine ⟨1433237472442639494713417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3821966593180371985902445 1433237472442639494713417)
                    ·
                      rfl

theorem cell22_4186830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_4186830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186830 prefixEnd_4186830 := by exact prefixLift 4186830
  have htrace : WordTrace (prefixWord ++ tailWord_4186830) baseStart_4186830 baseEnd_4186830 := by
    simpa [prefixWord, tailWord_4186830, baseEnd_4186830] using wordTrace_append hprefix tailTrace_4186830
  have hstable : (prefixWord ++ tailWord_4186830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186830).length < 2 ^ (prefixWord ++ tailWord_4186830).sum := by decide
  have hdescent : baseEnd_4186830 < baseStart_4186830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186888 : List Nat := [2, 1, 3, 2, 2, 2, 3, 2, 5]
def baseStart_4186888 : Nat := 118140960795 + 4186888 * 2 ^ 59
def prefixEnd_4186888 : Nat := 4983230072969 + 3 ^ 40 * 4186888 * 2
def baseEnd_4186888 : Nat := 477752442342648892254413

theorem tailTrace_4186888 : CollatzResearch.WordTrace tailWord_4186888 prefixEnd_4186888 477752442342648892254413 := by
  unfold tailWord_4186888
  simp only [CollatzResearch.WordTrace]
  refine ⟨76354175427813657193196659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101805567237084876257595545 76354175427813657193196659)
  ·
    refine ⟨114531263141720485789794989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76354175427813657193196659 114531263141720485789794989)
    ·
      refine ⟨42949223678145182171173121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114531263141720485789794989 42949223678145182171173121)
      ·
        refine ⟨32211917758608886628379841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42949223678145182171173121 32211917758608886628379841)
        ·
          refine ⟨24158938318956664971284881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32211917758608886628379841 24158938318956664971284881)
          ·
            refine ⟨18119203739217498728463661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24158938318956664971284881 18119203739217498728463661)
            ·
              refine ⟨6794701402206562023173873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18119203739217498728463661 6794701402206562023173873)
              ·
                refine ⟨5096026051654921517380405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6794701402206562023173873 5096026051654921517380405)
                ·
                  refine ⟨477752442342648892254413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5096026051654921517380405 477752442342648892254413)
                  ·
                    rfl

theorem cell22_4186888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 5].length) (baseStart_4186888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186888 prefixEnd_4186888 := by exact prefixLift 4186888
  have htrace : WordTrace (prefixWord ++ tailWord_4186888) baseStart_4186888 baseEnd_4186888 := by
    simpa [prefixWord, tailWord_4186888, baseEnd_4186888] using wordTrace_append hprefix tailTrace_4186888
  have hstable : (prefixWord ++ tailWord_4186888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186888).length < 2 ^ (prefixWord ++ tailWord_4186888).sum := by decide
  have hdescent : baseEnd_4186888 < baseStart_4186888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186965 : List Nat := [1, 3, 2, 2, 2, 1, 3, 3, 2, 3]
def baseStart_4186965 : Nat := 118140960795 + 4186965 * 2 ^ 59
def prefixEnd_4186965 : Nat := 4983230072969 + 3 ^ 40 * 4186965 * 2
def baseEnd_4186965 : Nat := 1433283685701544142588003

theorem tailTrace_4186965 : CollatzResearch.WordTrace tailWord_4186965 prefixEnd_4186965 1433283685701544142588003 := by
  unfold tailWord_4186965
  simp only [CollatzResearch.WordTrace]
  refine ⟨152711159276348356536946349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101807439517565571024630899 152711159276348356536946349)
  ·
    refine ⟨57266684728630633701354881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152711159276348356536946349 57266684728630633701354881)
    ·
      refine ⟨42950013546472975276016161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57266684728630633701354881 42950013546472975276016161)
      ·
        refine ⟨32212510159854731457012121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42950013546472975276016161 32212510159854731457012121)
        ·
          refine ⟨24159382619891048592759091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32212510159854731457012121 24159382619891048592759091)
          ·
            refine ⟨36239073929836572889138637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24159382619891048592759091 36239073929836572889138637)
            ·
              refine ⟨13589652723688714833426989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36239073929836572889138637 13589652723688714833426989)
              ·
                refine ⟨5096119771383268062535121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13589652723688714833426989 5096119771383268062535121)
                ·
                  refine ⟨3822089828537451046901341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5096119771383268062535121 3822089828537451046901341)
                  ·
                    refine ⟨1433283685701544142588003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3822089828537451046901341 1433283685701544142588003)
                    ·
                      rfl

theorem cell22_4186965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_4186965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186965 prefixEnd_4186965 := by exact prefixLift 4186965
  have htrace : WordTrace (prefixWord ++ tailWord_4186965) baseStart_4186965 baseEnd_4186965 := by
    simpa [prefixWord, tailWord_4186965, baseEnd_4186965] using wordTrace_append hprefix tailTrace_4186965
  have hstable : (prefixWord ++ tailWord_4186965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186965).length < 2 ^ (prefixWord ++ tailWord_4186965).sum := by decide
  have hdescent : baseEnd_4186965 < baseStart_4186965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186980 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_4186980 : Nat := 118140960795 + 4186980 * 2 ^ 59
def prefixEnd_4186980 : Nat := 4983230072969 + 3 ^ 40 * 4186980 * 2
def baseEnd_4186980 : Nat := 1433288820508089103462957

theorem tailTrace_4186980 : CollatzResearch.WordTrace tailWord_4186980 prefixEnd_4186980 1433288820508089103462957 := by
  unfold tailWord_4186980
  simp only [CollatzResearch.WordTrace]
  refine ⟨76355853185647007049371197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101807804247529342732494929 76355853185647007049371197)
  ·
    refine ⟨28633444944617627643514199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76355853185647007049371197 28633444944617627643514199)
    ·
      refine ⟨42950167416926441465271299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28633444944617627643514199 42950167416926441465271299)
      ·
        refine ⟨64425251125389662197906949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42950167416926441465271299 64425251125389662197906949)
        ·
          refine ⟨12079734586010561662107553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64425251125389662197906949 12079734586010561662107553)
          ·
            refine ⟨9059800939507921246580665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12079734586010561662107553 9059800939507921246580665)
            ·
              refine ⟨6794850704630940934935499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9059800939507921246580665 6794850704630940934935499)
              ·
                refine ⟨10192276056946411402403249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6794850704630940934935499 10192276056946411402403249)
                ·
                  refine ⟨7644207042709808551802437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10192276056946411402403249 7644207042709808551802437)
                  ·
                    refine ⟨1433288820508089103462957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7644207042709808551802437 1433288820508089103462957)
                    ·
                      rfl

theorem cell22_4186980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_4186980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186980 prefixEnd_4186980 := by exact prefixLift 4186980
  have htrace : WordTrace (prefixWord ++ tailWord_4186980) baseStart_4186980 baseEnd_4186980 := by
    simpa [prefixWord, tailWord_4186980, baseEnd_4186980] using wordTrace_append hprefix tailTrace_4186980
  have hstable : (prefixWord ++ tailWord_4186980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186980).length < 2 ^ (prefixWord ++ tailWord_4186980).sum := by decide
  have hdescent : baseEnd_4186980 < baseStart_4186980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4186991 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 4, 6]
def baseStart_4186991 : Nat := 118140960795 + 4186991 * 2 ^ 59
def prefixEnd_4186991 : Nat := 4983230072969 + 3 ^ 40 * 4186991 * 2
def baseEnd_4186991 : Nat := 1433292586032888741437923

theorem tailTrace_4186991 : CollatzResearch.WordTrace tailWord_4186991 prefixEnd_4186991 1433292586032888741437923 := by
  unfold tailWord_4186991
  simp only [CollatzResearch.WordTrace]
  refine ⟨152712107574254162977392827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101808071716169441984928551 152712107574254162977392827)
  ·
    refine ⟨229068161361381244466089241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152712107574254162977392827 229068161361381244466089241)
    ·
      refine ⟨171801121021035933349566931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229068161361381244466089241 171801121021035933349566931)
      ·
        refine ⟨257701681531553900024350397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171801121021035933349566931 257701681531553900024350397)
        ·
          refine ⟨96638130574332712509131399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257701681531553900024350397 96638130574332712509131399)
          ·
            refine ⟨144957195861499068763697099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96638130574332712509131399 144957195861499068763697099)
            ·
              refine ⟨217435793792248603145545649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144957195861499068763697099 217435793792248603145545649)
              ·
                refine ⟨163076845344186452359159237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217435793792248603145545649 163076845344186452359159237)
                ·
                  refine ⟨30576908502034959817342357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163076845344186452359159237 30576908502034959817342357)
                  ·
                    refine ⟨1433292586032888741437923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30576908502034959817342357 1433292586032888741437923)
                    ·
                      rfl

theorem cell22_4186991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_4186991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4186991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4186991 prefixEnd_4186991 := by exact prefixLift 4186991
  have htrace : WordTrace (prefixWord ++ tailWord_4186991) baseStart_4186991 baseEnd_4186991 := by
    simpa [prefixWord, tailWord_4186991, baseEnd_4186991] using wordTrace_append hprefix tailTrace_4186991
  have hstable : (prefixWord ++ tailWord_4186991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4186991).length < 2 ^ (prefixWord ++ tailWord_4186991).sum := by decide
  have hdescent : baseEnd_4186991 < baseStart_4186991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4186991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187057 : List Nat := [1, 2, 2, 4, 3, 2, 1, 2, 5]
def baseStart_4187057 : Nat := 118140960795 + 4187057 * 2 ^ 59
def prefixEnd_4187057 : Nat := 4983230072969 + 3 ^ 40 * 4187057 * 2
def baseEnd_4187057 : Nat := 477771726393895523095907

theorem tailTrace_4187057 : CollatzResearch.WordTrace tailWord_4187057 prefixEnd_4187057 477771726393895523095907 := by
  unfold tailWord_4187057
  simp only [CollatzResearch.WordTrace]
  refine ⟨152714514792015056249295425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101809676528010037499530283 152714514792015056249295425)
  ·
    refine ⟨114535886094011292186971569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152714514792015056249295425 114535886094011292186971569)
    ·
      refine ⟨85901914570508469140228677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114535886094011292186971569 85901914570508469140228677)
      ·
        refine ⟨16106608981970337963792877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85901914570508469140228677 16106608981970337963792877)
        ·
          refine ⟨6039978368238876736422329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16106608981970337963792877 6039978368238876736422329)
          ·
            refine ⟨4529983776179157552316747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6039978368238876736422329 4529983776179157552316747)
            ·
              refine ⟨6794975664268736328475121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4529983776179157552316747 6794975664268736328475121)
              ·
                refine ⟨5096231748201552246356341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6794975664268736328475121 5096231748201552246356341)
                ·
                  refine ⟨477771726393895523095907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5096231748201552246356341 477771726393895523095907)
                  ·
                    rfl

theorem cell22_4187057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 5].length) (baseStart_4187057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187057 prefixEnd_4187057 := by exact prefixLift 4187057
  have htrace : WordTrace (prefixWord ++ tailWord_4187057) baseStart_4187057 baseEnd_4187057 := by
    simpa [prefixWord, tailWord_4187057, baseEnd_4187057] using wordTrace_append hprefix tailTrace_4187057
  have hstable : (prefixWord ++ tailWord_4187057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187057).length < 2 ^ (prefixWord ++ tailWord_4187057).sum := by decide
  have hdescent : baseEnd_4187057 < baseStart_4187057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187138 : List Nat := [3, 4, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_4187138 : Nat := 118140960795 + 4187138 * 2 ^ 59
def prefixEnd_4187138 : Nat := 4983230072969 + 3 ^ 40 * 4187138 * 2
def baseEnd_4187138 : Nat := 1433342907137029358012473

theorem tailTrace_4187138 : CollatzResearch.WordTrace tailWord_4187138 prefixEnd_4187138 1433342907137029358012473 := by
  unfold tailWord_4187138
  simp only [CollatzResearch.WordTrace]
  refine ⟨38179367276180401770748517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101811646069814404721996045 38179367276180401770748517)
  ·
    refine ⟨7158631364283825332015347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38179367276180401770748517 7158631364283825332015347)
    ·
      refine ⟨10737947046425737998023021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7158631364283825332015347 10737947046425737998023021)
      ·
        refine ⟨4026730142409651749258633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10737947046425737998023021 4026730142409651749258633)
        ·
          refine ⟨3020047606807238811943975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4026730142409651749258633 3020047606807238811943975)
          ·
            refine ⟨4530071410210858217915963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3020047606807238811943975 4530071410210858217915963)
            ·
              refine ⟨6795107115316287326873945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4530071410210858217915963 6795107115316287326873945)
              ·
                refine ⟨5096330336487215495155459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6795107115316287326873945 5096330336487215495155459)
                ·
                  refine ⟨7644495504730823242733189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5096330336487215495155459 7644495504730823242733189)
                  ·
                    refine ⟨1433342907137029358012473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7644495504730823242733189 1433342907137029358012473)
                    ·
                      rfl

theorem cell22_4187138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_4187138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187138 prefixEnd_4187138 := by exact prefixLift 4187138
  have htrace : WordTrace (prefixWord ++ tailWord_4187138) baseStart_4187138 baseEnd_4187138 := by
    simpa [prefixWord, tailWord_4187138, baseEnd_4187138] using wordTrace_append hprefix tailTrace_4187138
  have hstable : (prefixWord ++ tailWord_4187138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187138).length < 2 ^ (prefixWord ++ tailWord_4187138).sum := by decide
  have hdescent : baseEnd_4187138 < baseStart_4187138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187145 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 3, 3]
def baseStart_4187145 : Nat := 118140960795 + 4187145 * 2 ^ 59
def prefixEnd_4187145 : Nat := 4983230072969 + 3 ^ 40 * 4187145 * 2
def baseEnd_4187145 : Nat := 1433345303380083673087451

theorem tailTrace_4187145 : CollatzResearch.WordTrace tailWord_4187145 prefixEnd_4187145 1433345303380083673087451 := by
  unfold tailWord_4187145
  simp only [CollatzResearch.WordTrace]
  refine ⟨152717724415696247278498889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101811816277130831518999259 152717724415696247278498889)
  ·
    refine ⟨114538293311772185458874167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152717724415696247278498889 114538293311772185458874167)
    ·
      refine ⟨171807439967658278188311251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114538293311772185458874167 171807439967658278188311251)
      ·
        refine ⟨257711159951487417282466877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171807439967658278188311251 257711159951487417282466877)
        ·
          refine ⟨96641684981807781480925079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257711159951487417282466877 96641684981807781480925079)
          ·
            refine ⟨144962527472711672221387619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96641684981807781480925079 144962527472711672221387619)
            ·
              refine ⟨217443791209067508332081429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144962527472711672221387619 217443791209067508332081429)
              ·
                refine ⟨10192677712925039453066317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 217443791209067508332081429 10192677712925039453066317)
                ·
                  refine ⟨3822254142346889794899869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10192677712925039453066317 3822254142346889794899869)
                  ·
                    refine ⟨1433345303380083673087451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3822254142346889794899869 1433345303380083673087451)
                    ·
                      rfl

theorem cell22_4187145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 3].length) (baseStart_4187145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187145 prefixEnd_4187145 := by exact prefixLift 4187145
  have htrace : WordTrace (prefixWord ++ tailWord_4187145) baseStart_4187145 baseEnd_4187145 := by
    simpa [prefixWord, tailWord_4187145, baseEnd_4187145] using wordTrace_append hprefix tailTrace_4187145
  have hstable : (prefixWord ++ tailWord_4187145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187145).length < 2 ^ (prefixWord ++ tailWord_4187145).sum := by decide
  have hdescent : baseEnd_4187145 < baseStart_4187145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187205 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_4187205 : Nat := 118140960795 + 4187205 * 2 ^ 59
def prefixEnd_4187205 : Nat := 4983230072969 + 3 ^ 40 * 4187205 * 2
def baseEnd_4187205 : Nat := 1433365842606263516587267

theorem tailTrace_4187205 : CollatzResearch.WordTrace tailWord_4187205 prefixEnd_4187205 1433365842606263516587267 := by
  unfold tailWord_4187205
  simp only [CollatzResearch.WordTrace]
  refine ⟨152719912795478877525683069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101813275196985918350455379 152719912795478877525683069)
  ·
    refine ⟨57269967298304579072131151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152719912795478877525683069 57269967298304579072131151)
    ·
      refine ⟨85904950947456868608196727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57269967298304579072131151 85904950947456868608196727)
      ·
        refine ⟨128857426421185302912295091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85904950947456868608196727 128857426421185302912295091)
        ·
          refine ⟨193286139631777954368442637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128857426421185302912295091 193286139631777954368442637)
          ·
            refine ⟨72482302361916732888165989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193286139631777954368442637 72482302361916732888165989)
            ·
              refine ⟨13590431692859387416531123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72482302361916732888165989 13590431692859387416531123)
              ·
                refine ⟨20385647539289081124796685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13590431692859387416531123 20385647539289081124796685)
                ·
                  refine ⟨7644617827233405421798757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20385647539289081124796685 7644617827233405421798757)
                  ·
                    refine ⟨1433365842606263516587267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7644617827233405421798757 1433365842606263516587267)
                    ·
                      rfl

theorem cell22_4187205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_4187205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187205 prefixEnd_4187205 := by exact prefixLift 4187205
  have htrace : WordTrace (prefixWord ++ tailWord_4187205) baseStart_4187205 baseEnd_4187205 := by
    simpa [prefixWord, tailWord_4187205, baseEnd_4187205] using wordTrace_append hprefix tailTrace_4187205
  have hstable : (prefixWord ++ tailWord_4187205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187205).length < 2 ^ (prefixWord ++ tailWord_4187205).sum := by decide
  have hdescent : baseEnd_4187205 < baseStart_4187205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187237 : List Nat := [1, 3, 1, 3, 2, 1, 1, 6, 4]
def baseStart_4187237 : Nat := 118140960795 + 4187237 * 2 ^ 59
def prefixEnd_4187237 : Nat := 4983230072969 + 3 ^ 40 * 4187237 * 2
def baseEnd_4187237 : Nat := 477792265620075366595723

theorem tailTrace_4187237 : CollatzResearch.WordTrace tailWord_4187237 prefixEnd_4187237 477792265620075366595723 := by
  unfold tailWord_4187237
  simp only [CollatzResearch.WordTrace]
  refine ⟨152721079931362946990847965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101814053287575297993898643 152721079931362946990847965)
  ·
    refine ⟨57270404974261105121567987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152721079931362946990847965 57270404974261105121567987)
    ·
      refine ⟨85905607461391657682351981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57270404974261105121567987 85905607461391657682351981)
      ·
        refine ⟨32214602798021871630881993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85905607461391657682351981 32214602798021871630881993)
        ·
          refine ⟨24160952098516403723161495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32214602798021871630881993 24160952098516403723161495)
          ·
            refine ⟨36241428147774605584742243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24160952098516403723161495 36241428147774605584742243)
            ·
              refine ⟨54362142221661908377113365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36241428147774605584742243 54362142221661908377113365)
              ·
                refine ⟨2548225416640401955177189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54362142221661908377113365 2548225416640401955177189)
                ·
                  refine ⟨477792265620075366595723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2548225416640401955177189 477792265620075366595723)
                  ·
                    rfl

theorem cell22_4187237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_4187237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187237 prefixEnd_4187237 := by exact prefixLift 4187237
  have htrace : WordTrace (prefixWord ++ tailWord_4187237) baseStart_4187237 baseEnd_4187237 := by
    simpa [prefixWord, tailWord_4187237, baseEnd_4187237] using wordTrace_append hprefix tailTrace_4187237
  have hstable : (prefixWord ++ tailWord_4187237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187237).length < 2 ^ (prefixWord ++ tailWord_4187237).sum := by decide
  have hdescent : baseEnd_4187237 < baseStart_4187237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187250 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_4187250 : Nat := 118140960795 + 4187250 * 2 ^ 59
def prefixEnd_4187250 : Nat := 4983230072969 + 3 ^ 40 * 4187250 * 2
def baseEnd_4187250 : Nat := 1433381247025898399212129

theorem tailTrace_4187250 : CollatzResearch.WordTrace tailWord_4187250 prefixEnd_4187250 1433381247025898399212129 := by
  unfold tailWord_4187250
  simp only [CollatzResearch.WordTrace]
  refine ⟨38180388520078962552767801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101814369386877233474047469 38180388520078962552767801)
  ·
    refine ⟨28635291390059221914575851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38180388520078962552767801 28635291390059221914575851)
    ·
      refine ⟨42952937085088832871863777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28635291390059221914575851 42952937085088832871863777)
      ·
        refine ⟨32214702813816624653897833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42952937085088832871863777 32214702813816624653897833)
        ·
          refine ⟨24161027110362468490423375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32214702813816624653897833 24161027110362468490423375)
          ·
            refine ⟨36241540665543702735635063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24161027110362468490423375 36241540665543702735635063)
            ·
              refine ⟨54362310998315554103452595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36241540665543702735635063 54362310998315554103452595)
              ·
                refine ⟨81543466497473331155178893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54362310998315554103452595 81543466497473331155178893)
                ·
                  refine ⟨30578799936552499183192085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81543466497473331155178893 30578799936552499183192085)
                  ·
                    refine ⟨1433381247025898399212129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30578799936552499183192085 1433381247025898399212129)
                    ·
                      rfl

theorem cell22_4187250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_4187250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187250 prefixEnd_4187250 := by exact prefixLift 4187250
  have htrace : WordTrace (prefixWord ++ tailWord_4187250) baseStart_4187250 baseEnd_4187250 := by
    simpa [prefixWord, tailWord_4187250, baseEnd_4187250] using wordTrace_append hprefix tailTrace_4187250
  have hstable : (prefixWord ++ tailWord_4187250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187250).length < 2 ^ (prefixWord ++ tailWord_4187250).sum := by decide
  have hdescent : baseEnd_4187250 < baseStart_4187250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187282 : List Nat := [3, 2, 3, 1, 1, 4, 8]
def baseStart_4187282 : Nat := 118140960795 + 4187282 * 2 ^ 59
def prefixEnd_4187282 : Nat := 4983230072969 + 3 ^ 40 * 4187282 * 2
def baseEnd_4187282 : Nat := 53088600047402258607853

theorem tailTrace_4187282 : CollatzResearch.WordTrace tailWord_4187282 prefixEnd_4187282 53088600047402258607853 := by
  unfold tailWord_4187282
  simp only [CollatzResearch.WordTrace]
  refine ⟨38180680304049979919059025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101815147477466613117490733 38180680304049979919059025)
  ·
    refine ⟨28635510228037484939294269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38180680304049979919059025 28635510228037484939294269)
    ·
      refine ⟨10738316335514056852235351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28635510228037484939294269 10738316335514056852235351)
      ·
        refine ⟨16107474503271085278353027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10738316335514056852235351 16107474503271085278353027)
        ·
          refine ⟨24161211754906627917529541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16107474503271085278353027 24161211754906627917529541)
          ·
            refine ⟨4530227204044992734536789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24161211754906627917529541 4530227204044992734536789)
            ·
              refine ⟨53088600047402258607853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4530227204044992734536789 53088600047402258607853)
              ·
                rfl

theorem cell22_4187282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 8].length) (baseStart_4187282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187282 prefixEnd_4187282 := by exact prefixLift 4187282
  have htrace : WordTrace (prefixWord ++ tailWord_4187282) baseStart_4187282 baseEnd_4187282 := by
    simpa [prefixWord, tailWord_4187282, baseEnd_4187282] using wordTrace_append hprefix tailTrace_4187282
  have hstable : (prefixWord ++ tailWord_4187282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187282).length < 2 ^ (prefixWord ++ tailWord_4187282).sum := by decide
  have hdescent : baseEnd_4187282 < baseStart_4187282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187303 : List Nat := [1, 1, 6, 2, 1, 3, 2, 1, 2, 3]
def baseStart_4187303 : Nat := 118140960795 + 4187303 * 2 ^ 59
def prefixEnd_4187303 : Nat := 4983230072969 + 3 ^ 40 * 4187303 * 2
def baseEnd_4187303 : Nat := 1433399390009023927636967

theorem tailTrace_4187303 : CollatzResearch.WordTrace tailWord_4187303 prefixEnd_4187303 1433399390009023927636967 := by
  unfold tailWord_4187303
  simp only [CollatzResearch.WordTrace]
  refine ⟨152723487149123840262750563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101815658099415893508500375 152723487149123840262750563)
  ·
    refine ⟨229085230723685760394125845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152723487149123840262750563 229085230723685760394125845)
    ·
      refine ⟨10738370190172770018474649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 229085230723685760394125845 10738370190172770018474649)
      ·
        refine ⟨8053777642629577513855987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10738370190172770018474649 8053777642629577513855987)
        ·
          refine ⟨12080666463944366270783981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8053777642629577513855987 12080666463944366270783981)
          ·
            refine ⟨4530249923979137351543993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12080666463944366270783981 4530249923979137351543993)
            ·
              refine ⟨3397687442984353013657995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4530249923979137351543993 3397687442984353013657995)
              ·
                refine ⟨5096531164476529520486993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3397687442984353013657995 5096531164476529520486993)
                ·
                  refine ⟨3822398373357397140365245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5096531164476529520486993 3822398373357397140365245)
                  ·
                    refine ⟨1433399390009023927636967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3822398373357397140365245 1433399390009023927636967)
                    ·
                      rfl

theorem cell22_4187303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_4187303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187303 prefixEnd_4187303 := by exact prefixLift 4187303
  have htrace : WordTrace (prefixWord ++ tailWord_4187303) baseStart_4187303 baseEnd_4187303 := by
    simpa [prefixWord, tailWord_4187303, baseEnd_4187303] using wordTrace_append hprefix tailTrace_4187303
  have hstable : (prefixWord ++ tailWord_4187303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187303).length < 2 ^ (prefixWord ++ tailWord_4187303).sum := by decide
  have hdescent : baseEnd_4187303 < baseStart_4187303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187318 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_4187318 : Nat := 118140960795 + 4187318 * 2 ^ 59
def prefixEnd_4187318 : Nat := 4983230072969 + 3 ^ 40 * 4187318 * 2
def baseEnd_4187318 : Nat := 1433404524815568888511921

theorem tailTrace_4187318 : CollatzResearch.WordTrace tailWord_4187318 prefixEnd_4187318 1433404524815568888511921 := by
  unfold tailWord_4187318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9545252140254343614034163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101816022829379665216364405 9545252140254343614034163)
  ·
    refine ⟨14317878210381515421051245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9545252140254343614034163 14317878210381515421051245)
    ·
      refine ⟨5369204328893068282894217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14317878210381515421051245 5369204328893068282894217)
      ·
        refine ⟨4026903246669801212170663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5369204328893068282894217 4026903246669801212170663)
        ·
          refine ⟨6040354870004701818255995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4026903246669801212170663 6040354870004701818255995)
          ·
            refine ⟨9060532305007052727383993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6040354870004701818255995 9060532305007052727383993)
            ·
              refine ⟨6795399228755289545537995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9060532305007052727383993 6795399228755289545537995)
              ·
                refine ⟨10193098843132934318306993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6795399228755289545537995 10193098843132934318306993)
                ·
                  refine ⟨7644824132349700738730245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10193098843132934318306993 7644824132349700738730245)
                  ·
                    refine ⟨1433404524815568888511921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7644824132349700738730245 1433404524815568888511921)
                    ·
                      rfl

theorem cell22_4187318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_4187318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187318 prefixEnd_4187318 := by exact prefixLift 4187318
  have htrace : WordTrace (prefixWord ++ tailWord_4187318) baseStart_4187318 baseEnd_4187318 := by
    simpa [prefixWord, tailWord_4187318, baseEnd_4187318] using wordTrace_append hprefix tailTrace_4187318
  have hstable : (prefixWord ++ tailWord_4187318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187318).length < 2 ^ (prefixWord ++ tailWord_4187318).sum := by decide
  have hdescent : baseEnd_4187318 < baseStart_4187318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187372 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 6]
def baseStart_4187372 : Nat := 118140960795 + 4187372 * 2 ^ 59
def prefixEnd_4187372 : Nat := 4983230072969 + 3 ^ 40 * 4187372 * 2
def baseEnd_4187372 : Nat := 477807670039710249220585

theorem tailTrace_4187372 : CollatzResearch.WordTrace tailWord_4187372 prefixEnd_4187372 477807670039710249220585 := by
  unfold tailWord_4187372
  simp only [CollatzResearch.WordTrace]
  refine ⟨76363001892936932523506185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101817335857249243364674913 76363001892936932523506185)
  ·
    refine ⟨57272251419702699392629639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76363001892936932523506185 57272251419702699392629639)
    ·
      refine ⟨85908377129554049088944459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57272251419702699392629639 85908377129554049088944459)
      ·
        refine ⟨128862565694331073633416689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85908377129554049088944459 128862565694331073633416689)
        ·
          refine ⟨96646924270748305225062517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128862565694331073633416689 96646924270748305225062517)
          ·
            refine ⟨9060649150382653614849611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96646924270748305225062517 9060649150382653614849611)
            ·
              refine ⟨13590973725573980422274417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9060649150382653614849611 13590973725573980422274417)
              ·
                refine ⟨10193230294180485316705813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13590973725573980422274417 10193230294180485316705813)
                ·
                  refine ⟨477807670039710249220585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10193230294180485316705813 477807670039710249220585)
                  ·
                    rfl

theorem cell22_4187372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_4187372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187372 prefixEnd_4187372 := by exact prefixLift 4187372
  have htrace : WordTrace (prefixWord ++ tailWord_4187372) baseStart_4187372 baseEnd_4187372 := by
    simpa [prefixWord, tailWord_4187372, baseEnd_4187372] using wordTrace_append hprefix tailTrace_4187372
  have hstable : (prefixWord ++ tailWord_4187372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187372).length < 2 ^ (prefixWord ++ tailWord_4187372).sum := by decide
  have hdescent : baseEnd_4187372 < baseStart_4187372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187391 : List Nat := [1, 1, 2, 2, 1, 7, 2, 1, 1, 4]
def baseStart_4187391 : Nat := 118140960795 + 4187391 * 2 ^ 59
def prefixEnd_4187391 : Nat := 4983230072969 + 3 ^ 40 * 4187391 * 2
def baseEnd_4187391 : Nat := 1433429514207421031436697

theorem tailTrace_4187391 : CollatzResearch.WordTrace tailWord_4187391 prefixEnd_4187391 1433429514207421031436697 := by
  unfold tailWord_4187391
  simp only [CollatzResearch.WordTrace]
  refine ⟨152726696772805031291954027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101817797848536687527969351 152726696772805031291954027)
  ·
    refine ⟨229090045159207546937931041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152726696772805031291954027 229090045159207546937931041)
    ·
      refine ⟨171817533869405660203448281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229090045159207546937931041 171817533869405660203448281)
      ·
        refine ⟨128863150402054245152586211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171817533869405660203448281 128863150402054245152586211)
        ·
          refine ⟨193294725603081367728879317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128863150402054245152586211 193294725603081367728879317)
          ·
            refine ⟨4530345131322219556145609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 193294725603081367728879317 4530345131322219556145609)
            ·
              refine ⟨3397758848491664667109207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4530345131322219556145609 3397758848491664667109207)
              ·
                refine ⟨5096638272737497000663811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3397758848491664667109207 5096638272737497000663811)
                ·
                  refine ⟨7644957409106245500995717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5096638272737497000663811 7644957409106245500995717)
                  ·
                    refine ⟨1433429514207421031436697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7644957409106245500995717 1433429514207421031436697)
                    ·
                      rfl

theorem cell22_4187391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 1, 4].length) (baseStart_4187391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187391 prefixEnd_4187391 := by exact prefixLift 4187391
  have htrace : WordTrace (prefixWord ++ tailWord_4187391) baseStart_4187391 baseEnd_4187391 := by
    simpa [prefixWord, tailWord_4187391, baseEnd_4187391] using wordTrace_append hprefix tailTrace_4187391
  have hstable : (prefixWord ++ tailWord_4187391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187391).length < 2 ^ (prefixWord ++ tailWord_4187391).sum := by decide
  have hdescent : baseEnd_4187391 < baseStart_4187391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187402 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_4187402 : Nat := 118140960795 + 4187402 * 2 ^ 59
def prefixEnd_4187402 : Nat := 4983230072969 + 3 ^ 40 * 4187402 * 2
def baseEnd_4187402 : Nat := 1433433279732220669411663

theorem tailTrace_4187402 : CollatzResearch.WordTrace tailWord_4187402 prefixEnd_4187402 1433433279732220669411663 := by
  unfold tailWord_4187402
  simp only [CollatzResearch.WordTrace]
  refine ⟨38181774493941295042651115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101818065317176786780402973 38181774493941295042651115)
  ·
    refine ⟨57272661740911942563976673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38181774493941295042651115 57272661740911942563976673)
    ·
      refine ⟨42954496305683956922982505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57272661740911942563976673 42954496305683956922982505)
      ·
        refine ⟨32215872229262967692236879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42954496305683956922982505 32215872229262967692236879)
        ·
          refine ⟨48323808343894451538355319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32215872229262967692236879 48323808343894451538355319)
          ·
            refine ⟨72485712515841677307532979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48323808343894451538355319 72485712515841677307532979)
            ·
              refine ⟨108728568773762515961299469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72485712515841677307532979 108728568773762515961299469)
              ·
                refine ⟨40773213290160943485487301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108728568773762515961299469 40773213290160943485487301)
                ·
                  refine ⟨7644977491905176903528869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40773213290160943485487301 7644977491905176903528869)
                  ·
                    refine ⟨1433433279732220669411663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7644977491905176903528869 1433433279732220669411663)
                    ·
                      rfl

theorem cell22_4187402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_4187402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187402 prefixEnd_4187402 := by exact prefixLift 4187402
  have htrace : WordTrace (prefixWord ++ tailWord_4187402) baseStart_4187402 baseEnd_4187402 := by
    simpa [prefixWord, tailWord_4187402, baseEnd_4187402] using wordTrace_append hprefix tailTrace_4187402
  have hstable : (prefixWord ++ tailWord_4187402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187402).length < 2 ^ (prefixWord ++ tailWord_4187402).sum := by decide
  have hdescent : baseEnd_4187402 < baseStart_4187402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187404 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 4, 3]
def baseStart_4187404 : Nat := 118140960795 + 4187404 * 2 ^ 59
def prefixEnd_4187404 : Nat := 4983230072969 + 3 ^ 40 * 4187404 * 2
def baseEnd_4187404 : Nat := 1433433964373093330861657

theorem tailTrace_4187404 : CollatzResearch.WordTrace tailWord_4187404 prefixEnd_4187404 1433433964373093330861657 := by
  unfold tailWord_4187404
  simp only [CollatzResearch.WordTrace]
  refine ⟨76363585460878967256088633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101818113947838623008118177 76363585460878967256088633)
  ·
    refine ⟨57272689095659225442066475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76363585460878967256088633 57272689095659225442066475)
    ·
      refine ⟨85909033643488838163099713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57272689095659225442066475 85909033643488838163099713)
      ·
        refine ⟨64431775232616628622324785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85909033643488838163099713 64431775232616628622324785)
        ·
          refine ⟨48323831424462471466743589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64431775232616628622324785 48323831424462471466743589)
          ·
            refine ⟨9060718392086713400014423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48323831424462471466743589 9060718392086713400014423)
            ·
              refine ⟨13591077588130070100021635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9060718392086713400014423 13591077588130070100021635)
              ·
                refine ⟨20386616382195105150032453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13591077588130070100021635 20386616382195105150032453)
                ·
                  refine ⟨3822490571661582215631085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20386616382195105150032453 3822490571661582215631085)
                  ·
                    refine ⟨1433433964373093330861657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3822490571661582215631085 1433433964373093330861657)
                    ·
                      rfl

theorem cell22_4187404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_4187404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187404 prefixEnd_4187404 := by exact prefixLift 4187404
  have htrace : WordTrace (prefixWord ++ tailWord_4187404) baseStart_4187404 baseEnd_4187404 := by
    simpa [prefixWord, tailWord_4187404, baseEnd_4187404] using wordTrace_append hprefix tailTrace_4187404
  have hstable : (prefixWord ++ tailWord_4187404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187404).length < 2 ^ (prefixWord ++ tailWord_4187404).sum := by decide
  have hdescent : baseEnd_4187404 < baseStart_4187404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187421 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_4187421 : Nat := 118140960795 + 4187421 * 2 ^ 59
def prefixEnd_4187421 : Nat := 4983230072969 + 3 ^ 40 * 4187421 * 2
def baseEnd_4187421 : Nat := 1433439783820510953186605

theorem tailTrace_4187421 : CollatzResearch.WordTrace tailWord_4187421 prefixEnd_4187421 1433439783820510953186605 := by
  unfold tailWord_4187421
  simp only [CollatzResearch.WordTrace]
  refine ⟨152727790962696346415546117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101818527308464230943697411 152727790962696346415546117)
  ·
    refine ⟨28636460805505564952914897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152727790962696346415546117 28636460805505564952914897)
    ·
      refine ⟨21477345604129173714686173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28636460805505564952914897 21477345604129173714686173)
      ·
        refine ⟨8054004601548440143007315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21477345604129173714686173 8054004601548440143007315)
        ·
          refine ⟨12081006902322660214510973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054004601548440143007315 12081006902322660214510973)
          ·
            refine ⟨4530377588370997580441615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12081006902322660214510973 4530377588370997580441615)
            ·
              refine ⟨6795566382556496370662423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4530377588370997580441615 6795566382556496370662423)
              ·
                refine ⟨10193349573834744555993635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6795566382556496370662423 10193349573834744555993635)
                ·
                  refine ⟨15290024360752116833990453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10193349573834744555993635 15290024360752116833990453)
                  ·
                    refine ⟨1433439783820510953186605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15290024360752116833990453 1433439783820510953186605)
                    ·
                      rfl

theorem cell22_4187421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_4187421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187421 prefixEnd_4187421 := by exact prefixLift 4187421
  have htrace : WordTrace (prefixWord ++ tailWord_4187421) baseStart_4187421 baseEnd_4187421 := by
    simpa [prefixWord, tailWord_4187421, baseEnd_4187421] using wordTrace_append hprefix tailTrace_4187421
  have hstable : (prefixWord ++ tailWord_4187421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187421).length < 2 ^ (prefixWord ++ tailWord_4187421).sum := by decide
  have hdescent : baseEnd_4187421 < baseStart_4187421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187434 : List Nat := [3, 1, 4, 2, 1, 2, 1, 8]
def baseStart_4187434 : Nat := 118140960795 + 4187434 * 2 ^ 59
def prefixEnd_4187434 : Nat := 4983230072969 + 3 ^ 40 * 4187434 * 2
def baseEnd_4187434 : Nat := 159271581554020361401285

theorem tailTrace_4187434 : CollatzResearch.WordTrace tailWord_4187434 prefixEnd_4187434 159271581554020361401285 := by
  unfold tailWord_4187434
  simp only [CollatzResearch.WordTrace]
  refine ⟨38182066277912312408942339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101818843407766166423846237 38182066277912312408942339)
  ·
    refine ⟨57273099416868468613413509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38182066277912312408942339 57273099416868468613413509)
    ·
      refine ⟨10738706140662837865015033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57273099416868468613413509 10738706140662837865015033)
      ·
        refine ⟨8054029605497128398761275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10738706140662837865015033 8054029605497128398761275)
        ·
          refine ⟨12081044408245692598141913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054029605497128398761275 12081044408245692598141913)
          ·
            refine ⟨9060783306184269448606435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12081044408245692598141913 9060783306184269448606435)
            ·
              refine ⟨13591174959276404172909653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9060783306184269448606435 13591174959276404172909653)
              ·
                refine ⟨159271581554020361401285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13591174959276404172909653 159271581554020361401285)
                ·
                  rfl

theorem cell22_4187434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_4187434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187434 prefixEnd_4187434 := by exact prefixLift 4187434
  have htrace : WordTrace (prefixWord ++ tailWord_4187434) baseStart_4187434 baseEnd_4187434 := by
    simpa [prefixWord, tailWord_4187434, baseEnd_4187434] using wordTrace_append hprefix tailTrace_4187434
  have hstable : (prefixWord ++ tailWord_4187434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187434).length < 2 ^ (prefixWord ++ tailWord_4187434).sum := by decide
  have hdescent : baseEnd_4187434 < baseStart_4187434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187466 : List Nat := [3, 1, 2, 1, 1, 1, 1, 8, 1, 3]
def baseStart_4187466 : Nat := 118140960795 + 4187466 * 2 ^ 59
def prefixEnd_4187466 : Nat := 4983230072969 + 3 ^ 40 * 4187466 * 2
def baseEnd_4187466 : Nat := 1433455188240145835811467

theorem tailTrace_4187466 : CollatzResearch.WordTrace tailWord_4187466 prefixEnd_4187466 1433455188240145835811467 := by
  unfold tailWord_4187466
  simp only [CollatzResearch.WordTrace]
  refine ⟨38182358061883329775233563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101819621498355546067289501 38182358061883329775233563)
  ·
    refine ⟨57273537092824994662850345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38182358061883329775233563 57273537092824994662850345)
    ·
      refine ⟨42955152819618745997137759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57273537092824994662850345 42955152819618745997137759)
      ·
        refine ⟨64432729229428118995706639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42955152819618745997137759 64432729229428118995706639)
        ·
          refine ⟨96649093844142178493559959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64432729229428118995706639 96649093844142178493559959)
          ·
            refine ⟨144973640766213267740339939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96649093844142178493559959 144973640766213267740339939)
            ·
              refine ⟨217460461149319901610509909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144973640766213267740339939 217460461149319901610509909)
              ·
                refine ⟨2548364779093592596998163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 217460461149319901610509909 2548364779093592596998163)
                ·
                  refine ⟨3822547168640388895497245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2548364779093592596998163 3822547168640388895497245)
                  ·
                    refine ⟨1433455188240145835811467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3822547168640388895497245 1433455188240145835811467)
                    ·
                      rfl

theorem cell22_4187466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_4187466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187466 prefixEnd_4187466 := by exact prefixLift 4187466
  have htrace : WordTrace (prefixWord ++ tailWord_4187466) baseStart_4187466 baseEnd_4187466 := by
    simpa [prefixWord, tailWord_4187466, baseEnd_4187466] using wordTrace_append hprefix tailTrace_4187466
  have hstable : (prefixWord ++ tailWord_4187466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187466).length < 2 ^ (prefixWord ++ tailWord_4187466).sum := by decide
  have hdescent : baseEnd_4187466 < baseStart_4187466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187479 : List Nat := [1, 1, 3, 2, 3, 3, 1, 3, 5]
def baseStart_4187479 : Nat := 118140960795 + 4187479 * 2 ^ 59
def prefixEnd_4187479 : Nat := 4983230072969 + 3 ^ 40 * 4187479 * 2
def baseEnd_4187479 : Nat := 477819879468606045078809

theorem tailTrace_4187479 : CollatzResearch.WordTrace tailWord_4187479 prefixEnd_4187479 477819879468606045078809 := by
  unfold tailWord_4187479
  simp only [CollatzResearch.WordTrace]
  refine ⟨152729906396486222321157491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101819937597657481547438327 152729906396486222321157491)
  ·
    refine ⟨229094859594729333481736237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152729906396486222321157491 229094859594729333481736237)
    ·
      refine ⟨85910572348023500055651089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229094859594729333481736237 85910572348023500055651089)
      ·
        refine ⟨64432929261017625041738317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85910572348023500055651089 64432929261017625041738317)
        ·
          refine ⟨24162348472881609390651869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64432929261017625041738317 24162348472881609390651869)
          ·
            refine ⟨9060880677330603521494451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24162348472881609390651869 9060880677330603521494451)
            ·
              refine ⟨13591321015995905282241677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9060880677330603521494451 13591321015995905282241677)
              ·
                refine ⟨5096745380998464480840629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13591321015995905282241677 5096745380998464480840629)
                ·
                  refine ⟨477819879468606045078809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5096745380998464480840629 477819879468606045078809)
                  ·
                    rfl

theorem cell22_4187479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 5].length) (baseStart_4187479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187479 prefixEnd_4187479 := by exact prefixLift 4187479
  have htrace : WordTrace (prefixWord ++ tailWord_4187479) baseStart_4187479 baseEnd_4187479 := by
    simpa [prefixWord, tailWord_4187479, baseEnd_4187479] using wordTrace_append hprefix tailTrace_4187479
  have hstable : (prefixWord ++ tailWord_4187479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187479).length < 2 ^ (prefixWord ++ tailWord_4187479).sum := by decide
  have hdescent : baseEnd_4187479 < baseStart_4187479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187537 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 3, 6]
def baseStart_4187537 : Nat := 118140960795 + 4187537 * 2 ^ 59
def prefixEnd_4187537 : Nat := 4983230072969 + 3 ^ 40 * 4187537 * 2
def baseEnd_4187537 : Nat := 1433479492991125317286249

theorem tailTrace_4187537 : CollatzResearch.WordTrace tailWord_4187537 prefixEnd_4187537 1433479492991125317286249 := by
  unfold tailWord_4187537
  simp only [CollatzResearch.WordTrace]
  refine ⟨152732021830276098226768865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101821347886850732151179243 152732021830276098226768865)
  ·
    refine ⟨114549016372707073670076649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152732021830276098226768865 114549016372707073670076649)
    ·
      refine ⟨85911762279530305252557487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114549016372707073670076649 85911762279530305252557487)
      ·
        refine ⟨128867643419295457878836231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85911762279530305252557487 128867643419295457878836231)
        ·
          refine ⟨193301465128943186818254347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128867643419295457878836231 193301465128943186818254347)
          ·
            refine ⟨289952197693414780227381521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193301465128943186818254347 289952197693414780227381521)
            ·
              refine ⟨217464148270061085170536141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289952197693414780227381521 217464148270061085170536141)
              ·
                refine ⟨81549055601272906938951053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217464148270061085170536141 81549055601272906938951053)
                ·
                  refine ⟨30580895850477340102106645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81549055601272906938951053 30580895850477340102106645)
                  ·
                    refine ⟨1433479492991125317286249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30580895850477340102106645 1433479492991125317286249)
                    ·
                      rfl

theorem cell22_4187537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_4187537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187537 prefixEnd_4187537 := by exact prefixLift 4187537
  have htrace : WordTrace (prefixWord ++ tailWord_4187537) baseStart_4187537 baseEnd_4187537 := by
    simpa [prefixWord, tailWord_4187537, baseEnd_4187537] using wordTrace_append hprefix tailTrace_4187537
  have hstable : (prefixWord ++ tailWord_4187537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187537).length < 2 ^ (prefixWord ++ tailWord_4187537).sum := by decide
  have hdescent : baseEnd_4187537 < baseStart_4187537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187567 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 1, 9]
def baseStart_4187567 : Nat := 118140960795 + 4187567 * 2 ^ 59
def prefixEnd_4187567 : Nat := 4983230072969 + 3 ^ 40 * 4187567 * 2
def baseEnd_4187567 : Nat := 1433489762604215239036157

theorem tailTrace_4187567 : CollatzResearch.WordTrace tailWord_4187567 prefixEnd_4187567 1433489762604215239036157 := by
  unfold tailWord_4187567
  simp only [CollatzResearch.WordTrace]
  refine ⟨152733116020167413350360955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101822077346778275566907303 152733116020167413350360955)
  ·
    refine ⟨229099674030251120025541433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152733116020167413350360955 229099674030251120025541433)
    ·
      refine ⟨171824755522688340019156075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229099674030251120025541433 171824755522688340019156075)
      ·
        refine ⟨257737133284032510028734113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171824755522688340019156075 257737133284032510028734113)
        ·
          refine ⟨193302849963024382521550585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257737133284032510028734113 193302849963024382521550585)
          ·
            refine ⟨144977137472268286891162939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193302849963024382521550585 144977137472268286891162939)
            ·
              refine ⟨217465706208402430336744409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144977137472268286891162939 217465706208402430336744409)
              ·
                refine ⟨163099279656301822752558307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217465706208402430336744409 163099279656301822752558307)
                ·
                  refine ⟨244648919484452734128837461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163099279656301822752558307 244648919484452734128837461)
                  ·
                    refine ⟨1433489762604215239036157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 244648919484452734128837461 1433489762604215239036157)
                    ·
                      rfl

theorem cell22_4187567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_4187567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187567 prefixEnd_4187567 := by exact prefixLift 4187567
  have htrace : WordTrace (prefixWord ++ tailWord_4187567) baseStart_4187567 baseEnd_4187567 := by
    simpa [prefixWord, tailWord_4187567, baseEnd_4187567] using wordTrace_append hprefix tailTrace_4187567
  have hstable : (prefixWord ++ tailWord_4187567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187567).length < 2 ^ (prefixWord ++ tailWord_4187567).sum := by decide
  have hdescent : baseEnd_4187567 < baseStart_4187567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187573 : List Nat := [1, 3, 3, 2, 2, 1, 3, 2, 2, 3]
def baseStart_4187573 : Nat := 118140960795 + 4187573 * 2 ^ 59
def prefixEnd_4187573 : Nat := 4983230072969 + 3 ^ 40 * 4187573 * 2
def baseEnd_4187573 : Nat := 1433491816526833223386139

theorem tailTrace_4187573 : CollatzResearch.WordTrace tailWord_4187573 prefixEnd_4187573 1433491816526833223386139 := by
  unfold tailWord_4187573
  simp only [CollatzResearch.WordTrace]
  refine ⟨152733334858145676375079373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101822223238763784250052915 152733334858145676375079373)
  ·
    refine ⟨57275000571804628640654765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152733334858145676375079373 57275000571804628640654765)
    ·
      refine ⟨21478125214426735740245537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57275000571804628640654765 21478125214426735740245537)
      ·
        refine ⟨16108593910820051805184153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21478125214426735740245537 16108593910820051805184153)
        ·
          refine ⟨12081445433115038853888115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16108593910820051805184153 12081445433115038853888115)
          ·
            refine ⟨18122168149672558280832173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12081445433115038853888115 18122168149672558280832173)
            ·
              refine ⟨6795813056127209355312065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18122168149672558280832173 6795813056127209355312065)
              ·
                refine ⟨5096859792095407016484049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6795813056127209355312065 5096859792095407016484049)
                ·
                  refine ⟨3822644844071555262363037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5096859792095407016484049 3822644844071555262363037)
                  ·
                    refine ⟨1433491816526833223386139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3822644844071555262363037 1433491816526833223386139)
                    ·
                      rfl

theorem cell22_4187573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_4187573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187573 prefixEnd_4187573 := by exact prefixLift 4187573
  have htrace : WordTrace (prefixWord ++ tailWord_4187573) baseStart_4187573 baseEnd_4187573 := by
    simpa [prefixWord, tailWord_4187573, baseEnd_4187573] using wordTrace_append hprefix tailTrace_4187573
  have hstable : (prefixWord ++ tailWord_4187573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187573).length < 2 ^ (prefixWord ++ tailWord_4187573).sum := by decide
  have hdescent : baseEnd_4187573 < baseStart_4187573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187708 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 1, 5]
def baseStart_4187708 : Nat := 118140960795 + 4187708 * 2 ^ 59
def prefixEnd_4187708 : Nat := 4983230072969 + 3 ^ 40 * 4187708 * 2
def baseEnd_4187708 : Nat := 1433538029785737871260725

theorem tailTrace_4187708 : CollatzResearch.WordTrace tailWord_4187708 prefixEnd_4187708 1433538029785737871260725 := by
  unfold tailWord_4187708
  simp only [CollatzResearch.WordTrace]
  refine ⟨76369129356328297215621889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101825505808437729620829185 76369129356328297215621889)
  ·
    refine ⟨57276847017246222911716417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76369129356328297215621889 57276847017246222911716417)
    ·
      refine ⟨42957635262934667183787313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57276847017246222911716417 42957635262934667183787313)
      ·
        refine ⟨32218226447201000387840485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42957635262934667183787313 32218226447201000387840485)
        ·
          refine ⟨6040917458850187572720091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32218226447201000387840485 6040917458850187572720091)
          ·
            refine ⟨9061376188275281359080137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6040917458850187572720091 9061376188275281359080137)
            ·
              refine ⟨6796032141206461019310103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9061376188275281359080137 6796032141206461019310103)
              ·
                refine ⟨10194048211809691528965155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6796032141206461019310103 10194048211809691528965155)
                ·
                  refine ⟨15291072317714537293447733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10194048211809691528965155 15291072317714537293447733)
                  ·
                    refine ⟨1433538029785737871260725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15291072317714537293447733 1433538029785737871260725)
                    ·
                      rfl

theorem cell22_4187708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_4187708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187708 prefixEnd_4187708 := by exact prefixLift 4187708
  have htrace : WordTrace (prefixWord ++ tailWord_4187708) baseStart_4187708 baseEnd_4187708 := by
    simpa [prefixWord, tailWord_4187708, baseEnd_4187708] using wordTrace_append hprefix tailTrace_4187708
  have hstable : (prefixWord ++ tailWord_4187708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187708).length < 2 ^ (prefixWord ++ tailWord_4187708).sum := by decide
  have hdescent : baseEnd_4187708 < baseStart_4187708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187736 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 7, 3]
def baseStart_4187736 : Nat := 118140960795 + 4187736 * 2 ^ 59
def prefixEnd_4187736 : Nat := 4983230072969 + 3 ^ 40 * 4187736 * 2
def baseEnd_4187736 : Nat := 1433547614757955131560639

theorem tailTrace_4187736 : CollatzResearch.WordTrace tailWord_4187736 prefixEnd_4187736 1433547614757955131560639 := by
  unfold tailWord_4187736
  simp only [CollatzResearch.WordTrace]
  refine ⟨76369639978277577606631531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101826186637703436808842041 76369639978277577606631531)
  ·
    refine ⟨114554459967416366409947297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76369639978277577606631531 114554459967416366409947297)
    ·
      refine ⟨85915844975562274807460473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114554459967416366409947297 85915844975562274807460473)
      ·
        refine ⟨64436883731671706105595355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85915844975562274807460473 64436883731671706105595355)
        ·
          refine ⟨96655325597507559158393033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64436883731671706105595355 96655325597507559158393033)
          ·
            refine ⟨72491494198130669368794775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96655325597507559158393033 72491494198130669368794775)
            ·
              refine ⟨108737241297196004053192163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72491494198130669368794775 108737241297196004053192163)
              ·
                refine ⟨163105861945794006079788245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108737241297196004053192163 163105861945794006079788245)
                ·
                  refine ⟨3822793639354547017495037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 163105861945794006079788245 3822793639354547017495037)
                  ·
                    refine ⟨1433547614757955131560639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3822793639354547017495037 1433547614757955131560639)
                    ·
                      rfl

theorem cell22_4187736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_4187736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187736 prefixEnd_4187736 := by exact prefixLift 4187736
  have htrace : WordTrace (prefixWord ++ tailWord_4187736) baseStart_4187736 baseEnd_4187736 := by
    simpa [prefixWord, tailWord_4187736, baseEnd_4187736] using wordTrace_append hprefix tailTrace_4187736
  have hstable : (prefixWord ++ tailWord_4187736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187736).length < 2 ^ (prefixWord ++ tailWord_4187736).sum := by decide
  have hdescent : baseEnd_4187736 < baseStart_4187736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187804 : List Nat := [2, 2, 3, 2, 3, 1, 3, 2, 1, 3]
def baseStart_4187804 : Nat := 118140960795 + 4187804 * 2 ^ 59
def prefixEnd_4187804 : Nat := 4983230072969 + 3 ^ 40 * 4187804 * 2
def baseEnd_4187804 : Nat := 1433570892547625620860431

theorem tailTrace_4187804 : CollatzResearch.WordTrace tailWord_4187804 prefixEnd_4187804 1433570892547625620860431 := by
  unfold tailWord_4187804
  simp only [CollatzResearch.WordTrace]
  refine ⟨76370880060154401413369233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101827840080205868551158977 76370880060154401413369233)
  ·
    refine ⟨57278160045115801060026925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76370880060154401413369233 57278160045115801060026925)
    ·
      refine ⟨21479310016918425397510097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57278160045115801060026925 21479310016918425397510097)
      ·
        refine ⟨16109482512688819048132573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21479310016918425397510097 16109482512688819048132573)
        ·
          refine ⟨6041055942258307143049715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16109482512688819048132573 6041055942258307143049715)
          ·
            refine ⟨9061583913387460714574573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6041055942258307143049715 9061583913387460714574573)
            ·
              refine ⟨3398093967520297767965465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9061583913387460714574573 3398093967520297767965465)
              ·
                refine ⟨2548570475640223325974099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3398093967520297767965465 2548570475640223325974099)
                ·
                  refine ⟨3822855713460334988961149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2548570475640223325974099 3822855713460334988961149)
                  ·
                    refine ⟨1433570892547625620860431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3822855713460334988961149 1433570892547625620860431)
                    ·
                      rfl

theorem cell22_4187804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_4187804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187804 prefixEnd_4187804 := by exact prefixLift 4187804
  have htrace : WordTrace (prefixWord ++ tailWord_4187804) baseStart_4187804 baseEnd_4187804 := by
    simpa [prefixWord, tailWord_4187804, baseEnd_4187804] using wordTrace_append hprefix tailTrace_4187804
  have hstable : (prefixWord ++ tailWord_4187804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187804).length < 2 ^ (prefixWord ++ tailWord_4187804).sum := by decide
  have hdescent : baseEnd_4187804 < baseStart_4187804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187892 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_4187892 : Nat := 118140960795 + 4187892 * 2 ^ 59
def prefixEnd_4187892 : Nat := 4983230072969 + 3 ^ 40 * 4187892 * 2
def baseEnd_4187892 : Nat := 1433601016746022724660161

theorem tailTrace_4187892 : CollatzResearch.WordTrace tailWord_4187892 prefixEnd_4187892 1433601016746022724660161 := by
  unfold tailWord_4187892
  simp only [CollatzResearch.WordTrace]
  refine ⟨76372484871994996927970965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101829979829326662570627953 76372484871994996927970965)
  ·
    refine ⟨3579960228374765480998639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76372484871994996927970965 3579960228374765480998639)
    ·
      refine ⟨5369940342562148221497959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3579960228374765480998639 5369940342562148221497959)
      ·
        refine ⟨8054910513843222332246939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5369940342562148221497959 8054910513843222332246939)
        ·
          refine ⟨12082365770764833498370409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054910513843222332246939 12082365770764833498370409)
          ·
            refine ⟨9061774328073625123777807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12082365770764833498370409 9061774328073625123777807)
            ·
              refine ⟨13592661492110437685666711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9061774328073625123777807 13592661492110437685666711)
              ·
                refine ⟨20388992238165656528500067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13592661492110437685666711 20388992238165656528500067)
                ·
                  refine ⟨30583488357248484792750101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20388992238165656528500067 30583488357248484792750101)
                  ·
                    refine ⟨1433601016746022724660161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30583488357248484792750101 1433601016746022724660161)
                    ·
                      rfl

theorem cell22_4187892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_4187892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187892 prefixEnd_4187892 := by exact prefixLift 4187892
  have htrace : WordTrace (prefixWord ++ tailWord_4187892) baseStart_4187892 baseEnd_4187892 := by
    simpa [prefixWord, tailWord_4187892, baseEnd_4187892] using wordTrace_append hprefix tailTrace_4187892
  have hstable : (prefixWord ++ tailWord_4187892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187892).length < 2 ^ (prefixWord ++ tailWord_4187892).sum := by decide
  have hdescent : baseEnd_4187892 < baseStart_4187892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187922 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_4187922 : Nat := 118140960795 + 4187922 * 2 ^ 59
def prefixEnd_4187922 : Nat := 4983230072969 + 3 ^ 40 * 4187922 * 2
def baseEnd_4187922 : Nat := 1433611286359112646410069

theorem tailTrace_4187922 : CollatzResearch.WordTrace tailWord_4187922 prefixEnd_4187922 1433611286359112646410069 := by
  unfold tailWord_4187922
  simp only [CollatzResearch.WordTrace]
  refine ⟨38186515983470327244883505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101830709289254205986356013 38186515983470327244883505)
  ·
    refine ⟨28639886987602745433662629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38186515983470327244883505 28639886987602745433662629)
    ·
      refine ⟨5369978810175514768811743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28639886987602745433662629 5369978810175514768811743)
      ·
        refine ⟨8054968215263272153217615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5369978810175514768811743 8054968215263272153217615)
        ·
          refine ⟨12082452322894908229826423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8054968215263272153217615 12082452322894908229826423)
          ·
            refine ⟨18123678484342362344739635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12082452322894908229826423 18123678484342362344739635)
            ·
              refine ⟨27185517726513543517109453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18123678484342362344739635 27185517726513543517109453)
              ·
                refine ⟨10194569147442578818916045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27185517726513543517109453 10194569147442578818916045)
                ·
                  refine ⟨3822963430290967057093517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10194569147442578818916045 3822963430290967057093517)
                  ·
                    refine ⟨1433611286359112646410069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3822963430290967057093517 1433611286359112646410069)
                    ·
                      rfl

theorem cell22_4187922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_4187922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187922 prefixEnd_4187922 := by exact prefixLift 4187922
  have htrace : WordTrace (prefixWord ++ tailWord_4187922) baseStart_4187922 baseEnd_4187922 := by
    simpa [prefixWord, tailWord_4187922, baseEnd_4187922] using wordTrace_append hprefix tailTrace_4187922
  have hstable : (prefixWord ++ tailWord_4187922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187922).length < 2 ^ (prefixWord ++ tailWord_4187922).sum := by decide
  have hdescent : baseEnd_4187922 < baseStart_4187922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187935 : List Nat := [1, 1, 2, 4, 2, 1, 5, 1, 5]
def baseStart_4187935 : Nat := 118140960795 + 4187935 * 2 ^ 59
def prefixEnd_4187935 : Nat := 4983230072969 + 3 ^ 40 * 4187935 * 2
def baseEnd_4187935 : Nat := 477871912174928315278343

theorem tailTrace_4187935 : CollatzResearch.WordTrace tailWord_4187935 prefixEnd_4187935 477871912174928315278343 := by
  unfold tailWord_4187935
  simp only [CollatzResearch.WordTrace]
  refine ⟨152746538082834212199757259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101831025388556141466504839 152746538082834212199757259)
  ·
    refine ⟨229119807124251318299635889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152746538082834212199757259 229119807124251318299635889)
    ·
      refine ⟨171839855343188488724726917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229119807124251318299635889 171839855343188488724726917)
      ·
        refine ⟨32219972876847841635886297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171839855343188488724726917 32219972876847841635886297)
        ·
          refine ⟨24164979657635881226914723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32219972876847841635886297 24164979657635881226914723)
          ·
            refine ⟨36247469486453821840372085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24164979657635881226914723 36247469486453821840372085)
            ·
              refine ⟨3398200264355045797534883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36247469486453821840372085 3398200264355045797534883)
              ·
                refine ⟨5097300396532568696302325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3398200264355045797534883 5097300396532568696302325)
                ·
                  refine ⟨477871912174928315278343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5097300396532568696302325 477871912174928315278343)
                  ·
                    rfl

theorem cell22_4187935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 5].length) (baseStart_4187935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187935 prefixEnd_4187935 := by exact prefixLift 4187935
  have htrace : WordTrace (prefixWord ++ tailWord_4187935) baseStart_4187935 baseEnd_4187935 := by
    simpa [prefixWord, tailWord_4187935, baseEnd_4187935] using wordTrace_append hprefix tailTrace_4187935
  have hstable : (prefixWord ++ tailWord_4187935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187935).length < 2 ^ (prefixWord ++ tailWord_4187935).sum := by decide
  have hdescent : baseEnd_4187935 < baseStart_4187935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187956 : List Nat := [2, 5, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_4187956 : Nat := 118140960795 + 4187956 * 2 ^ 59
def prefixEnd_4187956 : Nat := 4983230072969 + 3 ^ 40 * 4187956 * 2
def baseEnd_4187956 : Nat := 1433622925253947891059965

theorem tailTrace_4187956 : CollatzResearch.WordTrace tailWord_4187956 prefixEnd_4187956 1433622925253947891059965 := by
  unfold tailWord_4187956
  simp only [CollatzResearch.WordTrace]
  refine ⟨76373652007879066393135861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101831536010505421857514481 76373652007879066393135861)
  ·
    refine ⟨7160029875738662474356487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76373652007879066393135861 7160029875738662474356487)
    ·
      refine ⟨10740044813607993711534731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7160029875738662474356487 10740044813607993711534731)
      ·
        refine ⟨16110067220411990567302097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10740044813607993711534731 16110067220411990567302097)
        ·
          refine ⟨12082550415308992925476573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16110067220411990567302097 12082550415308992925476573)
          ·
            refine ⟨4530956405740872347053715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12082550415308992925476573 4530956405740872347053715)
            ·
              refine ⟨6796434608611308520580573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4530956405740872347053715 6796434608611308520580573)
              ·
                refine ⟨2548662978229240695217715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6796434608611308520580573 2548662978229240695217715)
                ·
                  refine ⟨3822994467343861042826573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2548662978229240695217715 3822994467343861042826573)
                  ·
                    refine ⟨1433622925253947891059965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3822994467343861042826573 1433622925253947891059965)
                    ·
                      rfl

theorem cell22_4187956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_4187956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187956 prefixEnd_4187956 := by exact prefixLift 4187956
  have htrace : WordTrace (prefixWord ++ tailWord_4187956) baseStart_4187956 baseEnd_4187956 := by
    simpa [prefixWord, tailWord_4187956, baseEnd_4187956] using wordTrace_append hprefix tailTrace_4187956
  have hstable : (prefixWord ++ tailWord_4187956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187956).length < 2 ^ (prefixWord ++ tailWord_4187956).sum := by decide
  have hdescent : baseEnd_4187956 < baseStart_4187956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4187993 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 4, 4]
def baseStart_4187993 : Nat := 118140960795 + 4187993 * 2 ^ 59
def prefixEnd_4187993 : Nat := 4983230072969 + 3 ^ 40 * 4187993 * 2
def baseEnd_4187993 : Nat := 1433635591110092127884851

theorem tailTrace_4187993 : CollatzResearch.WordTrace tailWord_4187993 prefixEnd_4187993 1433635591110092127884851 := by
  unfold tailWord_4187993
  simp only [CollatzResearch.WordTrace]
  refine ⟨152748653516624088105368633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101832435677749392070245755 152748653516624088105368633)
  ·
    refine ⟨114561490137468066079026475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152748653516624088105368633 114561490137468066079026475)
    ·
      refine ⟨171842235206202099118539713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114561490137468066079026475 171842235206202099118539713)
      ·
        refine ⟨128881676404651574338904785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171842235206202099118539713 128881676404651574338904785)
        ·
          refine ⟨96661257303488680754178589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128881676404651574338904785 96661257303488680754178589)
          ·
            refine ⟨36247971488808255282816971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96661257303488680754178589 36247971488808255282816971)
            ·
              refine ⟨54371957233212382924225457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36247971488808255282816971 54371957233212382924225457)
              ·
                refine ⟨40778967924909287193169093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54371957233212382924225457 40778967924909287193169093)
                ·
                  refine ⟨7646056485920491348719205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40778967924909287193169093 7646056485920491348719205)
                  ·
                    refine ⟨1433635591110092127884851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7646056485920491348719205 1433635591110092127884851)
                    ·
                      rfl

theorem cell22_4187993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_4187993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4187993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4187993 prefixEnd_4187993 := by exact prefixLift 4187993
  have htrace : WordTrace (prefixWord ++ tailWord_4187993) baseStart_4187993 baseEnd_4187993 := by
    simpa [prefixWord, tailWord_4187993, baseEnd_4187993] using wordTrace_append hprefix tailTrace_4187993
  have hstable : (prefixWord ++ tailWord_4187993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4187993).length < 2 ^ (prefixWord ++ tailWord_4187993).sum := by decide
  have hdescent : baseEnd_4187993 < baseStart_4187993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4187993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188008 : List Nat := [2, 1, 4, 2, 1, 1, 1, 10]
def baseStart_4188008 : Nat := 118140960795 + 4188008 * 2 ^ 59
def prefixEnd_4188008 : Nat := 4983230072969 + 3 ^ 40 * 4188008 * 2
def baseEnd_4188008 : Nat := 159293413990737454306645

theorem tailTrace_4188008 : CollatzResearch.WordTrace tailWord_4188008 prefixEnd_4188008 159293413990737454306645 := by
  unfold tailWord_4188008
  simp only [CollatzResearch.WordTrace]
  refine ⟨76374600305784872833582339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101832800407713163778109785 76374600305784872833582339)
  ·
    refine ⟨114561900458677309250373509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76374600305784872833582339 114561900458677309250373509)
    ·
      refine ⟨21480356336001995484445033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114561900458677309250373509 21480356336001995484445033)
      ·
        refine ⟨16110267252001496613333775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21480356336001995484445033 16110267252001496613333775)
        ·
          refine ⟨24165400878002244920000663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16110267252001496613333775 24165400878002244920000663)
          ·
            refine ⟨36248101317003367380000995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24165400878002244920000663 36248101317003367380000995)
            ·
              refine ⟨54372151975505051070001493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36248101317003367380000995 54372151975505051070001493)
              ·
                refine ⟨159293413990737454306645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 54372151975505051070001493 159293413990737454306645)
                ·
                  rfl

theorem cell22_4188008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 10].length) (baseStart_4188008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188008 prefixEnd_4188008 := by exact prefixLift 4188008
  have htrace : WordTrace (prefixWord ++ tailWord_4188008) baseStart_4188008 baseEnd_4188008 := by
    simpa [prefixWord, tailWord_4188008, baseEnd_4188008] using wordTrace_append hprefix tailTrace_4188008
  have hstable : (prefixWord ++ tailWord_4188008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188008).length < 2 ^ (prefixWord ++ tailWord_4188008).sum := by decide
  have hdescent : baseEnd_4188008 < baseStart_4188008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188042 : List Nat := [3, 1, 2, 4, 2, 2, 1, 7]
def baseStart_4188042 : Nat := 118140960795 + 4188042 * 2 ^ 59
def prefixEnd_4188042 : Nat := 4983230072969 + 3 ^ 40 * 4188042 * 2
def baseEnd_4188042 : Nat := 159294707201274703712189

theorem tailTrace_4188042 : CollatzResearch.WordTrace tailWord_4188042 prefixEnd_4188042 159294707201274703712189 := by
  unfold tailWord_4188042
  simp only [CollatzResearch.WordTrace]
  refine ⟨38187610173361642368475595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101833627128964379649268253 38187610173361642368475595)
  ·
    refine ⟨57281415260042463552713393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38187610173361642368475595 57281415260042463552713393)
    ·
      refine ⟨42961061445031847664535045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57281415260042463552713393 42961061445031847664535045)
      ·
        refine ⟨8055199020943471437100321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42961061445031847664535045 8055199020943471437100321)
        ·
          refine ⟨6041399265707603577825241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8055199020943471437100321 6041399265707603577825241)
          ·
            refine ⟨4531049449280702683368931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6041399265707603577825241 4531049449280702683368931)
            ·
              refine ⟨6796574173921054025053397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4531049449280702683368931 6796574173921054025053397)
              ·
                refine ⟨159294707201274703712189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6796574173921054025053397 159294707201274703712189)
                ·
                  rfl

theorem cell22_4188042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 7].length) (baseStart_4188042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188042 prefixEnd_4188042 := by exact prefixLift 4188042
  have htrace : WordTrace (prefixWord ++ tailWord_4188042) baseStart_4188042 baseEnd_4188042 := by
    simpa [prefixWord, tailWord_4188042, baseEnd_4188042] using wordTrace_append hprefix tailTrace_4188042
  have hstable : (prefixWord ++ tailWord_4188042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188042).length < 2 ^ (prefixWord ++ tailWord_4188042).sum := by decide
  have hdescent : baseEnd_4188042 < baseStart_4188042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188085 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_4188085 : Nat := 118140960795 + 4188085 * 2 ^ 59
def prefixEnd_4188085 : Nat := 4983230072969 + 3 ^ 40 * 4188085 * 2
def baseEnd_4188085 : Nat := 1433667084590234554584569

theorem tailTrace_4188085 : CollatzResearch.WordTrace tailWord_4188085 prefixEnd_4188085 1433667084590234554584569 := by
  unfold tailWord_4188085
  simp only [CollatzResearch.WordTrace]
  refine ⟨152752009032290787817717709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101834672688193858545145139 152752009032290787817717709)
  ·
    refine ⟨57282003387109045431644141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152752009032290787817717709 57282003387109045431644141)
    ·
      refine ⟨21480751270165892036866553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57282003387109045431644141 21480751270165892036866553)
      ·
        refine ⟨16110563452624419027649915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21480751270165892036866553 16110563452624419027649915)
        ·
          refine ⟨24165845178936628541474873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16110563452624419027649915 24165845178936628541474873)
          ·
            refine ⟨18124383884202471406106155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24165845178936628541474873 18124383884202471406106155)
            ·
              refine ⟨27186575826303707109159233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18124383884202471406106155 27186575826303707109159233)
              ·
                refine ⟨20389931869727780331869425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27186575826303707109159233 20389931869727780331869425)
                ·
                  refine ⟨15292448902295835248902069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20389931869727780331869425 15292448902295835248902069)
                  ·
                    refine ⟨1433667084590234554584569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15292448902295835248902069 1433667084590234554584569)
                    ·
                      rfl

theorem cell22_4188085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_4188085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188085 prefixEnd_4188085 := by exact prefixLift 4188085
  have htrace : WordTrace (prefixWord ++ tailWord_4188085) baseStart_4188085 baseEnd_4188085 := by
    simpa [prefixWord, tailWord_4188085, baseEnd_4188085] using wordTrace_append hprefix tailTrace_4188085
  have hstable : (prefixWord ++ tailWord_4188085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188085).length < 2 ^ (prefixWord ++ tailWord_4188085).sum := by decide
  have hdescent : baseEnd_4188085 < baseStart_4188085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188117 : List Nat := [1, 3, 2, 3, 2, 1, 1, 4, 1, 4]
def baseStart_4188117 : Nat := 118140960795 + 4188117 * 2 ^ 59
def prefixEnd_4188117 : Nat := 4983230072969 + 3 ^ 40 * 4188117 * 2
def baseEnd_4188117 : Nat := 1433678038844197137784471

theorem tailTrace_4188117 : CollatzResearch.WordTrace tailWord_4188117 prefixEnd_4188117 1433678038844197137784471 := by
  unfold tailWord_4188117
  simp only [CollatzResearch.WordTrace]
  refine ⟨152753176168174857282882605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101835450778783238188588403 152753176168174857282882605)
  ·
    refine ⟨57282441063065571481080977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152753176168174857282882605 57282441063065571481080977)
    ·
      refine ⟨42961830797299178610810733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57282441063065571481080977 42961830797299178610810733)
      ·
        refine ⟨16110686548987191979054025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42961830797299178610810733 16110686548987191979054025)
        ·
          refine ⟨12083014911740393984290519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16110686548987191979054025 12083014911740393984290519)
          ·
            refine ⟨18124522367610590976435779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12083014911740393984290519 18124522367610590976435779)
            ·
              refine ⟨27186783551415886464653669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18124522367610590976435779 27186783551415886464653669)
              ·
                refine ⟨5097521915890478712122563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27186783551415886464653669 5097521915890478712122563)
                ·
                  refine ⟨7646282873835718068183845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5097521915890478712122563 7646282873835718068183845)
                  ·
                    refine ⟨1433678038844197137784471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7646282873835718068183845 1433678038844197137784471)
                    ·
                      rfl

theorem cell22_4188117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_4188117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188117 prefixEnd_4188117 := by exact prefixLift 4188117
  have htrace : WordTrace (prefixWord ++ tailWord_4188117) baseStart_4188117 baseEnd_4188117 := by
    simpa [prefixWord, tailWord_4188117, baseEnd_4188117] using wordTrace_append hprefix tailTrace_4188117
  have hstable : (prefixWord ++ tailWord_4188117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188117).length < 2 ^ (prefixWord ++ tailWord_4188117).sum := by decide
  have hdescent : baseEnd_4188117 < baseStart_4188117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188200 : List Nat := [2, 1, 5, 3, 2, 1, 2, 2, 4]
def baseStart_4188200 : Nat := 118140960795 + 4188200 * 2 ^ 59
def prefixEnd_4188200 : Nat := 4983230072969 + 3 ^ 40 * 4188200 * 2
def baseEnd_4188200 : Nat := 477902150480137529319739

theorem tailTrace_4188200 : CollatzResearch.WordTrace tailWord_4188200 prefixEnd_4188200 477902150480137529319739 := by
  unfold tailWord_4188200
  simp only [CollatzResearch.WordTrace]
  refine ⟨76378101713437081229077027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101837468951249441638769369 76378101713437081229077027)
  ·
    refine ⟨114567152570155621843615541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76378101713437081229077027 114567152570155621843615541)
    ·
      refine ⟨10740670553452089547838957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114567152570155621843615541 10740670553452089547838957)
      ·
        refine ⟨4027751457544533580439609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10740670553452089547838957 4027751457544533580439609)
        ·
          refine ⟨3020813593158400185329707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4027751457544533580439609 3020813593158400185329707)
          ·
            refine ⟨4531220389737600277994561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3020813593158400185329707 4531220389737600277994561)
            ·
              refine ⟨3398415292303200208495921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4531220389737600277994561 3398415292303200208495921)
              ·
                refine ⟨2548811469227400156371941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3398415292303200208495921 2548811469227400156371941)
                ·
                  refine ⟨477902150480137529319739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2548811469227400156371941 477902150480137529319739)
                  ·
                    rfl

theorem cell22_4188200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 4].length) (baseStart_4188200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188200 prefixEnd_4188200 := by exact prefixLift 4188200
  have htrace : WordTrace (prefixWord ++ tailWord_4188200) baseStart_4188200 baseEnd_4188200 := by
    simpa [prefixWord, tailWord_4188200, baseEnd_4188200] using wordTrace_append hprefix tailTrace_4188200
  have hstable : (prefixWord ++ tailWord_4188200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188200).length < 2 ^ (prefixWord ++ tailWord_4188200).sum := by decide
  have hdescent : baseEnd_4188200 < baseStart_4188200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188237 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_4188237 : Nat := 118140960795 + 4188237 * 2 ^ 59
def prefixEnd_4188237 : Nat := 4983230072969 + 3 ^ 40 * 4188237 * 2
def baseEnd_4188237 : Nat := 1433719117296556824784103

theorem tailTrace_4188237 : CollatzResearch.WordTrace tailWord_4188237 prefixEnd_4188237 1433719117296556824784103 := by
  unfold tailWord_4188237
  simp only [CollatzResearch.WordTrace]
  refine ⟨152757552927740117777250965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101838368618493411851500643 152757552927740117777250965)
  ·
    refine ⟨7160510293487818020808639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152757552927740117777250965 7160510293487818020808639)
    ·
      refine ⟨10740765440231727031212959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7160510293487818020808639 10740765440231727031212959)
      ·
        refine ⟨16111148160347590546819439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10740765440231727031212959 16111148160347590546819439)
        ·
          refine ⟨24166722240521385820229159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16111148160347590546819439 24166722240521385820229159)
          ·
            refine ⟨36250083360782078730343739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24166722240521385820229159 36250083360782078730343739)
            ·
              refine ⟨54375125041173118095515609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36250083360782078730343739 54375125041173118095515609)
              ·
                refine ⟨40781343780879838571636707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54375125041173118095515609 40781343780879838571636707)
                ·
                  refine ⟨61172015671319757857455061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40781343780879838571636707 61172015671319757857455061)
                  ·
                    refine ⟨1433719117296556824784103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61172015671319757857455061 1433719117296556824784103)
                    ·
                      rfl

theorem cell22_4188237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_4188237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188237 prefixEnd_4188237 := by exact prefixLift 4188237
  have htrace : WordTrace (prefixWord ++ tailWord_4188237) baseStart_4188237 baseEnd_4188237 := by
    simpa [prefixWord, tailWord_4188237, baseEnd_4188237] using wordTrace_append hprefix tailTrace_4188237
  have hstable : (prefixWord ++ tailWord_4188237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188237).length < 2 ^ (prefixWord ++ tailWord_4188237).sum := by decide
  have hdescent : baseEnd_4188237 < baseStart_4188237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188250 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 8]
def baseStart_4188250 : Nat := 118140960795 + 4188250 * 2 ^ 59
def prefixEnd_4188250 : Nat := 4983230072969 + 3 ^ 40 * 4188250 * 2
def baseEnd_4188250 : Nat := 477907855820743041403021

theorem tailTrace_4188250 : CollatzResearch.WordTrace tailWord_4188250 prefixEnd_4188250 477907855820743041403021 := by
  unfold tailWord_4188250
  simp only [CollatzResearch.WordTrace]
  refine ⟨38189506769173255249368551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101838684717795347331649469 38189506769173255249368551)
  ·
    refine ⟨57284260153759882874052827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38189506769173255249368551 57284260153759882874052827)
    ·
      refine ⟨85926390230639824311079241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57284260153759882874052827 85926390230639824311079241)
      ·
        refine ⟨64444792672979868233309431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85926390230639824311079241 64444792672979868233309431)
        ·
          refine ⟨96667189009469802349964147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64444792672979868233309431 96667189009469802349964147)
          ·
            refine ⟨145000783514204703524946221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96667189009469802349964147 145000783514204703524946221)
            ·
              refine ⟨54375293817826763821854833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145000783514204703524946221 54375293817826763821854833)
              ·
                refine ⟨40781470363370072866391125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54375293817826763821854833 40781470363370072866391125)
                ·
                  refine ⟨477907855820743041403021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40781470363370072866391125 477907855820743041403021)
                  ·
                    rfl

theorem cell22_4188250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_4188250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188250 prefixEnd_4188250 := by exact prefixLift 4188250
  have htrace : WordTrace (prefixWord ++ tailWord_4188250) baseStart_4188250 baseEnd_4188250 := by
    simpa [prefixWord, tailWord_4188250, baseEnd_4188250] using wordTrace_append hprefix tailTrace_4188250
  have hstable : (prefixWord ++ tailWord_4188250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188250).length < 2 ^ (prefixWord ++ tailWord_4188250).sum := by decide
  have hdescent : baseEnd_4188250 < baseStart_4188250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188297 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 2, 4]
def baseStart_4188297 : Nat := 118140960795 + 4188297 * 2 ^ 59
def prefixEnd_4188297 : Nat := 4983230072969 + 3 ^ 40 * 4188297 * 2
def baseEnd_4188297 : Nat := 1433739656522736668283919

theorem tailTrace_4188297 : CollatzResearch.WordTrace tailWord_4188297 prefixEnd_4188297 1433739656522736668283919 := by
  unfold tailWord_4188297
  simp only [CollatzResearch.WordTrace]
  refine ⟨152759741307522748024435145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101839827538348498682956763 152759741307522748024435145)
  ·
    refine ⟨114569805980642061018326359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152759741307522748024435145 114569805980642061018326359)
    ·
      refine ⟨171854708970963091527489539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114569805980642061018326359 171854708970963091527489539)
      ·
        refine ⟨257782063456444637291234309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171854708970963091527489539 257782063456444637291234309)
        ·
          refine ⟨48334136898083369492106433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257782063456444637291234309 48334136898083369492106433)
          ·
            refine ⟨36250602673562527119079825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48334136898083369492106433 36250602673562527119079825)
            ·
              refine ⟨27187952005171895339309869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36250602673562527119079825 27187952005171895339309869)
              ·
                refine ⟨10195482001939460752241201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27187952005171895339309869 10195482001939460752241201)
                ·
                  refine ⟨7646611501454595564180901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10195482001939460752241201 7646611501454595564180901)
                  ·
                    refine ⟨1433739656522736668283919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7646611501454595564180901 1433739656522736668283919)
                    ·
                      rfl

theorem cell22_4188297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_4188297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188297 prefixEnd_4188297 := by exact prefixLift 4188297
  have htrace : WordTrace (prefixWord ++ tailWord_4188297) baseStart_4188297 baseEnd_4188297 := by
    simpa [prefixWord, tailWord_4188297, baseEnd_4188297] using wordTrace_append hprefix tailTrace_4188297
  have hstable : (prefixWord ++ tailWord_4188297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188297).length < 2 ^ (prefixWord ++ tailWord_4188297).sum := by decide
  have hdescent : baseEnd_4188297 < baseStart_4188297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188318 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_4188318 : Nat := 118140960795 + 4188318 * 2 ^ 59
def prefixEnd_4188318 : Nat := 4983230072969 + 3 ^ 40 * 4188318 * 2
def baseEnd_4188318 : Nat := 477915615083966537836285

theorem tailTrace_4188318 : CollatzResearch.WordTrace tailWord_4188318 prefixEnd_4188318 477915615083966537836285 := by
  unfold tailWord_4188318
  simp only [CollatzResearch.WordTrace]
  refine ⟨19095063405055833576368701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101840338160297779073966405 19095063405055833576368701)
  ·
    refine ⟨7160648776895937591138263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19095063405055833576368701 7160648776895937591138263)
    ·
      refine ⟨10740973165343906386707395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7160648776895937591138263 10740973165343906386707395)
      ·
        refine ⟨16111459748015859580061093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10740973165343906386707395 16111459748015859580061093)
        ·
          refine ⟨3020898702752973671261455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16111459748015859580061093 3020898702752973671261455)
          ·
            refine ⟨4531348054129460506892183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3020898702752973671261455 4531348054129460506892183)
            ·
              refine ⟨6797022081194190760338275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4531348054129460506892183 6797022081194190760338275)
              ·
                refine ⟨10195533121791286140507413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6797022081194190760338275 10195533121791286140507413)
                ·
                  refine ⟨477915615083966537836285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10195533121791286140507413 477915615083966537836285)
                  ·
                    rfl

theorem cell22_4188318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_4188318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188318 prefixEnd_4188318 := by exact prefixLift 4188318
  have htrace : WordTrace (prefixWord ++ tailWord_4188318) baseStart_4188318 baseEnd_4188318 := by
    simpa [prefixWord, tailWord_4188318, baseEnd_4188318] using wordTrace_append hprefix tailTrace_4188318
  have hstable : (prefixWord ++ tailWord_4188318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188318).length < 2 ^ (prefixWord ++ tailWord_4188318).sum := by decide
  have hdescent : baseEnd_4188318 < baseStart_4188318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188333 : List Nat := [1, 5, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_4188333 : Nat := 118140960795 + 4188333 * 2 ^ 59
def prefixEnd_4188333 : Nat := 4983230072969 + 3 ^ 40 * 4188333 * 2
def baseEnd_4188333 : Nat := 1433751980058444574383809

theorem tailTrace_4188333 : CollatzResearch.WordTrace tailWord_4188333 prefixEnd_4188333 1433751980058444574383809 := by
  unfold tailWord_4188333
  simp only [CollatzResearch.WordTrace]
  refine ⟨152761054335392326172745653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101840702890261550781830435 152761054335392326172745653)
  ·
    refine ⟨14321348843943030578694905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152761054335392326172745653 14321348843943030578694905)
    ·
      refine ⟨10741011632957272934021179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14321348843943030578694905 10741011632957272934021179)
      ·
        refine ⟨16111517449435909401031769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10741011632957272934021179 16111517449435909401031769)
        ·
          refine ⟨12083638087076932050773827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16111517449435909401031769 12083638087076932050773827)
          ·
            refine ⟨18125457130615398076160741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12083638087076932050773827 18125457130615398076160741)
            ·
              refine ⟨3398523211990387139280139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18125457130615398076160741 3398523211990387139280139)
              ·
                refine ⟨5097784817985580708920209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3398523211990387139280139 5097784817985580708920209)
                ·
                  refine ⟨3823338613489185531690157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5097784817985580708920209 3823338613489185531690157)
                  ·
                    refine ⟨1433751980058444574383809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3823338613489185531690157 1433751980058444574383809)
                    ·
                      rfl

theorem cell22_4188333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_4188333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188333 prefixEnd_4188333 := by exact prefixLift 4188333
  have htrace : WordTrace (prefixWord ++ tailWord_4188333) baseStart_4188333 baseEnd_4188333 := by
    simpa [prefixWord, tailWord_4188333, baseEnd_4188333] using wordTrace_append hprefix tailTrace_4188333
  have hstable : (prefixWord ++ tailWord_4188333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188333).length < 2 ^ (prefixWord ++ tailWord_4188333).sum := by decide
  have hdescent : baseEnd_4188333 < baseStart_4188333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188378 : List Nat := [3, 1, 1, 2, 2, 1, 6, 2, 1, 3]
def baseStart_4188378 : Nat := 118140960795 + 4188378 * 2 ^ 59
def prefixEnd_4188378 : Nat := 4983230072969 + 3 ^ 40 * 4188378 * 2
def baseEnd_4188378 : Nat := 1433767384478079457008671

theorem tailTrace_4188378 : CollatzResearch.WordTrace tailWord_4188378 prefixEnd_4188378 1433767384478079457008671 := by
  unfold tailWord_4188378
  simp only [CollatzResearch.WordTrace]
  refine ⟨38190673905057324714533447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101841797080152865905422525 38190673905057324714533447)
  ·
    refine ⟨57286010857585987071800171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38190673905057324714533447 57286010857585987071800171)
    ·
      refine ⟨85929016286378980607700257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57286010857585987071800171 85929016286378980607700257)
      ·
        refine ⟨64446762214784235455775193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85929016286378980607700257 64446762214784235455775193)
        ·
          refine ⟨48335071661088176591831395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64446762214784235455775193 48335071661088176591831395)
          ·
            refine ⟨72502607491632264887747093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48335071661088176591831395 72502607491632264887747093)
            ·
              refine ⟨3398559726170262416613145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72502607491632264887747093 3398559726170262416613145)
              ·
                refine ⟨2548919794627696812459859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3398559726170262416613145 2548919794627696812459859)
                ·
                  refine ⟨3823379691941545218689789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2548919794627696812459859 3823379691941545218689789)
                  ·
                    refine ⟨1433767384478079457008671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3823379691941545218689789 1433767384478079457008671)
                    ·
                      rfl

theorem cell22_4188378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_4188378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188378 prefixEnd_4188378 := by exact prefixLift 4188378
  have htrace : WordTrace (prefixWord ++ tailWord_4188378) baseStart_4188378 baseEnd_4188378 := by
    simpa [prefixWord, tailWord_4188378, baseEnd_4188378] using wordTrace_append hprefix tailTrace_4188378
  have hstable : (prefixWord ++ tailWord_4188378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188378).length < 2 ^ (prefixWord ++ tailWord_4188378).sum := by decide
  have hdescent : baseEnd_4188378 < baseStart_4188378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188389 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_4188389 : Nat := 118140960795 + 4188389 * 2 ^ 59
def prefixEnd_4188389 : Nat := 4983230072969 + 3 ^ 40 * 4188389 * 2
def baseEnd_4188389 : Nat := 1433771150002879094983637

theorem tailTrace_4188389 : CollatzResearch.WordTrace tailWord_4188389 prefixEnd_4188389 1433771150002879094983637 := by
  unfold tailWord_4188389
  simp only [CollatzResearch.WordTrace]
  refine ⟨152763096823189447736784221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101842064548792965157856147 152763096823189447736784221)
  ·
    refine ⟨57286161308696042901294083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152763096823189447736784221 57286161308696042901294083)
    ·
      refine ⟨85929241963044064351941125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57286161308696042901294083 85929241963044064351941125)
      ·
        refine ⟨16111732868070762065988961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85929241963044064351941125 16111732868070762065988961)
        ·
          refine ⟨12083799651053071549491721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16111732868070762065988961 12083799651053071549491721)
          ·
            refine ⟨9062849738289803662118791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12083799651053071549491721 9062849738289803662118791)
            ·
              refine ⟨13594274607434705493178187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9062849738289803662118791 13594274607434705493178187)
              ·
                refine ⟨20391411911152058239767281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13594274607434705493178187 20391411911152058239767281)
                ·
                  refine ⟨15293558933364043679825461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20391411911152058239767281 15293558933364043679825461)
                  ·
                    refine ⟨1433771150002879094983637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15293558933364043679825461 1433771150002879094983637)
                    ·
                      rfl

theorem cell22_4188389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_4188389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188389 prefixEnd_4188389 := by exact prefixLift 4188389
  have htrace : WordTrace (prefixWord ++ tailWord_4188389) baseStart_4188389 baseEnd_4188389 := by
    simpa [prefixWord, tailWord_4188389, baseEnd_4188389] using wordTrace_append hprefix tailTrace_4188389
  have hstable : (prefixWord ++ tailWord_4188389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188389).length < 2 ^ (prefixWord ++ tailWord_4188389).sum := by decide
  have hdescent : baseEnd_4188389 < baseStart_4188389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188481 : List Nat := [1, 2, 5, 2, 2, 2, 8]
def baseStart_4188481 : Nat := 118140960795 + 4188481 * 2 ^ 59
def prefixEnd_4188481 : Nat := 4983230072969 + 3 ^ 40 * 4188481 * 2
def baseEnd_4188481 : Nat := 53103801610482278580865

theorem tailTrace_4188481 : CollatzResearch.WordTrace tailWord_4188481 prefixEnd_4188481 53103801610482278580865 := by
  unfold tailWord_4188481
  simp only [CollatzResearch.WordTrace]
  refine ⟨152766452338856147449133297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101844301559237431632755531 152766452338856147449133297)
  ·
    refine ⟨114574839254142110586849973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152766452338856147449133297 114574839254142110586849973)
    ·
      refine ⟨10741391180075822867517185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114574839254142110586849973 10741391180075822867517185)
      ·
        refine ⟨8056043385056867150637889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10741391180075822867517185 8056043385056867150637889)
        ·
          refine ⟨6042032538792650362978417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8056043385056867150637889 6042032538792650362978417)
          ·
            refine ⟨4531524404094487772233813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6042032538792650362978417 4531524404094487772233813)
            ·
              refine ⟨53103801610482278580865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4531524404094487772233813 53103801610482278580865)
              ·
                rfl

theorem cell22_4188481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 8].length) (baseStart_4188481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188481 prefixEnd_4188481 := by exact prefixLift 4188481
  have htrace : WordTrace (prefixWord ++ tailWord_4188481) baseStart_4188481 baseEnd_4188481 := by
    simpa [prefixWord, tailWord_4188481, baseEnd_4188481] using wordTrace_append hprefix tailTrace_4188481
  have hstable : (prefixWord ++ tailWord_4188481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188481).length < 2 ^ (prefixWord ++ tailWord_4188481).sum := by decide
  have hdescent : baseEnd_4188481 < baseStart_4188481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188496 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 3, 3]
def baseStart_4188496 : Nat := 118140960795 + 4188496 * 2 ^ 59
def prefixEnd_4188496 : Nat := 4983230072969 + 3 ^ 40 * 4188496 * 2
def baseEnd_4188496 : Nat := 1433807778289566482558309

theorem tailTrace_4188496 : CollatzResearch.WordTrace tailWord_4188496 prefixEnd_4188496 1433807778289566482558309 := by
  unfold tailWord_4188496
  simp only [CollatzResearch.WordTrace]
  refine ⟨76383499716900902505464671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101844666289201203340619561 76383499716900902505464671)
  ·
    refine ⟨114575249575351353758197007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76383499716900902505464671 114575249575351353758197007)
    ·
      refine ⟨171862874363027030637295511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114575249575351353758197007 171862874363027030637295511)
      ·
        refine ⟨257794311544540545955943267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171862874363027030637295511 257794311544540545955943267)
        ·
          refine ⟨386691467316810818933914901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257794311544540545955943267 386691467316810818933914901)
          ·
            refine ⟨18126162530475507137527261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 386691467316810818933914901 18126162530475507137527261)
            ·
              refine ⟨6797310948928315176572723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18126162530475507137527261 6797310948928315176572723)
              ·
                refine ⟨10195966423392472764859085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6797310948928315176572723 10195966423392472764859085)
                ·
                  refine ⟨3823487408772177286822157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10195966423392472764859085 3823487408772177286822157)
                  ·
                    refine ⟨1433807778289566482558309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3823487408772177286822157 1433807778289566482558309)
                    ·
                      rfl

theorem cell22_4188496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 3, 3].length) (baseStart_4188496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188496 prefixEnd_4188496 := by exact prefixLift 4188496
  have htrace : WordTrace (prefixWord ++ tailWord_4188496) baseStart_4188496 baseEnd_4188496 := by
    simpa [prefixWord, tailWord_4188496, baseEnd_4188496] using wordTrace_append hprefix tailTrace_4188496
  have hstable : (prefixWord ++ tailWord_4188496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188496).length < 2 ^ (prefixWord ++ tailWord_4188496).sum := by decide
  have hdescent : baseEnd_4188496 < baseStart_4188496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188547 : List Nat := [1, 1, 1, 3, 6, 2, 2, 2, 1, 3]
def baseStart_4188547 : Nat := 118140960795 + 4188547 * 2 ^ 59
def prefixEnd_4188547 : Nat := 4983230072969 + 3 ^ 40 * 4188547 * 2
def baseEnd_4188547 : Nat := 1433825236631819349533153

theorem tailTrace_4188547 : CollatzResearch.WordTrace tailWord_4188547 prefixEnd_4188547 1433825236631819349533153 := by
  unfold tailWord_4188547
  simp only [CollatzResearch.WordTrace]
  refine ⟨152768859556617040721035895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101845906371078027147357263 152768859556617040721035895)
  ·
    refine ⟨229153289334925561081553843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152768859556617040721035895 229153289334925561081553843)
    ·
      refine ⟨343729934002388341622330765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229153289334925561081553843 343729934002388341622330765)
      ·
        refine ⟨128898725250895628108374037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343729934002388341622330765 128898725250895628108374037)
        ·
          refine ⟨6042127746135732567580033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128898725250895628108374037 6042127746135732567580033)
          ·
            refine ⟨4531595809601799425685025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6042127746135732567580033 4531595809601799425685025)
            ·
              refine ⟨3398696857201349569263769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4531595809601799425685025 3398696857201349569263769)
              ·
                refine ⟨2549022642901012176947827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3398696857201349569263769 2549022642901012176947827)
                ·
                  refine ⟨3823533964351518265421741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549022642901012176947827 3823533964351518265421741)
                  ·
                    refine ⟨1433825236631819349533153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3823533964351518265421741 1433825236631819349533153)
                    ·
                      rfl

theorem cell22_4188547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 1, 3].length) (baseStart_4188547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188547 prefixEnd_4188547 := by exact prefixLift 4188547
  have htrace : WordTrace (prefixWord ++ tailWord_4188547) baseStart_4188547 baseEnd_4188547 := by
    simpa [prefixWord, tailWord_4188547, baseEnd_4188547] using wordTrace_append hprefix tailTrace_4188547
  have hstable : (prefixWord ++ tailWord_4188547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188547).length < 2 ^ (prefixWord ++ tailWord_4188547).sum := by decide
  have hdescent : baseEnd_4188547 < baseStart_4188547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188599 : List Nat := [1, 1, 3, 1, 3, 4, 9]
def baseStart_4188599 : Nat := 118140960795 + 4188599 * 2 ^ 59
def prefixEnd_4188599 : Nat := 4983230072969 + 3 ^ 40 * 4188599 * 2
def baseEnd_4188599 : Nat := 53105297677574390638259

theorem tailTrace_4188599 : CollatzResearch.WordTrace tailWord_4188599 prefixEnd_4188599 53105297677574390638259 := by
  unfold tailWord_4188599
  simp only [CollatzResearch.WordTrace]
  refine ⟨152770756152428653601928851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101847170768285769067952567 152770756152428653601928851)
  ·
    refine ⟨229156134228642980402893277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152770756152428653601928851 229156134228642980402893277)
    ·
      refine ⟨85933550335741117651084979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229156134228642980402893277 85933550335741117651084979)
      ·
        refine ⟨128900325503611676476627469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85933550335741117651084979 128900325503611676476627469)
        ·
          refine ⟨48337622063854378678735301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128900325503611676476627469 48337622063854378678735301)
          ·
            refine ⟨9063304136972696002262869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48337622063854378678735301 9063304136972696002262869)
            ·
              refine ⟨53105297677574390638259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9063304136972696002262869 53105297677574390638259)
              ·
                rfl

theorem cell22_4188599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 9].length) (baseStart_4188599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188599 prefixEnd_4188599 := by exact prefixLift 4188599
  have htrace : WordTrace (prefixWord ++ tailWord_4188599) baseStart_4188599 baseEnd_4188599 := by
    simpa [prefixWord, tailWord_4188599, baseEnd_4188599] using wordTrace_append hprefix tailTrace_4188599
  have hstable : (prefixWord ++ tailWord_4188599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188599).length < 2 ^ (prefixWord ++ tailWord_4188599).sum := by decide
  have hdescent : baseEnd_4188599 < baseStart_4188599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188620 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 1, 5]
def baseStart_4188620 : Nat := 118140960795 + 4188620 * 2 ^ 59
def prefixEnd_4188620 : Nat := 4983230072969 + 3 ^ 40 * 4188620 * 2
def baseEnd_4188620 : Nat := 1433850226023671492457929

theorem tailTrace_4188620 : CollatzResearch.WordTrace tailWord_4188620 prefixEnd_4188620 1433850226023671492457929 := by
  unfold tailWord_4188620
  simp only [CollatzResearch.WordTrace]
  refine ⟨76385761042676287094221657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101847681390235049458962209 76385761042676287094221657)
  ·
    refine ⟨57289320782007215320666243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76385761042676287094221657 57289320782007215320666243)
    ·
      refine ⟨85933981173010822980999365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57289320782007215320666243 85933981173010822980999365)
      ·
        refine ⟨16112621469939529308937381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85933981173010822980999365 16112621469939529308937381)
        ·
          refine ⟨3021116525613661745425759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16112621469939529308937381 3021116525613661745425759)
          ·
            refine ⟨4531674788420492618138639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3021116525613661745425759 4531674788420492618138639)
            ·
              refine ⟨6797512182630738927207959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4531674788420492618138639 6797512182630738927207959)
              ·
                refine ⟨10196268273946108390811939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6797512182630738927207959 10196268273946108390811939)
                ·
                  refine ⟨15294402410919162586217909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10196268273946108390811939 15294402410919162586217909)
                  ·
                    refine ⟨1433850226023671492457929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15294402410919162586217909 1433850226023671492457929)
                    ·
                      rfl

theorem cell22_4188620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_4188620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188620 prefixEnd_4188620 := by exact prefixLift 4188620
  have htrace : WordTrace (prefixWord ++ tailWord_4188620) baseStart_4188620 baseEnd_4188620 := by
    simpa [prefixWord, tailWord_4188620, baseEnd_4188620] using wordTrace_append hprefix tailTrace_4188620
  have hstable : (prefixWord ++ tailWord_4188620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188620).length < 2 ^ (prefixWord ++ tailWord_4188620).sum := by decide
  have hdescent : baseEnd_4188620 < baseStart_4188620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188691 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 3, 4]
def baseStart_4188691 : Nat := 118140960795 + 4188691 * 2 ^ 59
def prefixEnd_4188691 : Nat := 4983230072969 + 3 ^ 40 * 4188691 * 2
def baseEnd_4188691 : Nat := 1433874530774650973932711

theorem tailTrace_4188691 : CollatzResearch.WordTrace tailWord_4188691 prefixEnd_4188691 1433874530774650973932711 := by
  unfold tailWord_4188691
  simp only [CollatzResearch.WordTrace]
  refine ⟨152774111668095353314277927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101849407778730235542851951 152774111668095353314277927)
  ·
    refine ⟨229161167502143029971416891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152774111668095353314277927 229161167502143029971416891)
    ·
      refine ⟨343741751253214544957125337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229161167502143029971416891 343741751253214544957125337)
      ·
        refine ⟨257806313439910908717844003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343741751253214544957125337 257806313439910908717844003)
        ·
          refine ⟨386709470159866363076766005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257806313439910908717844003 386709470159866363076766005)
          ·
            refine ⟨36254012827487471538446813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 386709470159866363076766005 36254012827487471538446813)
            ·
              refine ⟨13595254810307801826917555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36254012827487471538446813 13595254810307801826917555)
              ·
                refine ⟨20392882215461702740376333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13595254810307801826917555 20392882215461702740376333)
                ·
                  refine ⟨7647330830798138527641125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20392882215461702740376333 7647330830798138527641125)
                  ·
                    refine ⟨1433874530774650973932711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7647330830798138527641125 1433874530774650973932711)
                    ·
                      rfl

theorem cell22_4188691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 4].length) (baseStart_4188691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188691 prefixEnd_4188691 := by exact prefixLift 4188691
  have htrace : WordTrace (prefixWord ++ tailWord_4188691) baseStart_4188691 baseEnd_4188691 := by
    simpa [prefixWord, tailWord_4188691, baseEnd_4188691] using wordTrace_append hprefix tailTrace_4188691
  have hstable : (prefixWord ++ tailWord_4188691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188691).length < 2 ^ (prefixWord ++ tailWord_4188691).sum := by decide
  have hdescent : baseEnd_4188691 < baseStart_4188691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188723 : List Nat := [1, 1, 1, 2, 4, 2, 3, 4, 4]
def baseStart_4188723 : Nat := 118140960795 + 4188723 * 2 ^ 59
def prefixEnd_4188723 : Nat := 4983230072969 + 3 ^ 40 * 4188723 * 2
def baseEnd_4188723 : Nat := 477961828342871185710871

theorem tailTrace_4188723 : CollatzResearch.WordTrace tailWord_4188723 prefixEnd_4188723 477961828342871185710871 := by
  unfold tailWord_4188723
  simp only [CollatzResearch.WordTrace]
  refine ⟨152775278803979422779442823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101850185869319615186295215 152775278803979422779442823)
  ·
    refine ⟨229162918205969134169164235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152775278803979422779442823 229162918205969134169164235)
    ·
      refine ⟨343744377308953701253746353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229162918205969134169164235 343744377308953701253746353)
      ·
        refine ⟨257808282981715275940309765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343744377308953701253746353 257808282981715275940309765)
        ·
          refine ⟨48339053059071614238808081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257808282981715275940309765 48339053059071614238808081)
          ·
            refine ⟨36254289794303710679106061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48339053059071614238808081 36254289794303710679106061)
            ·
              refine ⟨13595358672863891504664773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36254289794303710679106061 13595358672863891504664773)
              ·
                refine ⟨2549129751161979657124645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13595358672863891504664773 2549129751161979657124645)
                ·
                  refine ⟨477961828342871185710871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2549129751161979657124645 477961828342871185710871)
                  ·
                    rfl

theorem cell22_4188723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 4].length) (baseStart_4188723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188723 prefixEnd_4188723 := by exact prefixLift 4188723
  have htrace : WordTrace (prefixWord ++ tailWord_4188723) baseStart_4188723 baseEnd_4188723 := by
    simpa [prefixWord, tailWord_4188723, baseEnd_4188723] using wordTrace_append hprefix tailTrace_4188723
  have hstable : (prefixWord ++ tailWord_4188723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188723).length < 2 ^ (prefixWord ++ tailWord_4188723).sum := by decide
  have hdescent : baseEnd_4188723 < baseStart_4188723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188736 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 4, 4]
def baseStart_4188736 : Nat := 118140960795 + 4188736 * 2 ^ 59
def prefixEnd_4188736 : Nat := 4983230072969 + 3 ^ 40 * 4188736 * 2
def baseEnd_4188736 : Nat := 1433889935194285856557573

theorem tailTrace_4188736 : CollatzResearch.WordTrace tailWord_4188736 prefixEnd_4188736 1433889935194285856557573 := by
  unfold tailWord_4188736
  simp only [CollatzResearch.WordTrace]
  refine ⟨76387876476466162999833031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101850501968621550666444041 76387876476466162999833031)
  ·
    refine ⟨114581814714699244499749547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76387876476466162999833031 114581814714699244499749547)
    ·
      refine ⟨171872722072048866749624321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114581814714699244499749547 171872722072048866749624321)
      ·
        refine ⟨128904541554036650062218241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171872722072048866749624321 128904541554036650062218241)
        ·
          refine ⟨96678406165527487546663681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128904541554036650062218241 96678406165527487546663681)
          ·
            refine ⟨72508804624145615659997761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96678406165527487546663681 72508804624145615659997761)
            ·
              refine ⟨54381603468109211744998321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72508804624145615659997761 54381603468109211744998321)
              ·
                refine ⟨40786202601081908808748741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54381603468109211744998321 40786202601081908808748741)
                ·
                  refine ⟨7647412987702857901640389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40786202601081908808748741 7647412987702857901640389)
                  ·
                    refine ⟨1433889935194285856557573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7647412987702857901640389 1433889935194285856557573)
                    ·
                      rfl

theorem cell22_4188736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_4188736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188736 prefixEnd_4188736 := by exact prefixLift 4188736
  have htrace : WordTrace (prefixWord ++ tailWord_4188736) baseStart_4188736 baseEnd_4188736 := by
    simpa [prefixWord, tailWord_4188736, baseEnd_4188736] using wordTrace_append hprefix tailTrace_4188736
  have hstable : (prefixWord ++ tailWord_4188736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188736).length < 2 ^ (prefixWord ++ tailWord_4188736).sum := by decide
  have hdescent : baseEnd_4188736 < baseStart_4188736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188753 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 2, 4]
def baseStart_4188753 : Nat := 118140960795 + 4188753 * 2 ^ 59
def prefixEnd_4188753 : Nat := 4983230072969 + 3 ^ 40 * 4188753 * 2
def baseEnd_4188753 : Nat := 1433895754641703478882521

theorem tailTrace_4188753 : CollatzResearch.WordTrace tailWord_4188753 prefixEnd_4188753 1433895754641703478882521 := by
  unfold tailWord_4188753
  simp only [CollatzResearch.WordTrace]
  refine ⟨152776372993870737903034913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101850915329247158602023275 152776372993870737903034913)
  ·
    refine ⟨114582279745403053427276185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152776372993870737903034913 114582279745403053427276185)
    ·
      refine ⟨85936709809052290070457139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114582279745403053427276185 85936709809052290070457139)
      ·
        refine ⟨128905064713578435105685709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85936709809052290070457139 128905064713578435105685709)
        ·
          refine ⟨48339399267591913164632141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128905064713578435105685709 48339399267591913164632141)
          ·
            refine ⟨18127274725346967436737053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48339399267591913164632141 18127274725346967436737053)
            ·
              refine ⟨6797728022005112788776395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18127274725346967436737053 6797728022005112788776395)
              ·
                refine ⟨10196592033007669183164593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6797728022005112788776395 10196592033007669183164593)
                ·
                  refine ⟨7647444024755751887373445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10196592033007669183164593 7647444024755751887373445)
                  ·
                    refine ⟨1433895754641703478882521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7647444024755751887373445 1433895754641703478882521)
                    ·
                      rfl

theorem cell22_4188753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_4188753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188753 prefixEnd_4188753 := by exact prefixLift 4188753
  have htrace : WordTrace (prefixWord ++ tailWord_4188753) baseStart_4188753 baseEnd_4188753 := by
    simpa [prefixWord, tailWord_4188753, baseEnd_4188753] using wordTrace_append hprefix tailTrace_4188753
  have hstable : (prefixWord ++ tailWord_4188753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188753).length < 2 ^ (prefixWord ++ tailWord_4188753).sum := by decide
  have hdescent : baseEnd_4188753 < baseStart_4188753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188783 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 3, 3]
def baseStart_4188783 : Nat := 118140960795 + 4188783 * 2 ^ 59
def prefixEnd_4188783 : Nat := 4983230072969 + 3 ^ 40 * 4188783 * 2
def baseEnd_4188783 : Nat := 1433906024254793400632429

theorem tailTrace_4188783 : CollatzResearch.WordTrace tailWord_4188783 prefixEnd_4188783 1433906024254793400632429 := by
  unfold tailWord_4188783
  simp only [CollatzResearch.WordTrace]
  refine ⟨152777467183762053026627003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101851644789174702017751335 152777467183762053026627003)
  ·
    refine ⟨229166200775643079539940505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152777467183762053026627003 229166200775643079539940505)
    ·
      refine ⟨171874650581732309654955379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229166200775643079539940505 171874650581732309654955379)
      ·
        refine ⟨257811975872598464482433069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171874650581732309654955379 257811975872598464482433069)
        ·
          refine ⟨96679490952224424180912401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257811975872598464482433069 96679490952224424180912401)
          ·
            refine ⟨72509618214168318135684301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96679490952224424180912401 72509618214168318135684301)
            ·
              refine ⟨27191106830313119300881613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72509618214168318135684301 27191106830313119300881613)
              ·
                refine ⟨10196665061367419737830605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27191106830313119300881613 10196665061367419737830605)
                ·
                  refine ⟨3823749398012782401686477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10196665061367419737830605 3823749398012782401686477)
                  ·
                    refine ⟨1433906024254793400632429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3823749398012782401686477 1433906024254793400632429)
                    ·
                      rfl

theorem cell22_4188783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 3].length) (baseStart_4188783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188783 prefixEnd_4188783 := by exact prefixLift 4188783
  have htrace : WordTrace (prefixWord ++ tailWord_4188783) baseStart_4188783 baseEnd_4188783 := by
    simpa [prefixWord, tailWord_4188783, baseEnd_4188783] using wordTrace_append hprefix tailTrace_4188783
  have hstable : (prefixWord ++ tailWord_4188783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188783).length < 2 ^ (prefixWord ++ tailWord_4188783).sum := by decide
  have hdescent : baseEnd_4188783 < baseStart_4188783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188789 : List Nat := [1, 3, 4, 2, 2, 1, 3, 1, 2, 3]
def baseStart_4188789 : Nat := 118140960795 + 4188789 * 2 ^ 59
def prefixEnd_4188789 : Nat := 4983230072969 + 3 ^ 40 * 4188789 * 2
def baseEnd_4188789 : Nat := 1433908078177411384982411

theorem tailTrace_4188789 : CollatzResearch.WordTrace tailWord_4188789 prefixEnd_4188789 1433908078177411384982411 := by
  unfold tailWord_4188789
  simp only [CollatzResearch.WordTrace]
  refine ⟨152777686021740316051345421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101851790681160210700896947 152777686021740316051345421)
  ·
    refine ⟨57291632258152618519254533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152777686021740316051345421 57291632258152618519254533)
    ·
      refine ⟨10742181048403615972360225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57291632258152618519254533 10742181048403615972360225)
      ·
        refine ⟨8056635786302711979270169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10742181048403615972360225 8056635786302711979270169)
        ·
          refine ⟨6042476839727033984452627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8056635786302711979270169 6042476839727033984452627)
          ·
            refine ⟨9063715259590550976678941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042476839727033984452627 9063715259590550976678941)
            ·
              refine ⟨3398893222346456616254603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9063715259590550976678941 3398893222346456616254603)
              ·
                refine ⟨5098339833519684924381905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3398893222346456616254603 5098339833519684924381905)
                ·
                  refine ⟨3823754875139763693286429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5098339833519684924381905 3823754875139763693286429)
                  ·
                    refine ⟨1433908078177411384982411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3823754875139763693286429 1433908078177411384982411)
                    ·
                      rfl

theorem cell22_4188789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_4188789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188789 prefixEnd_4188789 := by exact prefixLift 4188789
  have htrace : WordTrace (prefixWord ++ tailWord_4188789) baseStart_4188789 baseEnd_4188789 := by
    simpa [prefixWord, tailWord_4188789, baseEnd_4188789] using wordTrace_append hprefix tailTrace_4188789
  have hstable : (prefixWord ++ tailWord_4188789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188789).length < 2 ^ (prefixWord ++ tailWord_4188789).sum := by decide
  have hdescent : baseEnd_4188789 < baseStart_4188789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188811 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 4, 5]
def baseStart_4188811 : Nat := 118140960795 + 4188811 * 2 ^ 59
def prefixEnd_4188811 : Nat := 4983230072969 + 3 ^ 40 * 4188811 * 2
def baseEnd_4188811 : Nat := 1433915609227010660932343

theorem tailTrace_4188811 : CollatzResearch.WordTrace tailWord_4188811 prefixEnd_4188811 1433915609227010660932343 := by
  unfold tailWord_4188811
  simp only [CollatzResearch.WordTrace]
  refine ⟨152778488427660613808646287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101852325618440409205764191 152778488427660613808646287)
  ·
    refine ⟨229167732641490920712969431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152778488427660613808646287 229167732641490920712969431)
    ·
      refine ⟨343751598962236381069454147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229167732641490920712969431 343751598962236381069454147)
      ·
        refine ⟨515627398443354571604181221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343751598962236381069454147 515627398443354571604181221)
        ·
          refine ⟨96680137208128982175783979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 515627398443354571604181221 96680137208128982175783979)
          ·
            refine ⟨145020205812193473263675969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96680137208128982175783979 145020205812193473263675969)
            ·
              refine ⟨108765154359145104947756977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145020205812193473263675969 108765154359145104947756977)
              ·
                refine ⟨81573865769358828710817733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108765154359145104947756977 81573865769358828710817733)
                ·
                  refine ⟨15295099831754780383278325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81573865769358828710817733 15295099831754780383278325)
                  ·
                    refine ⟨1433915609227010660932343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15295099831754780383278325 1433915609227010660932343)
                    ·
                      rfl

theorem cell22_4188811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 5].length) (baseStart_4188811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188811 prefixEnd_4188811 := by exact prefixLift 4188811
  have htrace : WordTrace (prefixWord ++ tailWord_4188811) baseStart_4188811 baseEnd_4188811 := by
    simpa [prefixWord, tailWord_4188811, baseEnd_4188811] using wordTrace_append hprefix tailTrace_4188811
  have hstable : (prefixWord ++ tailWord_4188811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188811).length < 2 ^ (prefixWord ++ tailWord_4188811).sum := by decide
  have hdescent : baseEnd_4188811 < baseStart_4188811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188830 : List Nat := [4, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_4188830 : Nat := 118140960795 + 4188830 * 2 ^ 59
def prefixEnd_4188830 : Nat := 4983230072969 + 3 ^ 40 * 4188830 * 2
def baseEnd_4188830 : Nat := 477974037771766981569095

theorem tailTrace_4188830 : CollatzResearch.WordTrace tailWord_4188830 prefixEnd_4188830 477974037771766981569095 := by
  unfold tailWord_4188830
  simp only [CollatzResearch.WordTrace]
  refine ⟨19097397676823972506698493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101852787609727853369058629 19097397676823972506698493)
  ·
    refine ⟨7161524128808989690011935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19097397676823972506698493 7161524128808989690011935)
    ·
      refine ⟨10742286193213484535017903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7161524128808989690011935 10742286193213484535017903)
      ·
        refine ⟨16113429289820226802526855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10742286193213484535017903 16113429289820226802526855)
        ·
          refine ⟨24170143934730340203790283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16113429289820226802526855 24170143934730340203790283)
          ·
            refine ⟨36255215902095510305685425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24170143934730340203790283 36255215902095510305685425)
            ·
              refine ⟨27191411926571632729264069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36255215902095510305685425 27191411926571632729264069)
              ·
                refine ⟨5098389736232181136737013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27191411926571632729264069 5098389736232181136737013)
                ·
                  refine ⟨477974037771766981569095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5098389736232181136737013 477974037771766981569095)
                  ·
                    rfl

theorem cell22_4188830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_4188830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188830 prefixEnd_4188830 := by exact prefixLift 4188830
  have htrace : WordTrace (prefixWord ++ tailWord_4188830) baseStart_4188830 baseEnd_4188830 := by
    simpa [prefixWord, tailWord_4188830, baseEnd_4188830] using wordTrace_append hprefix tailTrace_4188830
  have hstable : (prefixWord ++ tailWord_4188830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188830).length < 2 ^ (prefixWord ++ tailWord_4188830).sum := by decide
  have hdescent : baseEnd_4188830 < baseStart_4188830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188986 : List Nat := [3, 1, 1, 1, 6, 2, 1, 3, 1, 3]
def baseStart_4188986 : Nat := 118140960795 + 4188986 * 2 ^ 59
def prefixEnd_4188986 : Nat := 4983230072969 + 3 ^ 40 * 4188986 * 2
def baseEnd_4188986 : Nat := 1433975515303368537806807

theorem tailTrace_4188986 : CollatzResearch.WordTrace tailWord_4188986 prefixEnd_4188986 1433975515303368537806807 := by
  unfold tailWord_4188986
  simp only [CollatzResearch.WordTrace]
  refine ⟨38196217800506654674066703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101856580801351079130844541 38196217800506654674066703)
  ·
    refine ⟨57294326700759982011100055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38196217800506654674066703 57294326700759982011100055)
    ·
      refine ⟨85941490051139973016650083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57294326700759982011100055 85941490051139973016650083)
      ·
        refine ⟨128912235076709959524975125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85941490051139973016650083 128912235076709959524975125)
        ·
          refine ⟨6042761019220779352733209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128912235076709959524975125 6042761019220779352733209)
          ·
            refine ⟨4532070764415584514549907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6042761019220779352733209 4532070764415584514549907)
            ·
              refine ⟨6798106146623376771824861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4532070764415584514549907 6798106146623376771824861)
              ·
                refine ⟨2549289804983766289434323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6798106146623376771824861 2549289804983766289434323)
                ·
                  refine ⟨3823934707475649434151485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2549289804983766289434323 3823934707475649434151485)
                  ·
                    refine ⟨1433975515303368537806807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3823934707475649434151485 1433975515303368537806807)
                    ·
                      rfl

theorem cell22_4188986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_4188986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188986 prefixEnd_4188986 := by exact prefixLift 4188986
  have htrace : WordTrace (prefixWord ++ tailWord_4188986) baseStart_4188986 baseEnd_4188986 := by
    simpa [prefixWord, tailWord_4188986, baseEnd_4188986] using wordTrace_append hprefix tailTrace_4188986
  have hstable : (prefixWord ++ tailWord_4188986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188986).length < 2 ^ (prefixWord ++ tailWord_4188986).sum := by decide
  have hdescent : baseEnd_4188986 < baseStart_4188986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4188995 : List Nat := [1, 1, 1, 3, 1, 4, 1, 5, 1, 4]
def baseStart_4188995 : Nat := 118140960795 + 4188995 * 2 ^ 59
def prefixEnd_4188995 : Nat := 4983230072969 + 3 ^ 40 * 4188995 * 2
def baseEnd_4188995 : Nat := 1433978596187295514331779

theorem tailTrace_4188995 : CollatzResearch.WordTrace tailWord_4188995 prefixEnd_4188995 1433978596187295514331779 := by
  unfold tailWord_4188995
  simp only [CollatzResearch.WordTrace]
  refine ⟨152785199458994013233344439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101856799639329342155562959 152785199458994013233344439)
  ·
    refine ⟨229177799188491019850016659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152785199458994013233344439 229177799188491019850016659)
    ·
      refine ⟨343766698782736529775024989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229177799188491019850016659 343766698782736529775024989)
      ·
        refine ⟨128912512043526198665634371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343766698782736529775024989 128912512043526198665634371)
        ·
          refine ⟨193368768065289297998451557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128912512043526198665634371 193368768065289297998451557)
          ·
            refine ⟨36256644012241743374709667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193368768065289297998451557 36256644012241743374709667)
            ·
              refine ⟨54384966018362615062064501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36256644012241743374709667 54384966018362615062064501)
              ·
                refine ⟨5098590564221495162068547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54384966018362615062064501 5098590564221495162068547)
                ·
                  refine ⟨7647885846332242743102821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098590564221495162068547 7647885846332242743102821)
                  ·
                    refine ⟨1433978596187295514331779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7647885846332242743102821 1433978596187295514331779)
                    ·
                      rfl

theorem cell22_4188995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 4].length) (baseStart_4188995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4188995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4188995 prefixEnd_4188995 := by exact prefixLift 4188995
  have htrace : WordTrace (prefixWord ++ tailWord_4188995) baseStart_4188995 baseEnd_4188995 := by
    simpa [prefixWord, tailWord_4188995, baseEnd_4188995] using wordTrace_append hprefix tailTrace_4188995
  have hstable : (prefixWord ++ tailWord_4188995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4188995).length < 2 ^ (prefixWord ++ tailWord_4188995).sum := by decide
  have hdescent : baseEnd_4188995 < baseStart_4188995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4188995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189025 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 6, 3]
def baseStart_4189025 : Nat := 118140960795 + 4189025 * 2 ^ 59
def prefixEnd_4189025 : Nat := 4983230072969 + 3 ^ 40 * 4189025 * 2
def baseEnd_4189025 : Nat := 1433988865800385436081687

theorem tailTrace_4189025 : CollatzResearch.WordTrace tailWord_4189025 prefixEnd_4189025 1433988865800385436081687 := by
  unfold tailWord_4189025
  simp only [CollatzResearch.WordTrace]
  refine ⟨152786293648885328356936529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101857529099256885571291019 152786293648885328356936529)
  ·
    refine ⟨114589720236663996267702397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152786293648885328356936529 114589720236663996267702397)
    ·
      refine ⟨42971145088748998600388399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114589720236663996267702397 42971145088748998600388399)
      ·
        refine ⟨64456717633123497900582599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42971145088748998600388399 64456717633123497900582599)
        ·
          refine ⟨96685076449685246850873899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64456717633123497900582599 96685076449685246850873899)
          ·
            refine ⟨145027614674527870276310849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96685076449685246850873899 145027614674527870276310849)
            ·
              refine ⟨108770711005895902707233137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145027614674527870276310849 108770711005895902707233137)
              ·
                refine ⟨81578033254421927030424853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108770711005895902707233137 81578033254421927030424853)
                ·
                  refine ⟨3823970308801027829551165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81578033254421927030424853 3823970308801027829551165)
                  ·
                    refine ⟨1433988865800385436081687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3823970308801027829551165 1433988865800385436081687)
                    ·
                      rfl

theorem cell22_4189025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_4189025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189025 prefixEnd_4189025 := by exact prefixLift 4189025
  have htrace : WordTrace (prefixWord ++ tailWord_4189025) baseStart_4189025 baseEnd_4189025 := by
    simpa [prefixWord, tailWord_4189025, baseEnd_4189025] using wordTrace_append hprefix tailTrace_4189025
  have hstable : (prefixWord ++ tailWord_4189025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189025).length < 2 ^ (prefixWord ++ tailWord_4189025).sum := by decide
  have hdescent : baseEnd_4189025 < baseStart_4189025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189040 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 2, 4]
def baseStart_4189040 : Nat := 118140960795 + 4189040 * 2 ^ 59
def prefixEnd_4189040 : Nat := 4983230072969 + 3 ^ 40 * 4189040 * 2
def baseEnd_4189040 : Nat := 1433994000606930396956641

theorem tailTrace_4189040 : CollatzResearch.WordTrace tailWord_4189040 prefixEnd_4189040 1433994000606930396956641 := by
  unfold tailWord_4189040
  simp only [CollatzResearch.WordTrace]
  refine ⟨76393420371915492959366287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101857893829220657279155049 76393420371915492959366287)
  ·
    refine ⟨114590130557873239439049431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76393420371915492959366287 114590130557873239439049431)
    ·
      refine ⟨171885195836809859158574147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114590130557873239439049431 171885195836809859158574147)
      ·
        refine ⟨257827793755214788737861221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171885195836809859158574147 257827793755214788737861221)
        ·
          refine ⟨48342711329102772888348979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257827793755214788737861221 48342711329102772888348979)
          ·
            refine ⟨72514066993654159332523469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48342711329102772888348979 72514066993654159332523469)
            ·
              refine ⟨27192775122620309749696301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72514066993654159332523469 27192775122620309749696301)
              ·
                refine ⟨10197290670982616156136113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27192775122620309749696301 10197290670982616156136113)
                ·
                  refine ⟨7647968003236962117102085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10197290670982616156136113 7647968003236962117102085)
                  ·
                    refine ⟨1433994000606930396956641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7647968003236962117102085 1433994000606930396956641)
                    ·
                      rfl

theorem cell22_4189040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_4189040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189040 prefixEnd_4189040 := by exact prefixLift 4189040
  have htrace : WordTrace (prefixWord ++ tailWord_4189040) baseStart_4189040 baseEnd_4189040 := by
    simpa [prefixWord, tailWord_4189040, baseEnd_4189040] using wordTrace_append hprefix tailTrace_4189040
  have hstable : (prefixWord ++ tailWord_4189040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189040).length < 2 ^ (prefixWord ++ tailWord_4189040).sum := by decide
  have hdescent : baseEnd_4189040 < baseStart_4189040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189046 : List Nat := [5, 1, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_4189046 : Nat := 118140960795 + 4189046 * 2 ^ 59
def prefixEnd_4189046 : Nat := 4983230072969 + 3 ^ 40 * 4189046 * 2
def baseEnd_4189046 : Nat := 1433996054529548381306623

theorem tailTrace_4189046 : CollatzResearch.WordTrace tailWord_4189046 prefixEnd_4189046 1433996054529548381306623 := by
  unfold tailWord_4189046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9549191223863078058965687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101858039721206165962300661 9549191223863078058965687)
  ·
    refine ⟨14323786835794617088448531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9549191223863078058965687 14323786835794617088448531)
    ·
      refine ⟨21485680253691925632672797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14323786835794617088448531 21485680253691925632672797)
      ·
        refine ⟨8057130095134472112252299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21485680253691925632672797 8057130095134472112252299)
        ·
          refine ⟨12085695142701708168378449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8057130095134472112252299 12085695142701708168378449)
          ·
            refine ⟨9064271357026281126283837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12085695142701708168378449 9064271357026281126283837)
            ·
              refine ⟨3399101758884855422356439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9064271357026281126283837 3399101758884855422356439)
              ·
                refine ⟨5098652638327283133534659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399101758884855422356439 5098652638327283133534659)
                ·
                  refine ⟨7647978957490924700301989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5098652638327283133534659 7647978957490924700301989)
                  ·
                    refine ⟨1433996054529548381306623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7647978957490924700301989 1433996054529548381306623)
                    ·
                      rfl

theorem cell22_4189046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_4189046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189046 prefixEnd_4189046 := by exact prefixLift 4189046
  have htrace : WordTrace (prefixWord ++ tailWord_4189046) baseStart_4189046 baseEnd_4189046 := by
    simpa [prefixWord, tailWord_4189046, baseEnd_4189046] using wordTrace_append hprefix tailTrace_4189046
  have hstable : (prefixWord ++ tailWord_4189046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189046).length < 2 ^ (prefixWord ++ tailWord_4189046).sum := by decide
  have hdescent : baseEnd_4189046 < baseStart_4189046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189085 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_4189085 : Nat := 118140960795 + 4189085 * 2 ^ 59
def prefixEnd_4189085 : Nat := 4983230072969 + 3 ^ 40 * 4189085 * 2
def baseEnd_4189085 : Nat := 1434009405026565279581503

theorem tailTrace_4189085 : CollatzResearch.WordTrace tailWord_4189085 prefixEnd_4189085 1434009405026565279581503 := by
  unfold tailWord_4189085
  simp only [CollatzResearch.WordTrace]
  refine ⟨152788482028667958604120709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101858988019111972402747139 152788482028667958604120709)
  ·
    refine ⟨28647840380375242238272633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152788482028667958604120709 28647840380375242238272633)
    ·
      refine ⟨21485880285281431678704475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28647840380375242238272633 21485880285281431678704475)
      ·
        refine ⟨32228820427922147518056713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21485880285281431678704475 32228820427922147518056713)
        ·
          refine ⟨24171615320941610638542535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32228820427922147518056713 24171615320941610638542535)
          ·
            refine ⟨36257422981412415957813803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24171615320941610638542535 36257422981412415957813803)
            ·
              refine ⟨54386134472118623936720705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36257422981412415957813803 54386134472118623936720705)
              ·
                refine ⟨40789600854088967952540529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54386134472118623936720705 40789600854088967952540529)
                ·
                  refine ⟨30592200640566725964405397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40789600854088967952540529 30592200640566725964405397)
                  ·
                    refine ⟨1434009405026565279581503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30592200640566725964405397 1434009405026565279581503)
                    ·
                      rfl

theorem cell22_4189085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_4189085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189085 prefixEnd_4189085 := by exact prefixLift 4189085
  have htrace : WordTrace (prefixWord ++ tailWord_4189085) baseStart_4189085 baseEnd_4189085 := by
    simpa [prefixWord, tailWord_4189085, baseEnd_4189085] using wordTrace_append hprefix tailTrace_4189085
  have hstable : (prefixWord ++ tailWord_4189085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189085).length < 2 ^ (prefixWord ++ tailWord_4189085).sum := by decide
  have hdescent : baseEnd_4189085 < baseStart_4189085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189087 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 5, 3]
def baseStart_4189087 : Nat := 118140960795 + 4189087 * 2 ^ 59
def prefixEnd_4189087 : Nat := 4983230072969 + 3 ^ 40 * 4189087 * 2
def baseEnd_4189087 : Nat := 1434010089667437941031497

theorem tailTrace_4189087 : CollatzResearch.WordTrace tailWord_4189087 prefixEnd_4189087 1434010089667437941031497 := by
  unfold tailWord_4189087
  simp only [CollatzResearch.WordTrace]
  refine ⟨152788554974660712945693515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101859036649773808630462343 152788554974660712945693515)
  ·
    refine ⟨229182832461991069418540273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152788554974660712945693515 229182832461991069418540273)
    ·
      refine ⟨171887124346493302063905205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229182832461991069418540273 171887124346493302063905205)
      ·
        refine ⟨16114417907483747068491113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171887124346493302063905205 16114417907483747068491113)
        ·
          refine ⟨12085813430612810301368335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16114417907483747068491113 12085813430612810301368335)
          ·
            refine ⟨18128720145919215452052503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12085813430612810301368335 18128720145919215452052503)
            ·
              refine ⟨27193080218878823178078755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18128720145919215452052503 27193080218878823178078755)
              ·
                refine ⟨40789620328318234767118133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27193080218878823178078755 40789620328318234767118133)
                ·
                  refine ⟨3824026905779834509417325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40789620328318234767118133 3824026905779834509417325)
                  ·
                    refine ⟨1434010089667437941031497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3824026905779834509417325 1434010089667437941031497)
                    ·
                      rfl

theorem cell22_4189087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 3].length) (baseStart_4189087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189087 prefixEnd_4189087 := by exact prefixLift 4189087
  have htrace : WordTrace (prefixWord ++ tailWord_4189087) baseStart_4189087 baseEnd_4189087 := by
    simpa [prefixWord, tailWord_4189087, baseEnd_4189087] using wordTrace_append hprefix tailTrace_4189087
  have hstable : (prefixWord ++ tailWord_4189087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189087).length < 2 ^ (prefixWord ++ tailWord_4189087).sum := by decide
  have hdescent : baseEnd_4189087 < baseStart_4189087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189117 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 7]
def baseStart_4189117 : Nat := 118140960795 + 4189117 * 2 ^ 59
def prefixEnd_4189117 : Nat := 4983230072969 + 3 ^ 40 * 4189117 * 2
def baseEnd_4189117 : Nat := 478006786426842620927135

theorem tailTrace_4189117 : CollatzResearch.WordTrace tailWord_4189117 prefixEnd_4189117 478006786426842620927135 := by
  unfold tailWord_4189117
  simp only [CollatzResearch.WordTrace]
  refine ⟨152789649164552028069285605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101859766109701352046190403 152789649164552028069285605)
  ·
    refine ⟨28648059218353505262991051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152789649164552028069285605 28648059218353505262991051)
    ·
      refine ⟨42972088827530257894486577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28648059218353505262991051 42972088827530257894486577)
      ·
        refine ⟨32229066620647693420864933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42972088827530257894486577 32229066620647693420864933)
        ·
          refine ⟨6042949991371442516412175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32229066620647693420864933 6042949991371442516412175)
          ·
            refine ⟨9064424987057163774618263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6042949991371442516412175 9064424987057163774618263)
            ·
              refine ⟨13596637480585745661927395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9064424987057163774618263 13596637480585745661927395)
              ·
                refine ⟨20394956220878618492891093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13596637480585745661927395 20394956220878618492891093)
                ·
                  refine ⟨478006786426842620927135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20394956220878618492891093 478006786426842620927135)
                  ·
                    rfl

theorem cell22_4189117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_4189117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189117 prefixEnd_4189117 := by exact prefixLift 4189117
  have htrace : WordTrace (prefixWord ++ tailWord_4189117) baseStart_4189117 baseEnd_4189117 := by
    simpa [prefixWord, tailWord_4189117, baseEnd_4189117] using wordTrace_append hprefix tailTrace_4189117
  have hstable : (prefixWord ++ tailWord_4189117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189117).length < 2 ^ (prefixWord ++ tailWord_4189117).sum := by decide
  have hdescent : baseEnd_4189117 < baseStart_4189117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189134 : List Nat := [4, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_4189134 : Nat := 118140960795 + 4189134 * 2 ^ 59
def prefixEnd_4189134 : Nat := 4983230072969 + 3 ^ 40 * 4189134 * 2
def baseEnd_4189134 : Nat := 478008726242648495035451

theorem tailTrace_4189134 : CollatzResearch.WordTrace tailWord_4189134 prefixEnd_4189134 478008726242648495035451 := by
  unfold tailWord_4189134
  simp only [CollatzResearch.WordTrace]
  refine ⟨19098783650686304996581807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101860179470326959981769637 19098783650686304996581807)
  ·
    refine ⟨28648175476029457494872711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19098783650686304996581807 28648175476029457494872711)
    ·
      refine ⟨42972263214044186242309067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28648175476029457494872711 42972263214044186242309067)
      ·
        refine ⟨64458394821066279363463601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42972263214044186242309067 64458394821066279363463601)
        ·
          refine ⟨48343796115799709522597701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64458394821066279363463601 48343796115799709522597701)
          ·
            refine ⟨9064461771712445535487069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48343796115799709522597701 9064461771712445535487069)
            ·
              refine ⟨3399173164392167075807651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9064461771712445535487069 3399173164392167075807651)
              ·
                refine ⟨5098759746588250613711477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3399173164392167075807651 5098759746588250613711477)
                ·
                  refine ⟨478008726242648495035451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5098759746588250613711477 478008726242648495035451)
                  ·
                    rfl

theorem cell22_4189134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_4189134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189134 prefixEnd_4189134 := by exact prefixLift 4189134
  have htrace : WordTrace (prefixWord ++ tailWord_4189134) baseStart_4189134 baseEnd_4189134 := by
    simpa [prefixWord, tailWord_4189134, baseEnd_4189134] using wordTrace_append hprefix tailTrace_4189134
  have hstable : (prefixWord ++ tailWord_4189134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189134).length < 2 ^ (prefixWord ++ tailWord_4189134).sum := by decide
  have hdescent : baseEnd_4189134 < baseStart_4189134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189172 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_4189172 : Nat := 118140960795 + 4189172 * 2 ^ 59
def prefixEnd_4189172 : Nat := 4983230072969 + 3 ^ 40 * 4189172 * 2
def baseEnd_4189172 : Nat := 1434039186904526052656237

theorem tailTrace_4189172 : CollatzResearch.WordTrace tailWord_4189172 prefixEnd_4189172 1434039186904526052656237 := by
  unfold tailWord_4189172
  simp only [CollatzResearch.WordTrace]
  refine ⟨76395827589676386231268885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101861103452901848308358513 76395827589676386231268885)
  ·
    refine ⟨3581054418266080604590729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76395827589676386231268885 3581054418266080604590729)
    ·
      refine ⟨2685790813699560453443047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3581054418266080604590729 2685790813699560453443047)
      ·
        refine ⟨4028686220549340680164571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2685790813699560453443047 4028686220549340680164571)
        ·
          refine ⟨6043029330824011020246857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4028686220549340680164571 6043029330824011020246857)
          ·
            refine ⟨4532271998118008265185143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6043029330824011020246857 4532271998118008265185143)
            ·
              refine ⟨6798407997177012397777715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4532271998118008265185143 6798407997177012397777715)
              ·
                refine ⟨10197611995765518596666573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6798407997177012397777715 10197611995765518596666573)
                ·
                  refine ⟨3824104498412069473749965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10197611995765518596666573 3824104498412069473749965)
                  ·
                    refine ⟨1434039186904526052656237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3824104498412069473749965 1434039186904526052656237)
                    ·
                      rfl

theorem cell22_4189172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_4189172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189172 prefixEnd_4189172 := by exact prefixLift 4189172
  have htrace : WordTrace (prefixWord ++ tailWord_4189172) baseStart_4189172 baseEnd_4189172 := by
    simpa [prefixWord, tailWord_4189172, baseEnd_4189172] using wordTrace_append hprefix tailTrace_4189172
  have hstable : (prefixWord ++ tailWord_4189172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189172).length < 2 ^ (prefixWord ++ tailWord_4189172).sum := by decide
  have hdescent : baseEnd_4189172 < baseStart_4189172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4189177 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 4, 3]
def baseStart_4189177 : Nat := 118140960795 + 4189177 * 2 ^ 59
def prefixEnd_4189177 : Nat := 4983230072969 + 3 ^ 40 * 4189177 * 2
def baseEnd_4189177 : Nat := 1434040898506707706281221

theorem tailTrace_4189177 : CollatzResearch.WordTrace tailWord_4189177 prefixEnd_4189177 1434040898506707706281221 := by
  unfold tailWord_4189177
  simp only [CollatzResearch.WordTrace]
  refine ⟨152791837544334658316469785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101861225029556438877646523 152791837544334658316469785)
  ·
    refine ⟨114593878158250993737352339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152791837544334658316469785 114593878158250993737352339)
    ·
      refine ⟨171890817237376490606028509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114593878158250993737352339 171890817237376490606028509)
      ·
        refine ⟨64459056464016183977260691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171890817237376490606028509 64459056464016183977260691)
        ·
          refine ⟨96688584696024275965891037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64459056464016183977260691 96688584696024275965891037)
          ·
            refine ⟨36258219261009103487209139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96688584696024275965891037 36258219261009103487209139)
            ·
              refine ⟨54387328891513655230813709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36258219261009103487209139 54387328891513655230813709)
              ·
                refine ⟨20395248334317620711555141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54387328891513655230813709 20395248334317620711555141)
                ·
                  refine ⟨3824109062684553883416589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20395248334317620711555141 3824109062684553883416589)
                  ·
                    refine ⟨1434040898506707706281221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3824109062684553883416589 1434040898506707706281221)
                    ·
                      rfl

theorem cell22_4189177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 3].length) (baseStart_4189177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4189177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4189177 prefixEnd_4189177 := by exact prefixLift 4189177
  have htrace : WordTrace (prefixWord ++ tailWord_4189177) baseStart_4189177 baseEnd_4189177 := by
    simpa [prefixWord, tailWord_4189177, baseEnd_4189177] using wordTrace_append hprefix tailTrace_4189177
  have hstable : (prefixWord ++ tailWord_4189177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4189177).length < 2 ^ (prefixWord ++ tailWord_4189177).sum := by decide
  have hdescent : baseEnd_4189177 < baseStart_4189177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4189177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
