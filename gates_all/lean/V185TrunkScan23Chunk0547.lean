import V185TrunkScan23Chunk0546

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3233639 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_3233639 : Nat := 118140960795 + 3233639 * 2 ^ 59
def prefixEnd_3233639 : Nat := 4983230072969 + 3 ^ 40 * 3233639 * 2
def baseEnd_3233639 : Nat := 1660411070124179106241271

theorem tailTrace_3233639 : CollatzResearch.WordTrace tailWord_3233639 prefixEnd_3233639 1660411070124179106241271 := by
  unfold tailWord_3233639
  simp only [CollatzResearch.WordTrace]
  refine ⟨117940503532085639418519971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78627002354723759612346647 117940503532085639418519971)
  ·
    refine ⟨176910755298128459127779957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117940503532085639418519971 176910755298128459127779957)
    ·
      refine ⟨16585383309199543043229371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176910755298128459127779957 16585383309199543043229371)
      ·
        refine ⟨24878074963799314564844057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16585383309199543043229371 24878074963799314564844057)
        ·
          refine ⟨18658556222849485923633043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24878074963799314564844057 18658556222849485923633043)
          ·
            refine ⟨27987834334274228885449565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18658556222849485923633043 27987834334274228885449565)
            ·
              refine ⟨10495437875352835832043587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27987834334274228885449565 10495437875352835832043587)
              ·
                refine ⟨15743156813029253748065381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10495437875352835832043587 15743156813029253748065381)
                ·
                  refine ⟨2951841902442985077762259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15743156813029253748065381 2951841902442985077762259)
                  ·
                    refine ⟨4427762853664477616643389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2951841902442985077762259 4427762853664477616643389)
                    ·
                      refine ⟨1660411070124179106241271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4427762853664477616643389 1660411070124179106241271)
                      ·
                        rfl

theorem cell23_3233639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_3233639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233639 prefixEnd_3233639 := by exact prefixLift 3233639
  have htrace : WordTrace (prefixWord ++ tailWord_3233639) baseStart_3233639 baseEnd_3233639 := by
    simpa [prefixWord, tailWord_3233639, baseEnd_3233639] using wordTrace_append hprefix tailTrace_3233639
  have hstable : (prefixWord ++ tailWord_3233639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233639).length < 2 ^ (prefixWord ++ tailWord_3233639).sum := by decide
  have hdescent : baseEnd_3233639 < baseStart_3233639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233696 : List Nat := [2, 1, 1, 4, 1, 1, 1, 6, 2, 2, 2]
def baseStart_3233696 : Nat := 118140960795 + 3233696 * 2 ^ 59
def prefixEnd_3233696 : Nat := 4983230072969 + 3 ^ 40 * 3233696 * 2
def baseEnd_3233696 : Nat := 1660440338521485383228509

theorem tailTrace_3233696 : CollatzResearch.WordTrace tailWord_3233696 prefixEnd_3233696 1660440338521485383228509 := by
  unfold tailWord_3233696
  simp only [CollatzResearch.WordTrace]
  refine ⟨58971291246439569076672471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78628388328586092102229961 58971291246439569076672471)
  ·
    refine ⟨88456936869659353615008707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58971291246439569076672471 88456936869659353615008707)
    ·
      refine ⟨132685405304489030422513061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88456936869659353615008707 132685405304489030422513061)
      ·
        refine ⟨24878513494591693204221199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132685405304489030422513061 24878513494591693204221199)
        ·
          refine ⟨37317770241887539806331799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24878513494591693204221199 37317770241887539806331799)
          ·
            refine ⟨55976655362831309709497699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37317770241887539806331799 55976655362831309709497699)
            ·
              refine ⟨83964983044246964564246549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55976655362831309709497699 83964983044246964564246549)
              ·
                refine ⟨3935858580199076463949057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83964983044246964564246549 3935858580199076463949057)
                ·
                  refine ⟨2951893935149307347961793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3935858580199076463949057 2951893935149307347961793)
                  ·
                    refine ⟨2213920451361980510971345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2951893935149307347961793 2213920451361980510971345)
                    ·
                      refine ⟨1660440338521485383228509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213920451361980510971345 1660440338521485383228509)
                      ·
                        rfl

theorem cell23_3233696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_3233696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233696 prefixEnd_3233696 := by exact prefixLift 3233696
  have htrace : WordTrace (prefixWord ++ tailWord_3233696) baseStart_3233696 baseEnd_3233696 := by
    simpa [prefixWord, tailWord_3233696, baseEnd_3233696] using wordTrace_append hprefix tailTrace_3233696
  have hstable : (prefixWord ++ tailWord_3233696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233696).length < 2 ^ (prefixWord ++ tailWord_3233696).sum := by decide
  have hdescent : baseEnd_3233696 < baseStart_3233696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233705 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 8]
def baseStart_3233705 : Nat := 118140960795 + 3233705 * 2 ^ 59
def prefixEnd_3233705 : Nat := 4983230072969 + 3 ^ 40 * 3233705 * 2
def baseEnd_3233705 : Nat := 1660444959847375848015967

theorem tailTrace_3233705 : CollatzResearch.WordTrace tailWord_3233705 prefixEnd_3233705 1660444959847375848015967 := by
  unfold tailWord_3233705
  simp only [CollatzResearch.WordTrace]
  refine ⟨117942910749846532690422569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78628607166564355126948379 117942910749846532690422569)
  ·
    refine ⟨88457183062384899517816927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117942910749846532690422569 88457183062384899517816927)
    ·
      refine ⟨132685774593577349276725391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88457183062384899517816927 132685774593577349276725391)
      ·
        refine ⟨199028661890366023915088087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132685774593577349276725391 199028661890366023915088087)
        ·
          refine ⟨298542992835549035872632131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199028661890366023915088087 298542992835549035872632131)
          ·
            refine ⟨447814489253323553808948197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298542992835549035872632131 447814489253323553808948197)
            ·
              refine ⟨83965216734998166339177787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 447814489253323553808948197 83965216734998166339177787)
              ·
                refine ⟨125947825102497249508766681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83965216734998166339177787 125947825102497249508766681)
                ·
                  refine ⟨94460868826872937131575011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125947825102497249508766681 94460868826872937131575011)
                  ·
                    refine ⟨141691303240309405697362517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94460868826872937131575011 141691303240309405697362517)
                    ·
                      refine ⟨1660444959847375848015967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 141691303240309405697362517 1660444959847375848015967)
                      ·
                        rfl

theorem cell23_3233705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_3233705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233705 prefixEnd_3233705 := by exact prefixLift 3233705
  have htrace : WordTrace (prefixWord ++ tailWord_3233705) baseStart_3233705 baseEnd_3233705 := by
    simpa [prefixWord, tailWord_3233705, baseEnd_3233705] using wordTrace_append hprefix tailTrace_3233705
  have hstable : (prefixWord ++ tailWord_3233705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233705).length < 2 ^ (prefixWord ++ tailWord_3233705).sum := by decide
  have hdescent : baseEnd_3233705 < baseStart_3233705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233713 : List Nat := [1, 2, 2, 4, 2, 2, 1, 3, 2, 2, 2]
def baseStart_3233713 : Nat := 118140960795 + 3233713 * 2 ^ 59
def prefixEnd_3233713 : Nat := 4983230072969 + 3 ^ 40 * 3233713 * 2
def baseEnd_3233713 : Nat := 1660449067692611816715931

theorem tailTrace_3233713 : CollatzResearch.WordTrace tailWord_3233713 prefixEnd_3233713 1660449067692611816715931 := by
  unfold tailWord_3233713
  simp only [CollatzResearch.WordTrace]
  refine ⟨117943202533817550056713793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78628801689211700037809195 117943202533817550056713793)
  ·
    refine ⟨88457401900363162542535345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117943202533817550056713793 88457401900363162542535345)
    ·
      refine ⟨66343051425272371906901509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88457401900363162542535345 66343051425272371906901509)
      ·
        refine ⟨12439322142238569732544033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66343051425272371906901509 12439322142238569732544033)
        ·
          refine ⟨9329491606678927299408025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12439322142238569732544033 9329491606678927299408025)
          ·
            refine ⟨6997118705009195474556019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9329491606678927299408025 6997118705009195474556019)
            ·
              refine ⟨10495678057513793211834029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6997118705009195474556019 10495678057513793211834029)
              ·
                refine ⟨3935879271567672454437761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10495678057513793211834029 3935879271567672454437761)
                ·
                  refine ⟨2951909453675754340828321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3935879271567672454437761 2951909453675754340828321)
                  ·
                    refine ⟨2213932090256815755621241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2951909453675754340828321 2213932090256815755621241)
                    ·
                      refine ⟨1660449067692611816715931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213932090256815755621241 1660449067692611816715931)
                      ·
                        rfl

theorem cell23_3233713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_3233713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233713 prefixEnd_3233713 := by exact prefixLift 3233713
  have htrace : WordTrace (prefixWord ++ tailWord_3233713) baseStart_3233713 baseEnd_3233713 := by
    simpa [prefixWord, tailWord_3233713, baseEnd_3233713] using wordTrace_append hprefix tailTrace_3233713
  have hstable : (prefixWord ++ tailWord_3233713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233713).length < 2 ^ (prefixWord ++ tailWord_3233713).sum := by decide
  have hdescent : baseEnd_3233713 < baseStart_3233713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233742 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3233742 : Nat := 118140960795 + 3233742 * 2 ^ 59
def prefixEnd_3233742 : Nat := 4983230072969 + 3 ^ 40 * 3233742 * 2
def baseEnd_3233742 : Nat := 1660463958631592203253297

theorem tailTrace_3233742 : CollatzResearch.WordTrace tailWord_3233742 prefixEnd_3233742 1660463958631592203253297 := by
  unfold tailWord_3233742
  simp only [CollatzResearch.WordTrace]
  refine ⟨14743032531339061001189935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78629506833808325339679653 14743032531339061001189935)
  ·
    refine ⟨22114548797008591501784903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14743032531339061001189935 22114548797008591501784903)
    ·
      refine ⟨33171823195512887252677355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22114548797008591501784903 33171823195512887252677355)
      ·
        refine ⟨49757734793269330879016033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33171823195512887252677355 49757734793269330879016033)
        ·
          refine ⟨37318301094951998159262025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49757734793269330879016033 37318301094951998159262025)
          ·
            refine ⟨27988725821213998619446519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37318301094951998159262025 27988725821213998619446519)
            ·
              refine ⟨41983088731820997929169779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27988725821213998619446519 41983088731820997929169779)
              ·
                refine ⟨62974633097731496893754669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41983088731820997929169779 62974633097731496893754669)
                ·
                  refine ⟨23615487411649311335158001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62974633097731496893754669 23615487411649311335158001)
                  ·
                    refine ⟨17711615558736983501368501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23615487411649311335158001 17711615558736983501368501)
                    ·
                      refine ⟨1660463958631592203253297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17711615558736983501368501 1660463958631592203253297)
                      ·
                        rfl

theorem cell23_3233742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3233742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233742 prefixEnd_3233742 := by exact prefixLift 3233742
  have htrace : WordTrace (prefixWord ++ tailWord_3233742) baseStart_3233742 baseEnd_3233742 := by
    simpa [prefixWord, tailWord_3233742, baseEnd_3233742] using wordTrace_append hprefix tailTrace_3233742
  have hstable : (prefixWord ++ tailWord_3233742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233742).length < 2 ^ (prefixWord ++ tailWord_3233742).sum := by decide
  have hdescent : baseEnd_3233742 < baseStart_3233742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233749 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 2, 5]
def baseStart_3233749 : Nat := 118140960795 + 3233749 * 2 ^ 59
def prefixEnd_3233749 : Nat := 4983230072969 + 3 ^ 40 * 3233749 * 2
def baseEnd_3233749 : Nat := 553489184332057891955255

theorem tailTrace_3233749 : CollatzResearch.WordTrace tailWord_3233749 prefixEnd_3233749 553489184332057891955255 := by
  unfold tailWord_3233749
  simp only [CollatzResearch.WordTrace]
  refine ⟨117944515561687128205024301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78629677041124752136682867 117944515561687128205024301)
  ·
    refine ⟨44229193335632673076884113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117944515561687128205024301 44229193335632673076884113)
    ·
      refine ⟨33171895001724504807663085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44229193335632673076884113 33171895001724504807663085)
      ·
        refine ⟨12439460625646689302873657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33171895001724504807663085 12439460625646689302873657)
        ·
          refine ⟨9329595469235016977155243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12439460625646689302873657 9329595469235016977155243)
          ·
            refine ⟨13994393203852525465732865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9329595469235016977155243 13994393203852525465732865)
            ·
              refine ⟨10495794902889394099299649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13994393203852525465732865 10495794902889394099299649)
              ·
                refine ⟨7871846177167045574474737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10495794902889394099299649 7871846177167045574474737)
                ·
                  refine ⟨5903884632875284180856053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7871846177167045574474737 5903884632875284180856053)
                  ·
                    refine ⟨553489184332057891955255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5903884632875284180856053 553489184332057891955255)
                    ·
                      rfl

theorem cell23_3233749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_3233749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233749 prefixEnd_3233749 := by exact prefixLift 3233749
  have htrace : WordTrace (prefixWord ++ tailWord_3233749) baseStart_3233749 baseEnd_3233749 := by
    simpa [prefixWord, tailWord_3233749, baseEnd_3233749] using wordTrace_append hprefix tailTrace_3233749
  have hstable : (prefixWord ++ tailWord_3233749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233749).length < 2 ^ (prefixWord ++ tailWord_3233749).sum := by decide
  have hdescent : baseEnd_3233749 < baseStart_3233749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233753 : List Nat := [1, 2, 1, 2, 6, 2, 2, 2, 5]
def baseStart_3233753 : Nat := 118140960795 + 3233753 * 2 ^ 59
def prefixEnd_3233753 : Nat := 4983230072969 + 3 ^ 40 * 3233753 * 2
def baseEnd_3233753 : Nat := 184496622990976851135083

theorem tailTrace_3233753 : CollatzResearch.WordTrace tailWord_3233753 prefixEnd_3233753 184496622990976851135083 := by
  unfold tailWord_3233753
  simp only [CollatzResearch.WordTrace]
  refine ⟨117944661453672636888169913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78629774302448424592113275 117944661453672636888169913)
  ·
    refine ⟨88458496090254477666127435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117944661453672636888169913 88458496090254477666127435)
    ·
      refine ⟨132687744135381716499191153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88458496090254477666127435 132687744135381716499191153)
      ·
        refine ⟨99515808101536287374393365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132687744135381716499191153 99515808101536287374393365)
        ·
          refine ⟨4664803504759513470674689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99515808101536287374393365 4664803504759513470674689)
          ·
            refine ⟨3498602628569635103006017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4664803504759513470674689 3498602628569635103006017)
            ·
              refine ⟨2623951971427226327254513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3498602628569635103006017 2623951971427226327254513)
              ·
                refine ⟨1967963978570419745440885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2623951971427226327254513 1967963978570419745440885)
                ·
                  refine ⟨184496622990976851135083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1967963978570419745440885 184496622990976851135083)
                  ·
                    rfl

theorem cell23_3233753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 5].length) (baseStart_3233753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233753 prefixEnd_3233753 := by exact prefixLift 3233753
  have htrace : WordTrace (prefixWord ++ tailWord_3233753) baseStart_3233753 baseEnd_3233753 := by
    simpa [prefixWord, tailWord_3233753, baseEnd_3233753] using wordTrace_append hprefix tailTrace_3233753
  have hstable : (prefixWord ++ tailWord_3233753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233753).length < 2 ^ (prefixWord ++ tailWord_3233753).sum := by decide
  have hdescent : baseEnd_3233753 < baseStart_3233753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233798 : List Nat := [6, 2, 1, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_3233798 : Nat := 118140960795 + 3233798 * 2 ^ 59
def prefixEnd_3233798 : Nat := 4983230072969 + 3 ^ 40 * 3233798 * 2
def baseEnd_3233798 : Nat := 1660492713548243984153041

theorem tailTrace_3233798 : CollatzResearch.WordTrace tailWord_3233798 prefixEnd_3233798 1660492713548243984153041 := by
  unfold tailWord_3233798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685821960578425299173689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78630868492339739715705365 3685821960578425299173689)
  ·
    refine ⟨2764366470433818974380267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3685821960578425299173689 2764366470433818974380267)
    ·
      refine ⟨4146549705650728461570401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2764366470433818974380267 4146549705650728461570401)
      ·
        refine ⟨3109912279238046346177801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4146549705650728461570401 3109912279238046346177801)
        ·
          refine ⟨2332434209428534759633351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3109912279238046346177801 2332434209428534759633351)
          ·
            refine ⟨3498651314142802139450027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2332434209428534759633351 3498651314142802139450027)
            ·
              refine ⟨5247976971214203209175041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3498651314142802139450027 5247976971214203209175041)
              ·
                refine ⟨3935982728410652406881281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5247976971214203209175041 3935982728410652406881281)
                ·
                  refine ⟨2951987046307989305160961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3935982728410652406881281 2951987046307989305160961)
                  ·
                    refine ⟨2213990284730991978870721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2951987046307989305160961 2213990284730991978870721)
                    ·
                      refine ⟨1660492713548243984153041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2213990284730991978870721 1660492713548243984153041)
                      ·
                        rfl

theorem cell23_3233798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_3233798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233798 prefixEnd_3233798 := by exact prefixLift 3233798
  have htrace : WordTrace (prefixWord ++ tailWord_3233798) baseStart_3233798 baseEnd_3233798 := by
    simpa [prefixWord, tailWord_3233798, baseEnd_3233798] using wordTrace_append hprefix tailTrace_3233798
  have hstable : (prefixWord ++ tailWord_3233798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233798).length < 2 ^ (prefixWord ++ tailWord_3233798).sum := by decide
  have hdescent : baseEnd_3233798 < baseStart_3233798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233826 : List Nat := [3, 3, 1, 1, 1, 2, 5, 1, 6]
def baseStart_3233826 : Nat := 118140960795 + 3233826 * 2 ^ 59
def prefixEnd_3233826 : Nat := 4983230072969 + 3 ^ 40 * 3233826 * 2
def baseEnd_3233826 : Nat := 184500787889618874955879

theorem tailTrace_3233826 : CollatzResearch.WordTrace tailWord_3233826 prefixEnd_3233826 184500787889618874955879 := by
  unfold tailWord_3233826
  simp only [CollatzResearch.WordTrace]
  refine ⟨29486830995602042588894333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78631549321605446903718221 29486830995602042588894333)
  ·
    refine ⟨11057561623350765970835375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29486830995602042588894333 11057561623350765970835375)
    ·
      refine ⟨16586342435026148956253063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11057561623350765970835375 16586342435026148956253063)
      ·
        refine ⟨24879513652539223434379595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16586342435026148956253063 24879513652539223434379595)
        ·
          refine ⟨37319270478808835151569393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24879513652539223434379595 37319270478808835151569393)
          ·
            refine ⟨27989452859106626363677045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37319270478808835151569393 27989452859106626363677045)
            ·
              refine ⟨2624011205541246221594723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27989452859106626363677045 2624011205541246221594723)
              ·
                refine ⟨3936016808311869332392085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2624011205541246221594723 3936016808311869332392085)
                ·
                  refine ⟨184500787889618874955879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3936016808311869332392085 184500787889618874955879)
                  ·
                    rfl

theorem cell23_3233826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_3233826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233826 prefixEnd_3233826 := by exact prefixLift 3233826
  have htrace : WordTrace (prefixWord ++ tailWord_3233826) baseStart_3233826 baseEnd_3233826 := by
    simpa [prefixWord, tailWord_3233826, baseEnd_3233826] using wordTrace_append hprefix tailTrace_3233826
  have hstable : (prefixWord ++ tailWord_3233826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233826).length < 2 ^ (prefixWord ++ tailWord_3233826).sum := by decide
  have hdescent : baseEnd_3233826 < baseStart_3233826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233879 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 5]
def baseStart_3233879 : Nat := 118140960795 + 3233879 * 2 ^ 59
def prefixEnd_3233879 : Nat := 4983230072969 + 3 ^ 40 * 3233879 * 2
def baseEnd_3233879 : Nat := 1660534305481258167240167

theorem tailTrace_3233879 : CollatzResearch.WordTrace tailWord_3233879 prefixEnd_3233879 1660534305481258167240167 := by
  unfold tailWord_3233879
  simp only [CollatzResearch.WordTrace]
  refine ⟨117949257051216160407256691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78632838034144106938171127 117949257051216160407256691)
  ·
    refine ⟨176923885576824240610885037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117949257051216160407256691 176923885576824240610885037)
    ·
      refine ⟨66346457091309090229081889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176923885576824240610885037 66346457091309090229081889)
      ·
        refine ⟨49759842818481817671811417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66346457091309090229081889 49759842818481817671811417)
        ·
          refine ⟨37319882113861363253858563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49759842818481817671811417 37319882113861363253858563)
          ·
            refine ⟨55979823170792044880787845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37319882113861363253858563 55979823170792044880787845)
            ·
              refine ⟨10496216844523508415147721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55979823170792044880787845 10496216844523508415147721)
              ·
                refine ⟨7872162633392631311360791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10496216844523508415147721 7872162633392631311360791)
                ·
                  refine ⟨11808243950088946967041187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7872162633392631311360791 11808243950088946967041187)
                  ·
                    refine ⟨17712365925133420450561781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11808243950088946967041187 17712365925133420450561781)
                    ·
                      refine ⟨1660534305481258167240167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17712365925133420450561781 1660534305481258167240167)
                      ·
                        rfl

theorem cell23_3233879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_3233879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233879 prefixEnd_3233879 := by exact prefixLift 3233879
  have htrace : WordTrace (prefixWord ++ tailWord_3233879) baseStart_3233879 baseEnd_3233879 := by
    simpa [prefixWord, tailWord_3233879, baseEnd_3233879] using wordTrace_append hprefix tailTrace_3233879
  have hstable : (prefixWord ++ tailWord_3233879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233879).length < 2 ^ (prefixWord ++ tailWord_3233879).sum := by decide
  have hdescent : baseEnd_3233879 < baseStart_3233879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233889 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_3233889 : Nat := 118140960795 + 3233889 * 2 ^ 59
def prefixEnd_3233889 : Nat := 4983230072969 + 3 ^ 40 * 3233889 * 2
def baseEnd_3233889 : Nat := 1660539440287803128115121

theorem tailTrace_3233889 : CollatzResearch.WordTrace tailWord_3233889 prefixEnd_3233889 1660539440287803128115121 := by
  unfold tailWord_3233889
  simp only [CollatzResearch.WordTrace]
  refine ⟨117949621781179932115120721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78633081187453288076747147 117949621781179932115120721)
  ·
    refine ⟨88462216335884949086340541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117949621781179932115120721 88462216335884949086340541)
    ·
      refine ⟨33173331125956855907377703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88462216335884949086340541 33173331125956855907377703)
      ·
        refine ⟨49759996688935283861066555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33173331125956855907377703 49759996688935283861066555)
        ·
          refine ⟨74639995033402925791599833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49759996688935283861066555 74639995033402925791599833)
          ·
            refine ⟨55979996275052194343699875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74639995033402925791599833 55979996275052194343699875)
            ·
              refine ⟨83969994412578291515549813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55979996275052194343699875 83969994412578291515549813)
              ·
                refine ⟨7872186976179214829582795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83969994412578291515549813 7872186976179214829582795)
                ·
                  refine ⟨11808280464268822244374193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7872186976179214829582795 11808280464268822244374193)
                  ·
                    refine ⟨8856210348201616683280645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11808280464268822244374193 8856210348201616683280645)
                    ·
                      refine ⟨1660539440287803128115121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8856210348201616683280645 1660539440287803128115121)
                      ·
                        rfl

theorem cell23_3233889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_3233889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233889 prefixEnd_3233889 := by exact prefixLift 3233889
  have htrace : WordTrace (prefixWord ++ tailWord_3233889) baseStart_3233889 baseEnd_3233889 := by
    simpa [prefixWord, tailWord_3233889, baseEnd_3233889] using wordTrace_append hprefix tailTrace_3233889
  have hstable : (prefixWord ++ tailWord_3233889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233889).length < 2 ^ (prefixWord ++ tailWord_3233889).sum := by decide
  have hdescent : baseEnd_3233889 < baseStart_3233889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233890 : List Nat := [3, 3, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3233890 : Nat := 118140960795 + 3233890 * 2 ^ 59
def prefixEnd_3233890 : Nat := 4983230072969 + 3 ^ 40 * 3233890 * 2
def baseEnd_3233890 : Nat := 553513317922819208067539

theorem tailTrace_3233890 : CollatzResearch.WordTrace tailWord_3233890 prefixEnd_3233890 553513317922819208067539 := by
  unfold tailWord_3233890
  simp only [CollatzResearch.WordTrace]
  refine ⟨29487414563544077321476781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78633105502784206190604749 29487414563544077321476781)
  ·
    refine ⟨11057780461329028995553793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29487414563544077321476781 11057780461329028995553793)
    ·
      refine ⟨8293335345996771746665345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11057780461329028995553793 8293335345996771746665345)
      ·
        refine ⟨6220001509497578809999009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8293335345996771746665345 6220001509497578809999009)
        ·
          refine ⟨4665001132123184107499257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6220001509497578809999009 4665001132123184107499257)
          ·
            refine ⟨3498750849092388080624443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4665001132123184107499257 3498750849092388080624443)
            ·
              refine ⟨5248126273638582120936665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3498750849092388080624443 5248126273638582120936665)
              ·
                refine ⟨3936094705228936590702499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5248126273638582120936665 3936094705228936590702499)
                ·
                  refine ⟨5904142057843404886053749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3936094705228936590702499 5904142057843404886053749)
                  ·
                    refine ⟨553513317922819208067539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5904142057843404886053749 553513317922819208067539)
                    ·
                      rfl

theorem cell23_3233890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3233890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233890 prefixEnd_3233890 := by exact prefixLift 3233890
  have htrace : WordTrace (prefixWord ++ tailWord_3233890) baseStart_3233890 baseEnd_3233890 := by
    simpa [prefixWord, tailWord_3233890, baseEnd_3233890] using wordTrace_append hprefix tailTrace_3233890
  have hstable : (prefixWord ++ tailWord_3233890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233890).length < 2 ^ (prefixWord ++ tailWord_3233890).sum := by decide
  have hdescent : baseEnd_3233890 < baseStart_3233890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233893 : List Nat := [1, 3, 1, 3, 2, 4, 1, 2, 1, 1, 4]
def baseStart_3233893 : Nat := 118140960795 + 3233893 * 2 ^ 59
def prefixEnd_3233893 : Nat := 4983230072969 + 3 ^ 40 * 3233893 * 2
def baseEnd_3233893 : Nat := 1660541494210421112465103

theorem tailTrace_3233893 : CollatzResearch.WordTrace tailWord_3233893 prefixEnd_3233893 1660541494210421112465103 := by
  unfold tailWord_3233893
  simp only [CollatzResearch.WordTrace]
  refine ⟨117949767673165440798266333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78633178448776960532177555 117949767673165440798266333)
  ·
    refine ⟨44231162877437040299349875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117949767673165440798266333 44231162877437040299349875)
    ·
      refine ⟨66346744316155560449024813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44231162877437040299349875 66346744316155560449024813)
      ·
        refine ⟨24880029118558335168384305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66346744316155560449024813 24880029118558335168384305)
        ·
          refine ⟨18660021838918751376288229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24880029118558335168384305 18660021838918751376288229)
          ·
            refine ⟨3498754094797265883054043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18660021838918751376288229 3498754094797265883054043)
            ·
              refine ⟨5248131142195898824581065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3498754094797265883054043 5248131142195898824581065)
              ·
                refine ⟨3936098356646924118435799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5248131142195898824581065 3936098356646924118435799)
                ·
                  refine ⟨5904147534970386177653699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3936098356646924118435799 5904147534970386177653699)
                  ·
                    refine ⟨8856221302455579266480549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5904147534970386177653699 8856221302455579266480549)
                    ·
                      refine ⟨1660541494210421112465103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8856221302455579266480549 1660541494210421112465103)
                      ·
                        rfl

theorem cell23_3233893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_3233893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233893 prefixEnd_3233893 := by exact prefixLift 3233893
  have htrace : WordTrace (prefixWord ++ tailWord_3233893) baseStart_3233893 baseEnd_3233893 := by
    simpa [prefixWord, tailWord_3233893, baseEnd_3233893] using wordTrace_append hprefix tailTrace_3233893
  have hstable : (prefixWord ++ tailWord_3233893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233893).length < 2 ^ (prefixWord ++ tailWord_3233893).sum := by decide
  have hdescent : baseEnd_3233893 < baseStart_3233893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233906 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_3233906 : Nat := 118140960795 + 3233906 * 2 ^ 59
def prefixEnd_3233906 : Nat := 4983230072969 + 3 ^ 40 * 3233906 * 2
def baseEnd_3233906 : Nat := 1660548169458929561602543

theorem tailTrace_3233906 : CollatzResearch.WordTrace tailWord_3233906 prefixEnd_3233906 1660548169458929561602543 := by
  unfold tailWord_3233906
  simp only [CollatzResearch.WordTrace]
  refine ⟨29487560455529586004622393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78633494548078896012326381 29487560455529586004622393)
  ·
    refine ⟨22115670341647189503466795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29487560455529586004622393 22115670341647189503466795)
    ·
      refine ⟨33173505512470784255200193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22115670341647189503466795 33173505512470784255200193)
      ·
        refine ⟨24880129134353088191400145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33173505512470784255200193 24880129134353088191400145)
        ·
          refine ⟨18660096850764816143550109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24880129134353088191400145 18660096850764816143550109)
          ·
            refine ⟨6997536319036806053831291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18660096850764816143550109 6997536319036806053831291)
            ·
              refine ⟨10496304478555209080746937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6997536319036806053831291 10496304478555209080746937)
              ·
                refine ⟨7872228358916406810560203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10496304478555209080746937 7872228358916406810560203)
                ·
                  refine ⟨11808342538374610215840305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7872228358916406810560203 11808342538374610215840305)
                  ·
                    refine ⟨8856256903780957661880229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11808342538374610215840305 8856256903780957661880229)
                    ·
                      refine ⟨1660548169458929561602543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8856256903780957661880229 1660548169458929561602543)
                      ·
                        rfl

theorem cell23_3233906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_3233906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233906 prefixEnd_3233906 := by exact prefixLift 3233906
  have htrace : WordTrace (prefixWord ++ tailWord_3233906) baseStart_3233906 baseEnd_3233906 := by
    simpa [prefixWord, tailWord_3233906, baseEnd_3233906] using wordTrace_append hprefix tailTrace_3233906
  have hstable : (prefixWord ++ tailWord_3233906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233906).length < 2 ^ (prefixWord ++ tailWord_3233906).sum := by decide
  have hdescent : baseEnd_3233906 < baseStart_3233906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233910 : List Nat := [5, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_3233910 : Nat := 118140960795 + 3233910 * 2 ^ 59
def prefixEnd_3233910 : Nat := 4983230072969 + 3 ^ 40 * 3233910 * 2
def baseEnd_3233910 : Nat := 1660550223381547545952525

theorem tailTrace_3233910 : CollatzResearch.WordTrace tailWord_3233910 prefixEnd_3233910 1660550223381547545952525 := by
  unfold tailWord_3233910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7371899232131490793852199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78633591809402568467756789 7371899232131490793852199)
  ·
    refine ⟨11057848848197236190778299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7371899232131490793852199 11057848848197236190778299)
    ·
      refine ⟨16586773272295854286167449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11057848848197236190778299 16586773272295854286167449)
      ·
        refine ⟨12440079954221890714625587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16586773272295854286167449 12440079954221890714625587)
        ·
          refine ⟨18660119931332836071938381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12440079954221890714625587 18660119931332836071938381)
          ·
            refine ⟨6997544974249813526976893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18660119931332836071938381 6997544974249813526976893)
            ·
              refine ⟨2624079365343680072616335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6997544974249813526976893 2624079365343680072616335)
              ·
                refine ⟨3936119048015520108924503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2624079365343680072616335 3936119048015520108924503)
                ·
                  refine ⟨5904178572023280163386755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3936119048015520108924503 5904178572023280163386755)
                  ·
                    refine ⟨8856267858034920245080133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5904178572023280163386755 8856267858034920245080133)
                    ·
                      refine ⟨1660550223381547545952525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8856267858034920245080133 1660550223381547545952525)
                      ·
                        rfl

theorem cell23_3233910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_3233910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233910 prefixEnd_3233910 := by exact prefixLift 3233910
  have htrace : WordTrace (prefixWord ++ tailWord_3233910) baseStart_3233910 baseEnd_3233910 := by
    simpa [prefixWord, tailWord_3233910, baseEnd_3233910] using wordTrace_append hprefix tailTrace_3233910
  have hstable : (prefixWord ++ tailWord_3233910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233910).length < 2 ^ (prefixWord ++ tailWord_3233910).sum := by decide
  have hdescent : baseEnd_3233910 < baseStart_3233910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233927 : List Nat := [1, 1, 4, 2, 1, 1, 6, 2, 1, 2, 2]
def baseStart_3233927 : Nat := 118140960795 + 3233927 * 2 ^ 59
def prefixEnd_3233927 : Nat := 4983230072969 + 3 ^ 40 * 3233927 * 2
def baseEnd_3233927 : Nat := 1660558952552673979439947

theorem tailTrace_3233927 : CollatzResearch.WordTrace tailWord_3233927 prefixEnd_3233927 1660558952552673979439947 := by
  unfold tailWord_3233927
  simp only [CollatzResearch.WordTrace]
  refine ⟨117951007755042264605004035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78634005170028176403336023 117951007755042264605004035)
  ·
    refine ⟨176926511632563396907506053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117951007755042264605004035 176926511632563396907506053)
    ·
      refine ⟨33173720931105636920157385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176926511632563396907506053 33173720931105636920157385)
      ·
        refine ⟨24880290698329227690118039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33173720931105636920157385 24880290698329227690118039)
        ·
          refine ⟨37320436047493841535177059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24880290698329227690118039 37320436047493841535177059)
          ·
            refine ⟨55980654071240762302765589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37320436047493841535177059 55980654071240762302765589)
            ·
              refine ⟨2624093159589410732942137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55980654071240762302765589 2624093159589410732942137)
              ·
                refine ⟨1968069869692058049706603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2624093159589410732942137 1968069869692058049706603)
                ·
                  refine ⟨2952104804538087074559905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968069869692058049706603 2952104804538087074559905)
                  ·
                    refine ⟨2214078603403565305919929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2952104804538087074559905 2214078603403565305919929)
                    ·
                      refine ⟨1660558952552673979439947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2214078603403565305919929 1660558952552673979439947)
                      ·
                        rfl

theorem cell23_3233927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_3233927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233927 prefixEnd_3233927 := by exact prefixLift 3233927
  have htrace : WordTrace (prefixWord ++ tailWord_3233927) baseStart_3233927 baseEnd_3233927 := by
    simpa [prefixWord, tailWord_3233927, baseEnd_3233927] using wordTrace_append hprefix tailTrace_3233927
  have hstable : (prefixWord ++ tailWord_3233927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233927).length < 2 ^ (prefixWord ++ tailWord_3233927).sum := by decide
  have hdescent : baseEnd_3233927 < baseStart_3233927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233936 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 5, 3, 2]
def baseStart_3233936 : Nat := 118140960795 + 3233936 * 2 ^ 59
def prefixEnd_3233936 : Nat := 4983230072969 + 3 ^ 40 * 3233936 * 2
def baseEnd_3233936 : Nat := 1660563573878564444227405

theorem tailTrace_3233936 : CollatzResearch.WordTrace tailWord_3233936 prefixEnd_3233936 1660563573878564444227405 := by
  unfold tailWord_3233936
  simp only [CollatzResearch.WordTrace]
  refine ⟨58975668006004829571040831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78634224008006439428054441 58975668006004829571040831)
  ·
    refine ⟨88463502009007244356561247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58975668006004829571040831 88463502009007244356561247)
    ·
      refine ⟨132695253013510866534841871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88463502009007244356561247 132695253013510866534841871)
      ·
        refine ⟨199042879520266299802262807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132695253013510866534841871 199042879520266299802262807)
        ·
          refine ⟨298564319280399449703394211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199042879520266299802262807 298564319280399449703394211)
          ·
            refine ⟨447846478920599174555091317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298564319280399449703394211 447846478920599174555091317)
            ·
              refine ⟨41985607398806172614539811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 447846478920599174555091317 41985607398806172614539811)
              ·
                refine ⟨62978411098209258921809717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41985607398806172614539811 62978411098209258921809717)
                ·
                  refine ⟨5904226040457118023919661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62978411098209258921809717 5904226040457118023919661)
                  ·
                    refine ⟨2214084765171419258969873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5904226040457118023919661 2214084765171419258969873)
                    ·
                      refine ⟨1660563573878564444227405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2214084765171419258969873 1660563573878564444227405)
                      ·
                        rfl

theorem cell23_3233936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 5, 3, 2].length) (baseStart_3233936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233936 prefixEnd_3233936 := by exact prefixLift 3233936
  have htrace : WordTrace (prefixWord ++ tailWord_3233936) baseStart_3233936 baseEnd_3233936 := by
    simpa [prefixWord, tailWord_3233936, baseEnd_3233936] using wordTrace_append hprefix tailTrace_3233936
  have hstable : (prefixWord ++ tailWord_3233936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233936).length < 2 ^ (prefixWord ++ tailWord_3233936).sum := by decide
  have hdescent : baseEnd_3233936 < baseStart_3233936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233940 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3233940 : Nat := 118140960795 + 3233940 * 2 ^ 59
def prefixEnd_3233940 : Nat := 4983230072969 + 3 ^ 40 * 3233940 * 2
def baseEnd_3233940 : Nat := 1660565627801182428577387

theorem tailTrace_3233940 : CollatzResearch.WordTrace tailWord_3233940 prefixEnd_3233940 1660565627801182428577387 := by
  unfold tailWord_3233940
  simp only [CollatzResearch.WordTrace]
  refine ⟨58975740951997583912613637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78634321269330111883484849 58975740951997583912613637)
  ·
    refine ⟨11057951428499546983615057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58975740951997583912613637 11057951428499546983615057)
    ·
      refine ⟨8293463571374660237711293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11057951428499546983615057 8293463571374660237711293)
      ·
        refine ⟨3110048839265497589141735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8293463571374660237711293 3110048839265497589141735)
        ·
          refine ⟨4665073258898246383712603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3110048839265497589141735 4665073258898246383712603)
          ·
            refine ⟨6997609888347369575568905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4665073258898246383712603 6997609888347369575568905)
            ·
              refine ⟨5248207416260527181676679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6997609888347369575568905 5248207416260527181676679)
              ·
                refine ⟨7872311124390790772515019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5248207416260527181676679 7872311124390790772515019)
                ·
                  refine ⟨11808466686586186158772529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7872311124390790772515019 11808466686586186158772529)
                  ·
                    refine ⟨8856350014939639619079397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11808466686586186158772529 8856350014939639619079397)
                    ·
                      refine ⟨1660565627801182428577387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8856350014939639619079397 1660565627801182428577387)
                      ·
                        rfl

theorem cell23_3233940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3233940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233940 prefixEnd_3233940 := by exact prefixLift 3233940
  have htrace : WordTrace (prefixWord ++ tailWord_3233940) baseStart_3233940 baseEnd_3233940 := by
    simpa [prefixWord, tailWord_3233940, baseEnd_3233940] using wordTrace_append hprefix tailTrace_3233940
  have hstable : (prefixWord ++ tailWord_3233940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233940).length < 2 ^ (prefixWord ++ tailWord_3233940).sum := by decide
  have hdescent : baseEnd_3233940 < baseStart_3233940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233943 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 3]
def baseStart_3233943 : Nat := 118140960795 + 3233943 * 2 ^ 59
def prefixEnd_3233943 : Nat := 4983230072969 + 3 ^ 40 * 3233943 * 2
def baseEnd_3233943 : Nat := 1660567168243145916839873

theorem tailTrace_3233943 : CollatzResearch.WordTrace tailWord_3233943 prefixEnd_3233943 1660567168243145916839873 := by
  unfold tailWord_3233943
  simp only [CollatzResearch.WordTrace]
  refine ⟨117951591322984299337586483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78634394215322866225057655 117951591322984299337586483)
  ·
    refine ⟨176927386984476449006379725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117951591322984299337586483 176927386984476449006379725)
    ·
      refine ⟨66347770119178668377392397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176927386984476449006379725 66347770119178668377392397)
      ·
        refine ⟨24880413794692000641522149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66347770119178668377392397 24880413794692000641522149)
        ·
          refine ⟨4665077586504750120285403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24880413794692000641522149 4665077586504750120285403)
          ·
            refine ⟨6997616379757125180428105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4665077586504750120285403 6997616379757125180428105)
            ·
              refine ⟨5248212284817843885321079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6997616379757125180428105 5248212284817843885321079)
              ·
                refine ⟨7872318427226765827981619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5248212284817843885321079 7872318427226765827981619)
                ·
                  refine ⟨11808477640840148741972429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7872318427226765827981619 11808477640840148741972429)
                  ·
                    refine ⟨4428179115315055778239661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11808477640840148741972429 4428179115315055778239661)
                    ·
                      refine ⟨1660567168243145916839873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4428179115315055778239661 1660567168243145916839873)
                      ·
                        rfl

theorem cell23_3233943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_3233943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233943 prefixEnd_3233943 := by exact prefixLift 3233943
  have htrace : WordTrace (prefixWord ++ tailWord_3233943) baseStart_3233943 baseEnd_3233943 := by
    simpa [prefixWord, tailWord_3233943, baseEnd_3233943] using wordTrace_append hprefix tailTrace_3233943
  have hstable : (prefixWord ++ tailWord_3233943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233943).length < 2 ^ (prefixWord ++ tailWord_3233943).sum := by decide
  have hdescent : baseEnd_3233943 < baseStart_3233943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233953 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 3, 3, 2]
def baseStart_3233953 : Nat := 118140960795 + 3233953 * 2 ^ 59
def prefixEnd_3233953 : Nat := 4983230072969 + 3 ^ 40 * 3233953 * 2
def baseEnd_3233953 : Nat := 1660572303049690877714827

theorem tailTrace_3233953 : CollatzResearch.WordTrace tailWord_3233953 prefixEnd_3233953 1660572303049690877714827 := by
  unfold tailWord_3233953
  simp only [CollatzResearch.WordTrace]
  refine ⟨117951956052948071045450513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78634637368632047363633675 117951956052948071045450513)
  ·
    refine ⟨88463967039711053284087885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117951956052948071045450513 88463967039711053284087885)
    ·
      refine ⟨33173987639891644981532957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88463967039711053284087885 33173987639891644981532957)
      ·
        refine ⟨12440245364959366868074859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33173987639891644981532957 12440245364959366868074859)
        ·
          refine ⟨18660368047439050302112289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12440245364959366868074859 18660368047439050302112289)
          ·
            refine ⟨13995276035579287726584217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18660368047439050302112289 13995276035579287726584217)
            ·
              refine ⟨10496457026684465794938163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13995276035579287726584217 10496457026684465794938163)
              ·
                refine ⟨15744685540026698692407245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10496457026684465794938163 15744685540026698692407245)
                ·
                  refine ⟨5904257077510012009652717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15744685540026698692407245 5904257077510012009652717)
                  ·
                    refine ⟨2214096404066254503619769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5904257077510012009652717 2214096404066254503619769)
                    ·
                      refine ⟨1660572303049690877714827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2214096404066254503619769 1660572303049690877714827)
                      ·
                        rfl

theorem cell23_3233953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_3233953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233953 prefixEnd_3233953 := by exact prefixLift 3233953
  have htrace : WordTrace (prefixWord ++ tailWord_3233953) baseStart_3233953 baseEnd_3233953 := by
    simpa [prefixWord, tailWord_3233953, baseEnd_3233953] using wordTrace_append hprefix tailTrace_3233953
  have hstable : (prefixWord ++ tailWord_3233953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233953).length < 2 ^ (prefixWord ++ tailWord_3233953).sum := by decide
  have hdescent : baseEnd_3233953 < baseStart_3233953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233979 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 4]
def baseStart_3233979 : Nat := 118140960795 + 3233979 * 2 ^ 59
def prefixEnd_3233979 : Nat := 4983230072969 + 3 ^ 40 * 3233979 * 2
def baseEnd_3233979 : Nat := 1660585653546707775989707

theorem tailTrace_3233979 : CollatzResearch.WordTrace tailWord_3233979 prefixEnd_3233979 1660585653546707775989707 := by
  unfold tailWord_3233979
  simp only [CollatzResearch.WordTrace]
  refine ⟨117952904350853877485896991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78635269567235918323931327 117952904350853877485896991)
  ·
    refine ⟨176929356526280816228845487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117952904350853877485896991 176929356526280816228845487)
    ·
      refine ⟨265394034789421224343268231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176929356526280816228845487 265394034789421224343268231)
      ·
        refine ⟨398091052184131836514902347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265394034789421224343268231 398091052184131836514902347)
        ·
          refine ⟨597136578276197754772353521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398091052184131836514902347 597136578276197754772353521)
          ·
            refine ⟨447852433707148316079265141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597136578276197754772353521 447852433707148316079265141)
            ·
              refine ⟨41986165660045154632431107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 447852433707148316079265141 41986165660045154632431107)
              ·
                refine ⟨62979248490067731948646661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41986165660045154632431107 62979248490067731948646661)
                ·
                  refine ⟨11808609091887699740371249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62979248490067731948646661 11808609091887699740371249)
                  ·
                    refine ⟨8856456818915774805278437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11808609091887699740371249 8856456818915774805278437)
                    ·
                      refine ⟨1660585653546707775989707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8856456818915774805278437 1660585653546707775989707)
                      ·
                        rfl

theorem cell23_3233979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 4].length) (baseStart_3233979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233979 prefixEnd_3233979 := by exact prefixLift 3233979
  have htrace : WordTrace (prefixWord ++ tailWord_3233979) baseStart_3233979 baseEnd_3233979 := by
    simpa [prefixWord, tailWord_3233979, baseEnd_3233979] using wordTrace_append hprefix tailTrace_3233979
  have hstable : (prefixWord ++ tailWord_3233979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233979).length < 2 ^ (prefixWord ++ tailWord_3233979).sum := by decide
  have hdescent : baseEnd_3233979 < baseStart_3233979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3233989 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 7]
def baseStart_3233989 : Nat := 118140960795 + 3233989 * 2 ^ 59
def prefixEnd_3233989 : Nat := 4983230072969 + 3 ^ 40 * 3233989 * 2
def baseEnd_3233989 : Nat := 184510087594805859651629

theorem tailTrace_3233989 : CollatzResearch.WordTrace tailWord_3233989 prefixEnd_3233989 184510087594805859651629 := by
  unfold tailWord_3233989
  simp only [CollatzResearch.WordTrace]
  refine ⟨117953269080817649193761021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78635512720545099462507347 117953269080817649193761021)
  ·
    refine ⟨44232475905306618447660383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117953269080817649193761021 44232475905306618447660383)
    ·
      refine ⟨66348713857959927671490575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44232475905306618447660383 66348713857959927671490575)
      ·
        refine ⟨99523070786939891507235863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66348713857959927671490575 99523070786939891507235863)
        ·
          refine ⟨149284606180409837260853795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99523070786939891507235863 149284606180409837260853795)
          ·
            refine ⟨223926909270614755891280693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149284606180409837260853795 223926909270614755891280693)
            ·
              refine ⟨20993147744120133364807565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 223926909270614755891280693 20993147744120133364807565)
              ·
                refine ⟨7872430404045050011802837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20993147744120133364807565 7872430404045050011802837)
                ·
                  refine ⟨184510087594805859651629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7872430404045050011802837 184510087594805859651629)
                  ·
                    rfl

theorem cell23_3233989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_3233989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3233989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3233989 prefixEnd_3233989 := by exact prefixLift 3233989
  have htrace : WordTrace (prefixWord ++ tailWord_3233989) baseStart_3233989 baseEnd_3233989 := by
    simpa [prefixWord, tailWord_3233989, baseEnd_3233989] using wordTrace_append hprefix tailTrace_3233989
  have hstable : (prefixWord ++ tailWord_3233989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3233989).length < 2 ^ (prefixWord ++ tailWord_3233989).sum := by decide
  have hdescent : baseEnd_3233989 < baseStart_3233989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3233989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234089 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 9]
def baseStart_3234089 : Nat := 118140960795 + 3234089 * 2 ^ 59
def prefixEnd_3234089 : Nat := 4983230072969 + 3 ^ 40 * 3234089 * 2
def baseEnd_3234089 : Nat := 1660642136418702345614201

theorem tailTrace_3234089 : CollatzResearch.WordTrace tailWord_3234089 prefixEnd_3234089 1660642136418702345614201 := by
  unfold tailWord_3234089
  simp only [CollatzResearch.WordTrace]
  refine ⟨117956916380455366272401321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78637944253636910848267547 117956916380455366272401321)
  ·
    refine ⟨88467687285341524704300991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117956916380455366272401321 88467687285341524704300991)
    ·
      refine ⟨132701530928012287056451487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88467687285341524704300991 132701530928012287056451487)
      ·
        refine ⟨199052296392018430584677231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132701530928012287056451487 199052296392018430584677231)
        ·
          refine ⟨298578444588027645877015847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199052296392018430584677231 298578444588027645877015847)
          ·
            refine ⟨447867666882041468815523771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298578444588027645877015847 447867666882041468815523771)
            ·
              refine ⟨671801500323062203223285657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447867666882041468815523771 671801500323062203223285657)
              ·
                refine ⟨503851125242296652417464243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671801500323062203223285657 503851125242296652417464243)
                ·
                  refine ⟨755776687863444978626196365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503851125242296652417464243 755776687863444978626196365)
                  ·
                    refine ⟨283416257948791866984823637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 755776687863444978626196365 283416257948791866984823637)
                    ·
                      refine ⟨1660642136418702345614201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 283416257948791866984823637 1660642136418702345614201)
                      ·
                        rfl

theorem cell23_3234089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 9].length) (baseStart_3234089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234089 prefixEnd_3234089 := by exact prefixLift 3234089
  have htrace : WordTrace (prefixWord ++ tailWord_3234089) baseStart_3234089 baseEnd_3234089 := by
    simpa [prefixWord, tailWord_3234089, baseEnd_3234089] using wordTrace_append hprefix tailTrace_3234089
  have hstable : (prefixWord ++ tailWord_3234089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234089).length < 2 ^ (prefixWord ++ tailWord_3234089).sum := by decide
  have hdescent : baseEnd_3234089 < baseStart_3234089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234157 : List Nat := [1, 5, 1, 1, 1, 2, 1, 6, 1, 1, 3]
def baseStart_3234157 : Nat := 118140960795 + 3234157 * 2 ^ 59
def prefixEnd_3234157 : Nat := 4983230072969 + 3 ^ 40 * 3234157 * 2
def baseEnd_3234157 : Nat := 1660677053103208079563889

theorem tailTrace_3234157 : CollatzResearch.WordTrace tailWord_3234157 prefixEnd_3234157 1660677053103208079563889 := by
  unfold tailWord_3234157
  simp only [CollatzResearch.WordTrace]
  refine ⟨117959396544209013885876725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78639597696139342590584483 117959396544209013885876725)
  ·
    refine ⟨11058693426019595051800943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117959396544209013885876725 11058693426019595051800943)
    ·
      refine ⟨16588040139029392577701415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11058693426019595051800943 16588040139029392577701415)
      ·
        refine ⟨24882060208544088866552123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16588040139029392577701415 24882060208544088866552123)
        ·
          refine ⟨37323090312816133299828185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24882060208544088866552123 37323090312816133299828185)
          ·
            refine ⟨27992317734612099974871139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37323090312816133299828185 27992317734612099974871139)
            ·
              refine ⟨41988476601918149962306709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27992317734612099974871139 41988476601918149962306709)
              ·
                refine ⟨1968209840714913279483127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41988476601918149962306709 1968209840714913279483127)
                ·
                  refine ⟨2952314761072369919224691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968209840714913279483127 2952314761072369919224691)
                  ·
                    refine ⟨4428472141608554878837037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2952314761072369919224691 4428472141608554878837037)
                    ·
                      refine ⟨1660677053103208079563889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4428472141608554878837037 1660677053103208079563889)
                      ·
                        rfl

theorem cell23_3234157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_3234157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234157 prefixEnd_3234157 := by exact prefixLift 3234157
  have htrace : WordTrace (prefixWord ++ tailWord_3234157) baseStart_3234157 baseEnd_3234157 := by
    simpa [prefixWord, tailWord_3234157, baseEnd_3234157] using wordTrace_append hprefix tailTrace_3234157
  have hstable : (prefixWord ++ tailWord_3234157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234157).length < 2 ^ (prefixWord ++ tailWord_3234157).sum := by decide
  have hdescent : baseEnd_3234157 < baseStart_3234157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234173 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_3234173 : Nat := 118140960795 + 3234173 * 2 ^ 59
def prefixEnd_3234173 : Nat := 4983230072969 + 3 ^ 40 * 3234173 * 2
def baseEnd_3234173 : Nat := 553561756264560005654605

theorem tailTrace_3234173 : CollatzResearch.WordTrace tailWord_3234173 prefixEnd_3234173 553561756264560005654605 := by
  unfold tailWord_3234173
  simp only [CollatzResearch.WordTrace]
  refine ⟨117959980112151048618459173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78639986741434032412306115 117959980112151048618459173)
  ·
    refine ⟨22117496271028321615961095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117959980112151048618459173 22117496271028321615961095)
    ·
      refine ⟨33176244406542482423941643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22117496271028321615961095 33176244406542482423941643)
      ·
        refine ⟨49764366609813723635912465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33176244406542482423941643 49764366609813723635912465)
        ·
          refine ⟨37323274957360292726934349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49764366609813723635912465 37323274957360292726934349)
          ·
            refine ⟨13996228109010109772600381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37323274957360292726934349 13996228109010109772600381)
            ·
              refine ⟨5248585540878791164725143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13996228109010109772600381 5248585540878791164725143)
              ·
                refine ⟨7872878311318186747087715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5248585540878791164725143 7872878311318186747087715)
                ·
                  refine ⟨11809317466977280120631573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7872878311318186747087715 11809317466977280120631573)
                  ·
                    refine ⟨553561756264560005654605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11809317466977280120631573 553561756264560005654605)
                    ·
                      rfl

theorem cell23_3234173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_3234173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234173 prefixEnd_3234173 := by exact prefixLift 3234173
  have htrace : WordTrace (prefixWord ++ tailWord_3234173) baseStart_3234173 baseEnd_3234173 := by
    simpa [prefixWord, tailWord_3234173, baseEnd_3234173] using wordTrace_append hprefix tailTrace_3234173
  have hstable : (prefixWord ++ tailWord_3234173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234173).length < 2 ^ (prefixWord ++ tailWord_3234173).sum := by decide
  have hdescent : baseEnd_3234173 < baseStart_3234173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234180 : List Nat := [2, 3, 2, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_3234180 : Nat := 118140960795 + 3234180 * 2 ^ 59
def prefixEnd_3234180 : Nat := 4983230072969 + 3 ^ 40 * 3234180 * 2
def baseEnd_3234180 : Nat := 1660688863158261489576283

theorem tailTrace_3234180 : CollatzResearch.WordTrace tailWord_3234180 prefixEnd_3234180 1660688863158261489576283 := by
  unfold tailWord_3234180
  simp only [CollatzResearch.WordTrace]
  refine ⟨58980117711562844406981997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78640156948750459209309329 58980117711562844406981997)
  ·
    refine ⟨22117544141836066652618249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58980117711562844406981997 22117544141836066652618249)
    ·
      refine ⟨16588158106377049989463687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22117544141836066652618249 16588158106377049989463687)
      ·
        refine ⟨24882237159565574984195531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16588158106377049989463687 24882237159565574984195531)
        ·
          refine ⟨37323355739348362476293297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24882237159565574984195531 37323355739348362476293297)
          ·
            refine ⟨27992516804511271857219973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37323355739348362476293297 27992516804511271857219973)
            ·
              refine ⟨5248596900845863473228745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27992516804511271857219973 5248596900845863473228745)
              ·
                refine ⟨3936447675634397604921559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5248596900845863473228745 3936447675634397604921559)
                ·
                  refine ⟨5904671513451596407382339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3936447675634397604921559 5904671513451596407382339)
                  ·
                    refine ⟨8857007270177394611073509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5904671513451596407382339 8857007270177394611073509)
                    ·
                      refine ⟨1660688863158261489576283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8857007270177394611073509 1660688863158261489576283)
                      ·
                        rfl

theorem cell23_3234180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_3234180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234180 prefixEnd_3234180 := by exact prefixLift 3234180
  have htrace : WordTrace (prefixWord ++ tailWord_3234180) baseStart_3234180 baseEnd_3234180 := by
    simpa [prefixWord, tailWord_3234180, baseEnd_3234180] using wordTrace_append hprefix tailTrace_3234180
  have hstable : (prefixWord ++ tailWord_3234180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234180).length < 2 ^ (prefixWord ++ tailWord_3234180).sum := by decide
  have hdescent : baseEnd_3234180 < baseStart_3234180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234190 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_3234190 : Nat := 118140960795 + 3234190 * 2 ^ 59
def prefixEnd_3234190 : Nat := 4983230072969 + 3 ^ 40 * 3234190 * 2
def baseEnd_3234190 : Nat := 553564665988268816817079

theorem tailTrace_3234190 : CollatzResearch.WordTrace tailWord_3234190 prefixEnd_3234190 553564665988268816817079 := by
  unfold tailWord_3234190
  simp only [CollatzResearch.WordTrace]
  refine ⟨14745075019136182565228503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78640400102059640347885349 14745075019136182565228503)
  ·
    refine ⟨22117612528704273847842755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14745075019136182565228503 22117612528704273847842755)
    ·
      refine ⟨33176418793056410771764133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22117612528704273847842755 33176418793056410771764133)
      ·
        refine ⟨6220578523698077019705775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33176418793056410771764133 6220578523698077019705775)
        ·
          refine ⟨9330867785547115529558663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6220578523698077019705775 9330867785547115529558663)
          ·
            refine ⟨13996301678320673294337995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9330867785547115529558663 13996301678320673294337995)
            ·
              refine ⟨20994452517481009941506993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13996301678320673294337995 20994452517481009941506993)
              ·
                refine ⟨15745839388110757456130245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20994452517481009941506993 15745839388110757456130245)
                ·
                  refine ⟨2952344885270767023024421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15745839388110757456130245 2952344885270767023024421)
                  ·
                    refine ⟨553564665988268816817079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2952344885270767023024421 553564665988268816817079)
                    ·
                      rfl

theorem cell23_3234190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_3234190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234190 prefixEnd_3234190 := by exact prefixLift 3234190
  have htrace : WordTrace (prefixWord ++ tailWord_3234190) baseStart_3234190 baseEnd_3234190 := by
    simpa [prefixWord, tailWord_3234190, baseEnd_3234190] using wordTrace_append hprefix tailTrace_3234190
  have hstable : (prefixWord ++ tailWord_3234190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234190).length < 2 ^ (prefixWord ++ tailWord_3234190).sum := by decide
  have hdescent : baseEnd_3234190 < baseStart_3234190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234200 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3234200 : Nat := 118140960795 + 3234200 * 2 ^ 59
def prefixEnd_3234200 : Nat := 4983230072969 + 3 ^ 40 * 3234200 * 2
def baseEnd_3234200 : Nat := 1660699132771351411326191

theorem tailTrace_3234200 : CollatzResearch.WordTrace tailWord_3234200 prefixEnd_3234200 1660699132771351411326191 := by
  unfold tailWord_3234200
  simp only [CollatzResearch.WordTrace]
  refine ⟨58980482441526616114846027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78640643255368821486461369 58980482441526616114846027)
  ·
    refine ⟨88470723662289924172269041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58980482441526616114846027 88470723662289924172269041)
    ·
      refine ⟨66353042746717443129201781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88470723662289924172269041 66353042746717443129201781)
      ·
        refine ⟨6220597757504760293362667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66353042746717443129201781 6220597757504760293362667)
        ·
          refine ⟨9330896636257140440044001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6220597757504760293362667 9330896636257140440044001)
          ·
            refine ⟨6998172477192855330033001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9330896636257140440044001 6998172477192855330033001)
            ·
              refine ⟨5248629357894641497524751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6998172477192855330033001 5248629357894641497524751)
              ·
                refine ⟨7872944036841962246287127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5248629357894641497524751 7872944036841962246287127)
                ·
                  refine ⟨11809416055262943369430691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7872944036841962246287127 11809416055262943369430691)
                  ·
                    refine ⟨17714124082894415054146037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11809416055262943369430691 17714124082894415054146037)
                    ·
                      refine ⟨1660699132771351411326191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17714124082894415054146037 1660699132771351411326191)
                      ·
                        rfl

theorem cell23_3234200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3234200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234200 prefixEnd_3234200 := by exact prefixLift 3234200
  have htrace : WordTrace (prefixWord ++ tailWord_3234200) baseStart_3234200 baseEnd_3234200 := by
    simpa [prefixWord, tailWord_3234200, baseEnd_3234200] using wordTrace_append hprefix tailTrace_3234200
  have hstable : (prefixWord ++ tailWord_3234200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234200).length < 2 ^ (prefixWord ++ tailWord_3234200).sum := by decide
  have hdescent : baseEnd_3234200 < baseStart_3234200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234223 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 1, 9, 2]
def baseStart_3234223 : Nat := 118140960795 + 3234223 * 2 ^ 59
def prefixEnd_3234223 : Nat := 4983230072969 + 3 ^ 40 * 3234223 * 2
def baseEnd_3234223 : Nat := 1660710942826404821338585

theorem tailTrace_3234223 : CollatzResearch.WordTrace tailWord_3234223 prefixEnd_3234223 1660710942826404821338585 := by
  unfold tailWord_3234223
  simp only [CollatzResearch.WordTrace]
  refine ⟨117961803761969907157779323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78641202507979938105186215 117961803761969907157779323)
  ·
    refine ⟨176942705642954860736668985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117961803761969907157779323 176942705642954860736668985)
    ·
      refine ⟨132707029232216145552501739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176942705642954860736668985 132707029232216145552501739)
      ·
        refine ⟨199060543848324218328752609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132707029232216145552501739 199060543848324218328752609)
        ·
          refine ⟨149295407886243163746564457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199060543848324218328752609 149295407886243163746564457)
          ·
            refine ⟨111971555914682372809923343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149295407886243163746564457 111971555914682372809923343)
            ·
              refine ⟨167957333872023559214885015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111971555914682372809923343 167957333872023559214885015)
              ·
                refine ⟨251936000808035338822327523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167957333872023559214885015 251936000808035338822327523)
                ·
                  refine ⟨377904001212053008233491285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251936000808035338822327523 377904001212053008233491285)
                  ·
                    refine ⟨2214281257101873095118113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 377904001212053008233491285 2214281257101873095118113)
                    ·
                      refine ⟨1660710942826404821338585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2214281257101873095118113 1660710942826404821338585)
                      ·
                        rfl

theorem cell23_3234223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 9, 2].length) (baseStart_3234223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234223 prefixEnd_3234223 := by exact prefixLift 3234223
  have htrace : WordTrace (prefixWord ++ tailWord_3234223) baseStart_3234223 baseEnd_3234223 := by
    simpa [prefixWord, tailWord_3234223, baseEnd_3234223] using wordTrace_append hprefix tailTrace_3234223
  have hstable : (prefixWord ++ tailWord_3234223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234223).length < 2 ^ (prefixWord ++ tailWord_3234223).sum := by decide
  have hdescent : baseEnd_3234223 < baseStart_3234223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234273 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_3234273 : Nat := 118140960795 + 3234273 * 2 ^ 59
def prefixEnd_3234273 : Nat := 4983230072969 + 3 ^ 40 * 3234273 * 2
def baseEnd_3234273 : Nat := 1660736616859129625713355

theorem tailTrace_3234273 : CollatzResearch.WordTrace tailWord_3234273 prefixEnd_3234273 1660736616859129625713355 := by
  unfold tailWord_3234273
  simp only [CollatzResearch.WordTrace]
  refine ⟨117963627411788765697099473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78642418274525843798066315 117963627411788765697099473)
  ·
    refine ⟨88472720558841574272824605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117963627411788765697099473 88472720558841574272824605)
    ·
      refine ⟨33177270209565590352309227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88472720558841574272824605 33177270209565590352309227)
      ·
        refine ⟨49765905314348385528463841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33177270209565590352309227 49765905314348385528463841)
        ·
          refine ⟨37324428985761289146347881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49765905314348385528463841 37324428985761289146347881)
          ·
            refine ⟨27993321739320966859760911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37324428985761289146347881 27993321739320966859760911)
            ·
              refine ⟨41989982608981450289641367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27993321739320966859760911 41989982608981450289641367)
              ·
                refine ⟨62984973913472175434462051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41989982608981450289641367 62984973913472175434462051)
                ·
                  refine ⟨94477460870208263151693077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62984973913472175434462051 94477460870208263151693077)
                  ·
                    refine ⟨4428630978291012335235613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94477460870208263151693077 4428630978291012335235613)
                    ·
                      refine ⟨1660736616859129625713355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4428630978291012335235613 1660736616859129625713355)
                      ·
                        rfl

theorem cell23_3234273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_3234273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234273 prefixEnd_3234273 := by exact prefixLift 3234273
  have htrace : WordTrace (prefixWord ++ tailWord_3234273) baseStart_3234273 baseEnd_3234273 := by
    simpa [prefixWord, tailWord_3234273, baseEnd_3234273] using wordTrace_append hprefix tailTrace_3234273
  have hstable : (prefixWord ++ tailWord_3234273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234273).length < 2 ^ (prefixWord ++ tailWord_3234273).sum := by decide
  have hdescent : baseEnd_3234273 < baseStart_3234273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234283 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 4]
def baseStart_3234283 : Nat := 118140960795 + 3234283 * 2 ^ 59
def prefixEnd_3234283 : Nat := 4983230072969 + 3 ^ 40 * 3234283 * 2
def baseEnd_3234283 : Nat := 1660741751665674586588309

theorem tailTrace_3234283 : CollatzResearch.WordTrace tailWord_3234283 prefixEnd_3234283 1660741751665674586588309 := by
  unfold tailWord_3234283
  simp only [CollatzResearch.WordTrace]
  refine ⟨117963992141752537404963503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78642661427835024936642335 117963992141752537404963503)
  ·
    refine ⟨176945988212628806107445255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117963992141752537404963503 176945988212628806107445255)
    ·
      refine ⟨265418982318943209161167883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176945988212628806107445255 265418982318943209161167883)
      ·
        refine ⟨398128473478414813741751825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265418982318943209161167883 398128473478414813741751825)
        ·
          refine ⟨298596355108811110306313869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398128473478414813741751825 298596355108811110306313869)
          ·
            refine ⟨111973633165804166364867701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298596355108811110306313869 111973633165804166364867701)
            ·
              refine ⟨10497528109294140596706347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111973633165804166364867701 10497528109294140596706347)
              ·
                refine ⟨15746292163941210895059521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10497528109294140596706347 15746292163941210895059521)
                ·
                  refine ⟨11809719122955908171294641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15746292163941210895059521 11809719122955908171294641)
                  ·
                    refine ⟨8857289342216931128470981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11809719122955908171294641 8857289342216931128470981)
                    ·
                      refine ⟨1660741751665674586588309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8857289342216931128470981 1660741751665674586588309)
                      ·
                        rfl

theorem cell23_3234283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 4].length) (baseStart_3234283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234283 prefixEnd_3234283 := by exact prefixLift 3234283
  have htrace : WordTrace (prefixWord ++ tailWord_3234283) baseStart_3234283 baseEnd_3234283 := by
    simpa [prefixWord, tailWord_3234283, baseEnd_3234283] using wordTrace_append hprefix tailTrace_3234283
  have hstable : (prefixWord ++ tailWord_3234283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234283).length < 2 ^ (prefixWord ++ tailWord_3234283).sum := by decide
  have hdescent : baseEnd_3234283 < baseStart_3234283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234303 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 3]
def baseStart_3234303 : Nat := 118140960795 + 3234303 * 2 ^ 59
def prefixEnd_3234303 : Nat := 4983230072969 + 3 ^ 40 * 3234303 * 2
def baseEnd_3234303 : Nat := 1660752021278764508338217

theorem tailTrace_3234303 : CollatzResearch.WordTrace tailWord_3234303 prefixEnd_3234303 1660752021278764508338217 := by
  unfold tailWord_3234303
  simp only [CollatzResearch.WordTrace]
  refine ⟨117964721601680080820691563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78643147734453387213794375 117964721601680080820691563)
  ·
    refine ⟨176947082402520121231037345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117964721601680080820691563 176947082402520121231037345)
    ·
      refine ⟨132710311801890090923278009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176947082402520121231037345 132710311801890090923278009)
      ·
        refine ⟨99532733851417568192458507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132710311801890090923278009 99532733851417568192458507)
        ·
          refine ⟨149299100777126352288687761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99532733851417568192458507 149299100777126352288687761)
          ·
            refine ⟨111974325582844764216515821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149299100777126352288687761 111974325582844764216515821)
            ·
              refine ⟨41990372093566786581193433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111974325582844764216515821 41990372093566786581193433)
              ·
                refine ⟨31492779070175089935895075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41990372093566786581193433 31492779070175089935895075)
                ·
                  refine ⟨47239168605262634903842613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31492779070175089935895075 47239168605262634903842613)
                  ·
                    refine ⟨4428672056743372022235245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47239168605262634903842613 4428672056743372022235245)
                    ·
                      refine ⟨1660752021278764508338217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4428672056743372022235245 1660752021278764508338217)
                      ·
                        rfl

theorem cell23_3234303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_3234303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234303 prefixEnd_3234303 := by exact prefixLift 3234303
  have htrace : WordTrace (prefixWord ++ tailWord_3234303) baseStart_3234303 baseEnd_3234303 := by
    simpa [prefixWord, tailWord_3234303, baseEnd_3234303] using wordTrace_append hprefix tailTrace_3234303
  have hstable : (prefixWord ++ tailWord_3234303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234303).length < 2 ^ (prefixWord ++ tailWord_3234303).sum := by decide
  have hdescent : baseEnd_3234303 < baseStart_3234303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234323 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 4, 5]
def baseStart_3234323 : Nat := 118140960795 + 3234323 * 2 ^ 59
def prefixEnd_3234323 : Nat := 4983230072969 + 3 ^ 40 * 3234323 * 2
def baseEnd_3234323 : Nat := 553587430297284810029375

theorem tailTrace_3234323 : CollatzResearch.WordTrace tailWord_3234323 prefixEnd_3234323 553587430297284810029375 := by
  unfold tailWord_3234323
  simp only [CollatzResearch.WordTrace]
  refine ⟨117965451061607624236419623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78643634041071749490946415 117965451061607624236419623)
  ·
    refine ⟨176948176592411436354629435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117965451061607624236419623 176948176592411436354629435)
    ·
      refine ⟨265422264888617154531944153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176948176592411436354629435 265422264888617154531944153)
      ·
        refine ⟨199066698666462865898958115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265422264888617154531944153 199066698666462865898958115)
        ·
          refine ⟨298600047999694298848437173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199066698666462865898958115 298600047999694298848437173)
          ·
            refine ⟨27993754499971340517040985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 298600047999694298848437173 27993754499971340517040985)
            ·
              refine ⟨20995315874978505387780739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27993754499971340517040985 20995315874978505387780739)
              ·
                refine ⟨31492973812467758081671109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20995315874978505387780739 31492973812467758081671109)
                ·
                  refine ⟨5904932589837704640313333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31492973812467758081671109 5904932589837704640313333)
                  ·
                    refine ⟨553587430297284810029375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5904932589837704640313333 553587430297284810029375)
                    ·
                      rfl

theorem cell23_3234323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 5].length) (baseStart_3234323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234323 prefixEnd_3234323 := by exact prefixLift 3234323
  have htrace : WordTrace (prefixWord ++ tailWord_3234323) baseStart_3234323 baseEnd_3234323 := by
    simpa [prefixWord, tailWord_3234323, baseEnd_3234323] using wordTrace_append hprefix tailTrace_3234323
  have hstable : (prefixWord ++ tailWord_3234323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234323).length < 2 ^ (prefixWord ++ tailWord_3234323).sum := by decide
  have hdescent : baseEnd_3234323 < baseStart_3234323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234327 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 7]
def baseStart_3234327 : Nat := 118140960795 + 3234327 * 2 ^ 59
def prefixEnd_3234327 : Nat := 4983230072969 + 3 ^ 40 * 3234327 * 2
def baseEnd_3234327 : Nat := 184529371646052490493123

theorem tailTrace_3234327 : CollatzResearch.WordTrace tailWord_3234327 prefixEnd_3234327 184529371646052490493123 := by
  unfold tailWord_3234327
  simp only [CollatzResearch.WordTrace]
  refine ⟨117965596953593132919565235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78643731302395421946376823 117965596953593132919565235)
  ·
    refine ⟨176948395430389699379347853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117965596953593132919565235 176948395430389699379347853)
    ·
      refine ⟨66355648286396137267255445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176948395430389699379347853 66355648286396137267255445)
      ·
        refine ⟨3110421013424818934402599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66355648286396137267255445 3110421013424818934402599)
        ·
          refine ⟨4665631520137228401603899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3110421013424818934402599 4665631520137228401603899)
          ·
            refine ⟨6998447280205842602405849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4665631520137228401603899 6998447280205842602405849)
            ·
              refine ⟨5248835460154381951804387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6998447280205842602405849 5248835460154381951804387)
              ·
                refine ⟨7873253190231572927706581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5248835460154381951804387 7873253190231572927706581)
                ·
                  refine ⟨184529371646052490493123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7873253190231572927706581 184529371646052490493123)
                  ·
                    rfl

theorem cell23_3234327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 7].length) (baseStart_3234327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234327 prefixEnd_3234327 := by exact prefixLift 3234327
  have htrace : WordTrace (prefixWord ++ tailWord_3234327) baseStart_3234327 baseEnd_3234327 := by
    simpa [prefixWord, tailWord_3234327, baseEnd_3234327] using wordTrace_append hprefix tailTrace_3234327
  have hstable : (prefixWord ++ tailWord_3234327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234327).length < 2 ^ (prefixWord ++ tailWord_3234327).sum := by decide
  have hdescent : baseEnd_3234327 < baseStart_3234327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234330 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2]
def baseStart_3234330 : Nat := 118140960795 + 3234330 * 2 ^ 59
def prefixEnd_3234330 : Nat := 4983230072969 + 3 ^ 40 * 3234330 * 2
def baseEnd_3234330 : Nat := 1660765885256435902700593

theorem tailTrace_3234330 : CollatzResearch.WordTrace tailWord_3234330 prefixEnd_3234330 1660765885256435902700593 := by
  unfold tailWord_3234330
  simp only [CollatzResearch.WordTrace]
  refine ⟨29491426593145566107981111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78643804248388176287949629 29491426593145566107981111)
  ·
    refine ⟨44237139889718349161971667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29491426593145566107981111 44237139889718349161971667)
    ·
      refine ⟨66355709834577523742957501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44237139889718349161971667 66355709834577523742957501)
      ·
        refine ⟨24883391187966571403609063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66355709834577523742957501 24883391187966571403609063)
        ·
          refine ⟨37325086781949857105413595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24883391187966571403609063 37325086781949857105413595)
          ·
            refine ⟨55987630172924785658120393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37325086781949857105413595 55987630172924785658120393)
            ·
              refine ⟨41990722629693589243590295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55987630172924785658120393 41990722629693589243590295)
              ·
                refine ⟨62986083944540383865385443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41990722629693589243590295 62986083944540383865385443)
                ·
                  refine ⟨94479125916810575798078165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62986083944540383865385443 94479125916810575798078165)
                  ·
                    refine ⟨2214354513675247870267457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 94479125916810575798078165 2214354513675247870267457)
                    ·
                      refine ⟨1660765885256435902700593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2214354513675247870267457 1660765885256435902700593)
                      ·
                        rfl

theorem cell23_3234330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_3234330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234330 prefixEnd_3234330 := by exact prefixLift 3234330
  have htrace : WordTrace (prefixWord ++ tailWord_3234330) baseStart_3234330 baseEnd_3234330 := by
    simpa [prefixWord, tailWord_3234330, baseEnd_3234330] using wordTrace_append hprefix tailTrace_3234330
  have hstable : (prefixWord ++ tailWord_3234330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234330).length < 2 ^ (prefixWord ++ tailWord_3234330).sum := by decide
  have hdescent : baseEnd_3234330 < baseStart_3234330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234360 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 2, 1, 4]
def baseStart_3234360 : Nat := 118140960795 + 3234360 * 2 ^ 59
def prefixEnd_3234360 : Nat := 4983230072969 + 3 ^ 40 * 3234360 * 2
def baseEnd_3234360 : Nat := 1660781289676070785325455

theorem tailTrace_3234360 : CollatzResearch.WordTrace tailWord_3234360 prefixEnd_3234360 1660781289676070785325455 := by
  unfold tailWord_3234360
  simp only [CollatzResearch.WordTrace]
  refine ⟨58983400281236789777758267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78644533708315719703677689 58983400281236789777758267)
  ·
    refine ⟨88475100421855184666637401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58983400281236789777758267 88475100421855184666637401)
    ·
      refine ⟨66356325316391388499978051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88475100421855184666637401 66356325316391388499978051)
      ·
        refine ⟨99534487974587082749967077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66356325316391388499978051 99534487974587082749967077)
        ·
          refine ⟨18662716495235078015618827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99534487974587082749967077 18662716495235078015618827)
          ·
            refine ⟨27994074742852617023428241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18662716495235078015618827 27994074742852617023428241)
            ·
              refine ⟨20995556057139462767571181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27994074742852617023428241 20995556057139462767571181)
              ·
                refine ⟨7873333521427298537839193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20995556057139462767571181 7873333521427298537839193)
                ·
                  refine ⟨5905000141070473903379395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7873333521427298537839193 5905000141070473903379395)
                  ·
                    refine ⟨8857500211605710855069093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5905000141070473903379395 8857500211605710855069093)
                    ·
                      refine ⟨1660781289676070785325455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8857500211605710855069093 1660781289676070785325455)
                      ·
                        rfl

theorem cell23_3234360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_3234360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234360 prefixEnd_3234360 := by exact prefixLift 3234360
  have htrace : WordTrace (prefixWord ++ tailWord_3234360) baseStart_3234360 baseEnd_3234360 := by
    simpa [prefixWord, tailWord_3234360, baseEnd_3234360] using wordTrace_append hprefix tailTrace_3234360
  have hstable : (prefixWord ++ tailWord_3234360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234360).length < 2 ^ (prefixWord ++ tailWord_3234360).sum := by decide
  have hdescent : baseEnd_3234360 < baseStart_3234360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234374 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_3234374 : Nat := 118140960795 + 3234374 * 2 ^ 59
def prefixEnd_3234374 : Nat := 4983230072969 + 3 ^ 40 * 3234374 * 2
def baseEnd_3234374 : Nat := 553596159468411243516797

theorem tailTrace_3234374 : CollatzResearch.WordTrace tailWord_3234374 prefixEnd_3234374 553596159468411243516797 := by
  unfold tailWord_3234374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3686478474513214373328943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78644874122948573297684117 3686478474513214373328943)
  ·
    refine ⟨5529717711769821559993415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3686478474513214373328943 5529717711769821559993415)
    ·
      refine ⟨8294576567654732339990123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5529717711769821559993415 8294576567654732339990123)
      ·
        refine ⟨12441864851482098509985185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8294576567654732339990123 12441864851482098509985185)
        ·
          refine ⟨9331398638611573882488889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12441864851482098509985185 9331398638611573882488889)
          ·
            refine ⟨6998548978958680411866667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9331398638611573882488889 6998548978958680411866667)
            ·
              refine ⟨10497823468438020617800001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6998548978958680411866667 10497823468438020617800001)
              ·
                refine ⟨7873367601328515463350001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10497823468438020617800001 7873367601328515463350001)
                ·
                  refine ⟨5905025700996386597512501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7873367601328515463350001 5905025700996386597512501)
                  ·
                    refine ⟨553596159468411243516797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5905025700996386597512501 553596159468411243516797)
                    ·
                      rfl

theorem cell23_3234374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_3234374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234374 prefixEnd_3234374 := by exact prefixLift 3234374
  have htrace : WordTrace (prefixWord ++ tailWord_3234374) baseStart_3234374 baseEnd_3234374 := by
    simpa [prefixWord, tailWord_3234374, baseEnd_3234374] using wordTrace_append hprefix tailTrace_3234374
  have hstable : (prefixWord ++ tailWord_3234374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234374).length < 2 ^ (prefixWord ++ tailWord_3234374).sum := by decide
  have hdescent : baseEnd_3234374 < baseStart_3234374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234383 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 8]
def baseStart_3234383 : Nat := 118140960795 + 3234383 * 2 ^ 59
def prefixEnd_3234383 : Nat := 4983230072969 + 3 ^ 40 * 3234383 * 2
def baseEnd_3234383 : Nat := 184532566636791577259761

theorem tailTrace_3234383 : CollatzResearch.WordTrace tailWord_3234383 prefixEnd_3234383 184532566636791577259761 := by
  unfold tailWord_3234383
  simp only [CollatzResearch.WordTrace]
  refine ⟨117967639441390254483603803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78645092960926836322402535 117967639441390254483603803)
  ·
    refine ⟨176951459162085381725405705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117967639441390254483603803 176951459162085381725405705)
    ·
      refine ⟨132713594371564036294054279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176951459162085381725405705 132713594371564036294054279)
      ·
        refine ⟨199070391557346054441081419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132713594371564036294054279 199070391557346054441081419)
        ·
          refine ⟨298605587336019081661622129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199070391557346054441081419 298605587336019081661622129)
          ·
            refine ⟨223954190502014311246216597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298605587336019081661622129 223954190502014311246216597)
            ·
              refine ⟨10497852679781920839666403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 223954190502014311246216597 10497852679781920839666403)
              ·
                refine ⟨15746779019672881259499605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10497852679781920839666403 15746779019672881259499605)
                ·
                  refine ⟨184532566636791577259761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15746779019672881259499605 184532566636791577259761)
                  ·
                    rfl

theorem cell23_3234383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 8].length) (baseStart_3234383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234383 prefixEnd_3234383 := by exact prefixLift 3234383
  have htrace : WordTrace (prefixWord ++ tailWord_3234383) baseStart_3234383 baseEnd_3234383 := by
    simpa [prefixWord, tailWord_3234383, baseEnd_3234383] using wordTrace_append hprefix tailTrace_3234383
  have hstable : (prefixWord ++ tailWord_3234383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234383).length < 2 ^ (prefixWord ++ tailWord_3234383).sum := by decide
  have hdescent : baseEnd_3234383 < baseStart_3234383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234414 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_3234414 : Nat := 118140960795 + 3234414 * 2 ^ 59
def prefixEnd_3234414 : Nat := 4983230072969 + 3 ^ 40 * 3234414 * 2
def baseEnd_3234414 : Nat := 1660809017631413574050207

theorem tailTrace_3234414 : CollatzResearch.WordTrace tailWord_3234414 prefixEnd_3234414 1660809017631413574050207 := by
  unfold tailWord_3234414
  simp only [CollatzResearch.WordTrace]
  refine ⟨14746096263034743347247787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78645846736185297851988197 14746096263034743347247787)
  ·
    refine ⟨22119144394552115020871681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14746096263034743347247787 22119144394552115020871681)
    ·
      refine ⟨16589358295914086265653761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22119144394552115020871681 16589358295914086265653761)
      ·
        refine ⟨12442018721935564699240321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16589358295914086265653761 12442018721935564699240321)
        ·
          refine ⟨9331514041451673524430241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12442018721935564699240321 9331514041451673524430241)
          ·
            refine ⟨6998635531088755143322681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9331514041451673524430241 6998635531088755143322681)
            ·
              refine ⟨5248976648316566357492011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6998635531088755143322681 5248976648316566357492011)
              ·
                refine ⟨7873464972474849536238017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5248976648316566357492011 7873464972474849536238017)
                ·
                  refine ⟨5905098729356137152178513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7873464972474849536238017 5905098729356137152178513)
                  ·
                    refine ⟨4428824047017102864133885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5905098729356137152178513 4428824047017102864133885)
                    ·
                      refine ⟨1660809017631413574050207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4428824047017102864133885 1660809017631413574050207)
                      ·
                        rfl

theorem cell23_3234414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_3234414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234414 prefixEnd_3234414 := by exact prefixLift 3234414
  have htrace : WordTrace (prefixWord ++ tailWord_3234414) baseStart_3234414 baseEnd_3234414 := by
    simpa [prefixWord, tailWord_3234414, baseEnd_3234414] using wordTrace_append hprefix tailTrace_3234414
  have hstable : (prefixWord ++ tailWord_3234414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234414).length < 2 ^ (prefixWord ++ tailWord_3234414).sum := by decide
  have hdescent : baseEnd_3234414 < baseStart_3234414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234471 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_3234471 : Nat := 118140960795 + 3234471 * 2 ^ 59
def prefixEnd_3234471 : Nat := 4983230072969 + 3 ^ 40 * 3234471 * 2
def baseEnd_3234471 : Nat := 1660838286028719851037445

theorem tailTrace_3234471 : CollatzResearch.WordTrace tailWord_3234471 prefixEnd_3234471 1660838286028719851037445 := by
  unfold tailWord_3234471
  simp only [CollatzResearch.WordTrace]
  refine ⟨117970849065071445512807267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78647232710047630341871511 117970849065071445512807267)
  ·
    refine ⟨176956273597607168269210901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117970849065071445512807267 176956273597607168269210901)
    ·
      refine ⟨8294825324887836012619261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 176956273597607168269210901 8294825324887836012619261)
      ·
        refine ⟨3110559496832938504732223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8294825324887836012619261 3110559496832938504732223)
        ·
          refine ⟨4665839245249407757098335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3110559496832938504732223 4665839245249407757098335)
          ·
            refine ⟨6998758867874111635647503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4665839245249407757098335 6998758867874111635647503)
            ·
              refine ⟨10498138301811167453471255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6998758867874111635647503 10498138301811167453471255)
              ·
                refine ⟨15747207452716751180206883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10498138301811167453471255 15747207452716751180206883)
                ·
                  refine ⟨23620811179075126770310325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15747207452716751180206883 23620811179075126770310325)
                  ·
                    refine ⟨2214451048038293134716593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23620811179075126770310325 2214451048038293134716593)
                    ·
                      refine ⟨1660838286028719851037445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2214451048038293134716593 1660838286028719851037445)
                      ·
                        rfl

theorem cell23_3234471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_3234471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234471 prefixEnd_3234471 := by exact prefixLift 3234471
  have htrace : WordTrace (prefixWord ++ tailWord_3234471) baseStart_3234471 baseEnd_3234471 := by
    simpa [prefixWord, tailWord_3234471, baseEnd_3234471] using wordTrace_append hprefix tailTrace_3234471
  have hstable : (prefixWord ++ tailWord_3234471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234471).length < 2 ^ (prefixWord ++ tailWord_3234471).sum := by decide
  have hdescent : baseEnd_3234471 < baseStart_3234471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234477 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_3234477 : Nat := 118140960795 + 3234477 * 2 ^ 59
def prefixEnd_3234477 : Nat := 4983230072969 + 3 ^ 40 * 3234477 * 2
def baseEnd_3234477 : Nat := 553613788970882275854139

theorem tailTrace_3234477 : CollatzResearch.WordTrace tailWord_3234477 prefixEnd_3234477 553613788970882275854139 := by
  unfold tailWord_3234477
  simp only [CollatzResearch.WordTrace]
  refine ⟨117971067903049708537525685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78647378602033139025017123 117971067903049708537525685)
  ·
    refine ⟨11059787615910910175393033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117971067903049708537525685 11059787615910910175393033)
    ·
      refine ⟨8294840711933182631544775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11059787615910910175393033 8294840711933182631544775)
      ·
        refine ⟨12442261067899773947317163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8294840711933182631544775 12442261067899773947317163)
        ·
          refine ⟨18663391601849660920975745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12442261067899773947317163 18663391601849660920975745)
          ·
            refine ⟨13997543701387245690731809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18663391601849660920975745 13997543701387245690731809)
            ·
              refine ⟨10498157776040434268048857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13997543701387245690731809 10498157776040434268048857)
              ·
                refine ⟨7873618332030325701036643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10498157776040434268048857 7873618332030325701036643)
                ·
                  refine ⟨11810427498045488551554965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7873618332030325701036643 11810427498045488551554965)
                  ·
                    refine ⟨553613788970882275854139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11810427498045488551554965 553613788970882275854139)
                    ·
                      rfl

theorem cell23_3234477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_3234477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234477 prefixEnd_3234477 := by exact prefixLift 3234477
  have htrace : WordTrace (prefixWord ++ tailWord_3234477) baseStart_3234477 baseEnd_3234477 := by
    simpa [prefixWord, tailWord_3234477, baseEnd_3234477] using wordTrace_append hprefix tailTrace_3234477
  have hstable : (prefixWord ++ tailWord_3234477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234477).length < 2 ^ (prefixWord ++ tailWord_3234477).sum := by decide
  have hdescent : baseEnd_3234477 < baseStart_3234477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234478 : List Nat := [4, 1, 4, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_3234478 : Nat := 118140960795 + 3234478 * 2 ^ 59
def prefixEnd_3234478 : Nat := 4983230072969 + 3 ^ 40 * 3234478 * 2
def baseEnd_3234478 : Nat := 1660841880393301323649913

theorem tailTrace_3234478 : CollatzResearch.WordTrace tailWord_3234478 prefixEnd_3234478 1660841880393301323649913 := by
  unfold tailWord_3234478
  simp only [CollatzResearch.WordTrace]
  refine ⟨14746388047005760713539011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78647402917364057138874725 14746388047005760713539011)
  ·
    refine ⟨22119582070508641070308517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14746388047005760713539011 22119582070508641070308517)
    ·
      refine ⟨4147421638220370200682847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22119582070508641070308517 4147421638220370200682847)
      ·
        refine ⟨6221132457330555301024271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4147421638220370200682847 6221132457330555301024271)
        ·
          refine ⟨9331698685995832951536407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6221132457330555301024271 9331698685995832951536407)
          ·
            refine ⟨13997548028993749427304611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9331698685995832951536407 13997548028993749427304611)
            ·
              refine ⟨20996322043490624140956917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13997548028993749427304611 20996322043490624140956917)
              ·
                refine ⟨1968405191577246013214711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20996322043490624140956917 1968405191577246013214711)
                ·
                  refine ⟨2952607787365869019822067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968405191577246013214711 2952607787365869019822067)
                  ·
                    refine ⟨4428911681048803529733101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2952607787365869019822067 4428911681048803529733101)
                    ·
                      refine ⟨1660841880393301323649913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4428911681048803529733101 1660841880393301323649913)
                      ·
                        rfl

theorem cell23_3234478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_3234478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234478 prefixEnd_3234478 := by exact prefixLift 3234478
  have htrace : WordTrace (prefixWord ++ tailWord_3234478) baseStart_3234478 baseEnd_3234478 := by
    simpa [prefixWord, tailWord_3234478, baseEnd_3234478] using wordTrace_append hprefix tailTrace_3234478
  have hstable : (prefixWord ++ tailWord_3234478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234478).length < 2 ^ (prefixWord ++ tailWord_3234478).sum := by decide
  have hdescent : baseEnd_3234478 < baseStart_3234478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234524 : List Nat := [2, 2, 5, 1, 1, 1, 4, 7]
def baseStart_3234524 : Nat := 118140960795 + 3234524 * 2 ^ 59
def prefixEnd_3234524 : Nat := 4983230072969 + 3 ^ 40 * 3234524 * 2
def baseEnd_3234524 : Nat := 61513537055681783099063

theorem tailTrace_3234524 : CollatzResearch.WordTrace tailWord_3234524 prefixEnd_3234524 61513537055681783099063 := by
  unfold tailWord_3234524
  simp only [CollatzResearch.WordTrace]
  refine ⟨58986391066939717782243313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78648521422586290376324417 58986391066939717782243313)
  ·
    refine ⟨44239793300204788336682485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58986391066939717782243313 44239793300204788336682485)
    ·
      refine ⟨4147480621894198906563983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44239793300204788336682485 4147480621894198906563983)
      ·
        refine ⟨6221220932841298359845975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4147480621894198906563983 6221220932841298359845975)
        ·
          refine ⟨9331831399261947539768963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6221220932841298359845975 9331831399261947539768963)
          ·
            refine ⟨13997747098892921309653445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9331831399261947539768963 13997747098892921309653445)
            ·
              refine ⟨2624577581042422745560021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13997747098892921309653445 2624577581042422745560021)
              ·
                refine ⟨61513537055681783099063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2624577581042422745560021 61513537055681783099063)
                ·
                  rfl

theorem cell23_3234524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 7].length) (baseStart_3234524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234524 prefixEnd_3234524 := by exact prefixLift 3234524
  have htrace : WordTrace (prefixWord ++ tailWord_3234524) baseStart_3234524 baseEnd_3234524 := by
    simpa [prefixWord, tailWord_3234524, baseEnd_3234524] using wordTrace_append hprefix tailTrace_3234524
  have hstable : (prefixWord ++ tailWord_3234524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234524).length < 2 ^ (prefixWord ++ tailWord_3234524).sum := by decide
  have hdescent : baseEnd_3234524 < baseStart_3234524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234540 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_3234540 : Nat := 118140960795 + 3234540 * 2 ^ 59
def prefixEnd_3234540 : Nat := 4983230072969 + 3 ^ 40 * 3234540 * 2
def baseEnd_3234540 : Nat := 1660873716193880081074627

theorem tailTrace_3234540 : CollatzResearch.WordTrace tailWord_3234540 prefixEnd_3234540 1660873716193880081074627 := by
  unfold tailWord_3234540
  simp only [CollatzResearch.WordTrace]
  refine ⟨58986682850910735148534537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78648910467880980198046049 58986682850910735148534537)
  ·
    refine ⟨44240012138183051361400903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58986682850910735148534537 44240012138183051361400903)
    ·
      refine ⟨66360018207274577042101355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44240012138183051361400903 66360018207274577042101355)
      ·
        refine ⟨99540027310911865563152033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66360018207274577042101355 99540027310911865563152033)
        ·
          refine ⟨74655020483183899172364025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99540027310911865563152033 74655020483183899172364025)
          ·
            refine ⟨55991265362387924379273019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74655020483183899172364025 55991265362387924379273019)
            ·
              refine ⟨83986898043581886568909529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55991265362387924379273019 83986898043581886568909529)
              ·
                refine ⟨62990173532686414926682147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83986898043581886568909529 62990173532686414926682147)
                ·
                  refine ⟨94485260299029622390023221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62990173532686414926682147 94485260299029622390023221)
                  ·
                    refine ⟨8857993153034027099064677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94485260299029622390023221 8857993153034027099064677)
                    ·
                      refine ⟨1660873716193880081074627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8857993153034027099064677 1660873716193880081074627)
                      ·
                        rfl

theorem cell23_3234540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_3234540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234540 prefixEnd_3234540 := by exact prefixLift 3234540
  have htrace : WordTrace (prefixWord ++ tailWord_3234540) baseStart_3234540 baseEnd_3234540 := by
    simpa [prefixWord, tailWord_3234540, baseEnd_3234540] using wordTrace_append hprefix tailTrace_3234540
  have hstable : (prefixWord ++ tailWord_3234540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234540).length < 2 ^ (prefixWord ++ tailWord_3234540).sum := by decide
  have hdescent : baseEnd_3234540 < baseStart_3234540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234544 : List Nat := [2, 1, 1, 1, 3, 1, 3, 5, 1, 3, 2]
def baseStart_3234544 : Nat := 118140960795 + 3234544 * 2 ^ 59
def prefixEnd_3234544 : Nat := 4983230072969 + 3 ^ 40 * 3234544 * 2
def baseEnd_3234544 : Nat := 1660875770116498065424609

theorem tailTrace_3234544 : CollatzResearch.WordTrace tailWord_3234544 prefixEnd_3234544 1660875770116498065424609 := by
  unfold tailWord_3234544
  simp only [CollatzResearch.WordTrace]
  refine ⟨58986755796903489490107343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78649007729204652653476457 58986755796903489490107343)
  ·
    refine ⟨88480133695355234235161015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58986755796903489490107343 88480133695355234235161015)
    ·
      refine ⟨132720200543032851352741523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88480133695355234235161015 132720200543032851352741523)
      ·
        refine ⟨199080300814549277029112285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132720200543032851352741523 199080300814549277029112285)
        ·
          refine ⟨74655112805455978885917107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199080300814549277029112285 74655112805455978885917107)
          ·
            refine ⟨111982669208183968328875661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74655112805455978885917107 111982669208183968328875661)
            ·
              refine ⟨41993500953068988123328373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111982669208183968328875661 41993500953068988123328373)
              ·
                refine ⟨3936890714350217636562035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41993500953068988123328373 3936890714350217636562035)
                ·
                  refine ⟨5905336071525326454843053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3936890714350217636562035 5905336071525326454843053)
                  ·
                    refine ⟨2214501026821997420566145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5905336071525326454843053 2214501026821997420566145)
                    ·
                      refine ⟨1660875770116498065424609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2214501026821997420566145 1660875770116498065424609)
                      ·
                        rfl

theorem cell23_3234544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 1, 3, 2].length) (baseStart_3234544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234544 prefixEnd_3234544 := by exact prefixLift 3234544
  have htrace : WordTrace (prefixWord ++ tailWord_3234544) baseStart_3234544 baseEnd_3234544 := by
    simpa [prefixWord, tailWord_3234544, baseEnd_3234544] using wordTrace_append hprefix tailTrace_3234544
  have hstable : (prefixWord ++ tailWord_3234544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234544).length < 2 ^ (prefixWord ++ tailWord_3234544).sum := by decide
  have hdescent : baseEnd_3234544 < baseStart_3234544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234560 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 5]
def baseStart_3234560 : Nat := 118140960795 + 3234560 * 2 ^ 59
def prefixEnd_3234560 : Nat := 4983230072969 + 3 ^ 40 * 3234560 * 2
def baseEnd_3234560 : Nat := 1660883985806970002824535

theorem tailTrace_3234560 : CollatzResearch.WordTrace tailWord_3234560 prefixEnd_3234560 1660883985806970002824535 := by
  unfold tailWord_3234560
  simp only [CollatzResearch.WordTrace]
  refine ⟨58987047580874506856398567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78649396774499342475198089 58987047580874506856398567)
  ·
    refine ⟨88480571371311760284597851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58987047580874506856398567 88480571371311760284597851)
    ·
      refine ⟨132720857056967640426896777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88480571371311760284597851 132720857056967640426896777)
      ·
        refine ⟨99540642792725730320172583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132720857056967640426896777 99540642792725730320172583)
        ·
          refine ⟨149310964189088595480258875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99540642792725730320172583 149310964189088595480258875)
          ·
            refine ⟨223966446283632893220388313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149310964189088595480258875 223966446283632893220388313)
            ·
              refine ⟨167974834712724669915291235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223966446283632893220388313 167974834712724669915291235)
              ·
                refine ⟨251962252069087004872936853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167974834712724669915291235 251962252069087004872936853)
                ·
                  refine ⟨11810730565738453353418915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 251962252069087004872936853 11810730565738453353418915)
                  ·
                    refine ⟨17716095848607680030128373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11810730565738453353418915 17716095848607680030128373)
                    ·
                      refine ⟨1660883985806970002824535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17716095848607680030128373 1660883985806970002824535)
                      ·
                        rfl

theorem cell23_3234560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_3234560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234560 prefixEnd_3234560 := by exact prefixLift 3234560
  have htrace : WordTrace (prefixWord ++ tailWord_3234560) baseStart_3234560 baseEnd_3234560 := by
    simpa [prefixWord, tailWord_3234560, baseEnd_3234560] using wordTrace_append hprefix tailTrace_3234560
  have hstable : (prefixWord ++ tailWord_3234560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234560).length < 2 ^ (prefixWord ++ tailWord_3234560).sum := by decide
  have hdescent : baseEnd_3234560 < baseStart_3234560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234568 : List Nat := [2, 1, 3, 2, 2, 4, 2, 1, 2, 1, 3]
def baseStart_3234568 : Nat := 118140960795 + 3234568 * 2 ^ 59
def prefixEnd_3234568 : Nat := 4983230072969 + 3 ^ 40 * 3234568 * 2
def baseEnd_3234568 : Nat := 1660888093652205971524499

theorem tailTrace_3234568 : CollatzResearch.WordTrace tailWord_3234568 prefixEnd_3234568 1660888093652205971524499 := by
  unfold tailWord_3234568
  simp only [CollatzResearch.WordTrace]
  refine ⟨58987193472860015539544179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78649591297146687386058905 58987193472860015539544179)
  ·
    refine ⟨88480790209290023309316269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58987193472860015539544179 88480790209290023309316269)
    ·
      refine ⟨33180296328483758740993601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88480790209290023309316269 33180296328483758740993601)
      ·
        refine ⟨24885222246362819055745201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33180296328483758740993601 24885222246362819055745201)
        ·
          refine ⟨18663916684772114291808901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24885222246362819055745201 18663916684772114291808901)
          ·
            refine ⟨3499484378394771429714169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18663916684772114291808901 3499484378394771429714169)
            ·
              refine ⟨2624613283796078572285627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3499484378394771429714169 2624613283796078572285627)
              ·
                refine ⟨3936919925694117858428441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2624613283796078572285627 3936919925694117858428441)
                ·
                  refine ⟨2952689944270588393821331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3936919925694117858428441 2952689944270588393821331)
                  ·
                    refine ⟨4429034916405882590731997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2952689944270588393821331 4429034916405882590731997)
                    ·
                      refine ⟨1660888093652205971524499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4429034916405882590731997 1660888093652205971524499)
                      ·
                        rfl

theorem cell23_3234568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_3234568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234568 prefixEnd_3234568 := by exact prefixLift 3234568
  have htrace : WordTrace (prefixWord ++ tailWord_3234568) baseStart_3234568 baseEnd_3234568 := by
    simpa [prefixWord, tailWord_3234568, baseEnd_3234568] using wordTrace_append hprefix tailTrace_3234568
  have hstable : (prefixWord ++ tailWord_3234568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234568).length < 2 ^ (prefixWord ++ tailWord_3234568).sum := by decide
  have hdescent : baseEnd_3234568 < baseStart_3234568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234574 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2]
def baseStart_3234574 : Nat := 118140960795 + 3234574 * 2 ^ 59
def prefixEnd_3234574 : Nat := 4983230072969 + 3 ^ 40 * 3234574 * 2
def baseEnd_3234574 : Nat := 1660891174536132948049471

theorem tailTrace_3234574 : CollatzResearch.WordTrace tailWord_3234574 prefixEnd_3234574 1660891174536132948049471 := by
  unfold tailWord_3234574
  simp only [CollatzResearch.WordTrace]
  refine ⟨14746825722962286762975847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78649737189132196069204517 14746825722962286762975847)
  ·
    refine ⟨22120238584443430144463771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14746825722962286762975847 22120238584443430144463771)
    ·
      refine ⟨33180357876665145216695657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22120238584443430144463771 33180357876665145216695657)
      ·
        refine ⟨24885268407498858912521743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33180357876665145216695657 24885268407498858912521743)
        ·
          refine ⟨37327902611248288368782615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24885268407498858912521743 37327902611248288368782615)
          ·
            refine ⟨55991853916872432553173923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37327902611248288368782615 55991853916872432553173923)
            ·
              refine ⟨83987780875308648829760885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55991853916872432553173923 83987780875308648829760885)
              ·
                refine ⟨7873854457060185827790083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83987780875308648829760885 7873854457060185827790083)
                ·
                  refine ⟨11810781685590278741685125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7873854457060185827790083 11810781685590278741685125)
                  ·
                    refine ⟨2214521566048177264065961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11810781685590278741685125 2214521566048177264065961)
                    ·
                      refine ⟨1660891174536132948049471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2214521566048177264065961 1660891174536132948049471)
                      ·
                        rfl

theorem cell23_3234574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_3234574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234574 prefixEnd_3234574 := by exact prefixLift 3234574
  have htrace : WordTrace (prefixWord ++ tailWord_3234574) baseStart_3234574 baseEnd_3234574 := by
    simpa [prefixWord, tailWord_3234574, baseEnd_3234574] using wordTrace_append hprefix tailTrace_3234574
  have hstable : (prefixWord ++ tailWord_3234574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234574).length < 2 ^ (prefixWord ++ tailWord_3234574).sum := by decide
  have hdescent : baseEnd_3234574 < baseStart_3234574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234578 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_3234578 : Nat := 118140960795 + 3234578 * 2 ^ 59
def prefixEnd_3234578 : Nat := 4983230072969 + 3 ^ 40 * 3234578 * 2
def baseEnd_3234578 : Nat := 1660893228458750932399453

theorem tailTrace_3234578 : CollatzResearch.WordTrace tailWord_3234578 prefixEnd_3234578 1660893228458750932399453 := by
  unfold tailWord_3234578
  simp only [CollatzResearch.WordTrace]
  refine ⟨29493687918920950696738097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78649834450455868524634925 29493687918920950696738097)
  ·
    refine ⟨22120265939190713022553573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29493687918920950696738097 22120265939190713022553573)
    ·
      refine ⟨4147549863598258691728795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22120265939190713022553573 4147549863598258691728795)
      ·
        refine ⟨6221324795397388037593193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4147549863598258691728795 6221324795397388037593193)
        ·
          refine ⟨4665993596548041028194895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6221324795397388037593193 4665993596548041028194895)
          ·
            refine ⟨6998990394822061542292343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4665993596548041028194895 6998990394822061542292343)
            ·
              refine ⟨10498485592233092313438515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6998990394822061542292343 10498485592233092313438515)
              ·
                refine ⟨15747728388349638470157773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10498485592233092313438515 15747728388349638470157773)
                ·
                  refine ⟨5905398145631114426309165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15747728388349638470157773 5905398145631114426309165)
                  ·
                    refine ⟨2214524304611667909865937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5905398145631114426309165 2214524304611667909865937)
                    ·
                      refine ⟨1660893228458750932399453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2214524304611667909865937 1660893228458750932399453)
                      ·
                        rfl

theorem cell23_3234578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_3234578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234578 prefixEnd_3234578 := by exact prefixLift 3234578
  have htrace : WordTrace (prefixWord ++ tailWord_3234578) baseStart_3234578 baseEnd_3234578 := by
    simpa [prefixWord, tailWord_3234578, baseEnd_3234578] using wordTrace_append hprefix tailTrace_3234578
  have hstable : (prefixWord ++ tailWord_3234578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234578).length < 2 ^ (prefixWord ++ tailWord_3234578).sum := by decide
  have hdescent : baseEnd_3234578 < baseStart_3234578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234644 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_3234644 : Nat := 118140960795 + 3234644 * 2 ^ 59
def prefixEnd_3234644 : Nat := 4983230072969 + 3 ^ 40 * 3234644 * 2
def baseEnd_3234644 : Nat := 553642372727315891391383

theorem tailTrace_3234644 : CollatzResearch.WordTrace tailWord_3234644 prefixEnd_3234644 553642372727315891391383 := by
  unfold tailWord_3234644
  simp only [CollatzResearch.WordTrace]
  refine ⟨58988579446722348029427493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78651439262296464039236657 58988579446722348029427493)
  ·
    refine ⟨11060358646260440255517655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58988579446722348029427493 11060358646260440255517655)
    ·
      refine ⟨16590537969390660383276483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11060358646260440255517655 16590537969390660383276483)
      ·
        refine ⟨24885806954085990574914725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16590537969390660383276483 24885806954085990574914725)
        ·
          refine ⟨4666088803891123232796511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24885806954085990574914725 4666088803891123232796511)
          ·
            refine ⟨6999133205836684849194767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4666088803891123232796511 6999133205836684849194767)
            ·
              refine ⟨10498699808755027273792151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6999133205836684849194767 10498699808755027273792151)
              ·
                refine ⟨15748049713132540910688227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10498699808755027273792151 15748049713132540910688227)
                ·
                  refine ⟨23622074569698811366032341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15748049713132540910688227 23622074569698811366032341)
                  ·
                    refine ⟨553642372727315891391383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23622074569698811366032341 553642372727315891391383)
                    ·
                      rfl

theorem cell23_3234644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_3234644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234644 prefixEnd_3234644 := by exact prefixLift 3234644
  have htrace : WordTrace (prefixWord ++ tailWord_3234644) baseStart_3234644 baseEnd_3234644 := by
    simpa [prefixWord, tailWord_3234644, baseEnd_3234644] using wordTrace_append hprefix tailTrace_3234644
  have hstable : (prefixWord ++ tailWord_3234644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234644).length < 2 ^ (prefixWord ++ tailWord_3234644).sum := by decide
  have hdescent : baseEnd_3234644 < baseStart_3234644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234674 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_3234674 : Nat := 118140960795 + 3234674 * 2 ^ 59
def prefixEnd_3234674 : Nat := 4983230072969 + 3 ^ 40 * 3234674 * 2
def baseEnd_3234674 : Nat := 553647507533860852266337

theorem tailTrace_3234674 : CollatzResearch.WordTrace tailWord_3234674 prefixEnd_3234674 553647507533860852266337 := by
  unfold tailWord_3234674
  simp only [CollatzResearch.WordTrace]
  refine ⟨29494563270834002795611769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78652168722224007454964717 29494563270834002795611769)
  ·
    refine ⟨22120922453125502096708827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29494563270834002795611769 22120922453125502096708827)
    ·
      refine ⟨33181383679688253145063241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22120922453125502096708827 33181383679688253145063241)
      ·
        refine ⟨24886037759766189858797431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33181383679688253145063241 24886037759766189858797431)
        ·
          refine ⟨37329056639649284788196147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24886037759766189858797431 37329056639649284788196147)
          ·
            refine ⟨55993584959473927182294221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37329056639649284788196147 55993584959473927182294221)
            ·
              refine ⟨20997594359802722693360333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55993584959473927182294221 20997594359802722693360333)
              ·
                refine ⟨7874097884926021010010125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20997594359802722693360333 7874097884926021010010125)
                ·
                  refine ⟨2952786706847257878753797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7874097884926021010010125 2952786706847257878753797)
                  ·
                    refine ⟨553647507533860852266337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2952786706847257878753797 553647507533860852266337)
                    ·
                      rfl

theorem cell23_3234674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_3234674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234674 prefixEnd_3234674 := by exact prefixLift 3234674
  have htrace : WordTrace (prefixWord ++ tailWord_3234674) baseStart_3234674 baseEnd_3234674 := by
    simpa [prefixWord, tailWord_3234674, baseEnd_3234674] using wordTrace_append hprefix tailTrace_3234674
  have hstable : (prefixWord ++ tailWord_3234674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234674).length < 2 ^ (prefixWord ++ tailWord_3234674).sum := by decide
  have hdescent : baseEnd_3234674 < baseStart_3234674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234687 : List Nat := [1, 1, 2, 2, 1, 1, 4, 5, 6]
def baseStart_3234687 : Nat := 118140960795 + 3234687 * 2 ^ 59
def prefixEnd_3234687 : Nat := 4983230072969 + 3 ^ 40 * 3234687 * 2
def baseEnd_3234687 : Nat := 184549910872232333992939

theorem tailTrace_3234687 : CollatzResearch.WordTrace tailWord_3234687 prefixEnd_3234687 184549910872232333992939 := by
  unfold tailWord_3234687
  simp only [CollatzResearch.WordTrace]
  refine ⟨117978727232288914402670315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78652484821525942935113543 117978727232288914402670315)
  ·
    refine ⟨176968090848433371604005473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117978727232288914402670315 176968090848433371604005473)
    ·
      refine ⟨132726068136325028703004105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176968090848433371604005473 132726068136325028703004105)
      ·
        refine ⟨99544551102243771527253079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132726068136325028703004105 99544551102243771527253079)
        ·
          refine ⟨149316826653365657290879619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99544551102243771527253079 149316826653365657290879619)
          ·
            refine ⟨223975239980048485936319429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149316826653365657290879619 223975239980048485936319429)
            ·
              refine ⟨41995357496259091113059893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223975239980048485936319429 41995357496259091113059893)
              ·
                refine ⟨3937064765274289791849365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41995357496259091113059893 3937064765274289791849365)
                ·
                  refine ⟨184549910872232333992939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3937064765274289791849365 184549910872232333992939)
                  ·
                    rfl

theorem cell23_3234687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 6].length) (baseStart_3234687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234687 prefixEnd_3234687 := by exact prefixLift 3234687
  have htrace : WordTrace (prefixWord ++ tailWord_3234687) baseStart_3234687 baseEnd_3234687 := by
    simpa [prefixWord, tailWord_3234687, baseEnd_3234687] using wordTrace_append hprefix tailTrace_3234687
  have hstable : (prefixWord ++ tailWord_3234687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234687).length < 2 ^ (prefixWord ++ tailWord_3234687).sum := by decide
  have hdescent : baseEnd_3234687 < baseStart_3234687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234741 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_3234741 : Nat := 118140960795 + 3234741 * 2 ^ 59
def prefixEnd_3234741 : Nat := 4983230072969 + 3 ^ 40 * 3234741 * 2
def baseEnd_3234741 : Nat := 1660976925805433794661203

theorem tailTrace_3234741 : CollatzResearch.WordTrace tailWord_3234741 prefixEnd_3234741 1660976925805433794661203 := by
  unfold tailWord_3234741
  simp only [CollatzResearch.WordTrace]
  refine ⟨117980696774093281625136077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78653797849395521083424051 117980696774093281625136077)
  ·
    refine ⟨44242761290284980609426029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117980696774093281625136077 44242761290284980609426029)
    ·
      refine ⟨16591035483856867728534761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44242761290284980609426029 16591035483856867728534761)
      ·
        refine ⟨12443276612892650796401071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16591035483856867728534761 12443276612892650796401071)
        ·
          refine ⟨18664914919338976194601607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12443276612892650796401071 18664914919338976194601607)
          ·
            refine ⟨27997372379008464291902411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18664914919338976194601607 27997372379008464291902411)
            ·
              refine ⟨41996058568512696437853617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27997372379008464291902411 41996058568512696437853617)
              ·
                refine ⟨31497043926384522328390213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41996058568512696437853617 31497043926384522328390213)
                ·
                  refine ⟨5905695736197097936573165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31497043926384522328390213 5905695736197097936573165)
                  ·
                    refine ⟨2214635901073911726214937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5905695736197097936573165 2214635901073911726214937)
                    ·
                      refine ⟨1660976925805433794661203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2214635901073911726214937 1660976925805433794661203)
                      ·
                        rfl

theorem cell23_3234741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_3234741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234741 prefixEnd_3234741 := by exact prefixLift 3234741
  have htrace : WordTrace (prefixWord ++ tailWord_3234741) baseStart_3234741 baseEnd_3234741 := by
    simpa [prefixWord, tailWord_3234741, baseEnd_3234741] using wordTrace_append hprefix tailTrace_3234741
  have hstable : (prefixWord ++ tailWord_3234741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234741).length < 2 ^ (prefixWord ++ tailWord_3234741).sum := by decide
  have hdescent : baseEnd_3234741 < baseStart_3234741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234764 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 1, 6]
def baseStart_3234764 : Nat := 118140960795 + 3234764 * 2 ^ 59
def prefixEnd_3234764 : Nat := 4983230072969 + 3 ^ 40 * 3234764 * 2
def baseEnd_3234764 : Nat := 553662911953495734891199

theorem tailTrace_3234764 : CollatzResearch.WordTrace tailWord_3234764 prefixEnd_3234764 553662911953495734891199 := by
  unfold tailWord_3234764
  simp only [CollatzResearch.WordTrace]
  refine ⟨58990767826504978276611673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78654357102006637702148897 58990767826504978276611673)
  ·
    refine ⟨44243075869878733707458755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58990767826504978276611673 44243075869878733707458755)
    ·
      refine ⟨66364613804818100561188133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44243075869878733707458755 66364613804818100561188133)
      ·
        refine ⟨12443365088403393855222775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66364613804818100561188133 12443365088403393855222775)
        ·
          refine ⟨18665047632605090782834163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12443365088403393855222775 18665047632605090782834163)
          ·
            refine ⟨27997571448907636174251245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18665047632605090782834163 27997571448907636174251245)
            ·
              refine ⟨10499089293340363565344217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27997571448907636174251245 10499089293340363565344217)
              ·
                refine ⟨7874316970005272674008163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10499089293340363565344217 7874316970005272674008163)
                ·
                  refine ⟨11811475455007909011012245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7874316970005272674008163 11811475455007909011012245)
                  ·
                    refine ⟨553662911953495734891199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11811475455007909011012245 553662911953495734891199)
                    ·
                      rfl

theorem cell23_3234764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_3234764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234764 prefixEnd_3234764 := by exact prefixLift 3234764
  have htrace : WordTrace (prefixWord ++ tailWord_3234764) baseStart_3234764 baseEnd_3234764 := by
    simpa [prefixWord, tailWord_3234764, baseEnd_3234764] using wordTrace_append hprefix tailTrace_3234764
  have hstable : (prefixWord ++ tailWord_3234764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234764).length < 2 ^ (prefixWord ++ tailWord_3234764).sum := by decide
  have hdescent : baseEnd_3234764 < baseStart_3234764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234777 : List Nat := [1, 2, 1, 2, 5, 12]
def baseStart_3234777 : Nat := 118140960795 + 3234777 * 2 ^ 59
def prefixEnd_3234777 : Nat := 4983230072969 + 3 ^ 40 * 3234777 * 2
def baseEnd_3234777 : Nat := 6835372062176936846959

theorem tailTrace_3234777 : CollatzResearch.WordTrace tailWord_3234777 prefixEnd_3234777 6835372062176936846959 := by
  unfold tailWord_3234777
  simp only [CollatzResearch.WordTrace]
  refine ⟨117982009801962859773446585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78654673201308573182297723 117982009801962859773446585)
  ·
    refine ⟨88486507351472144830084939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117982009801962859773446585 88486507351472144830084939)
    ·
      refine ⟨132729761027208217245127409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88486507351472144830084939 132729761027208217245127409)
      ·
        refine ⟨99547320770406162933845557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132729761027208217245127409 99547320770406162933845557)
        ·
          refine ⟨9332561322225577775048021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99547320770406162933845557 9332561322225577775048021)
          ·
            refine ⟨6835372062176936846959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9332561322225577775048021 6835372062176936846959)
            ·
              rfl

theorem cell23_3234777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 12].length) (baseStart_3234777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234777 prefixEnd_3234777 := by exact prefixLift 3234777
  have htrace : WordTrace (prefixWord ++ tailWord_3234777) baseStart_3234777 baseEnd_3234777 := by
    simpa [prefixWord, tailWord_3234777, baseEnd_3234777] using wordTrace_append hprefix tailTrace_3234777
  have hstable : (prefixWord ++ tailWord_3234777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234777).length < 2 ^ (prefixWord ++ tailWord_3234777).sum := by decide
  have hdescent : baseEnd_3234777 < baseStart_3234777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234791 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3234791 : Nat := 118140960795 + 3234791 * 2 ^ 59
def prefixEnd_3234791 : Nat := 4983230072969 + 3 ^ 40 * 3234791 * 2
def baseEnd_3234791 : Nat := 1661002599838158599035973

theorem tailTrace_3234791 : CollatzResearch.WordTrace tailWord_3234791 prefixEnd_3234791 1661002599838158599035973 := by
  unfold tailWord_3234791
  simp only [CollatzResearch.WordTrace]
  refine ⟨117982520423912140164456227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78655013615941426776304151 117982520423912140164456227)
  ·
    refine ⟨176973780635868210246684341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117982520423912140164456227 176973780635868210246684341)
    ·
      refine ⟨16591291934612644710626657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 176973780635868210246684341 16591291934612644710626657)
      ·
        refine ⟨12443468950959483532969993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16591291934612644710626657 12443468950959483532969993)
        ·
          refine ⟨9332601713219612649727495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12443468950959483532969993 9332601713219612649727495)
          ·
            refine ⟨13998902569829418974591243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9332601713219612649727495 13998902569829418974591243)
            ·
              refine ⟨20998353854744128461886865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13998902569829418974591243 20998353854744128461886865)
              ·
                refine ⟨15748765391058096346415149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20998353854744128461886865 15748765391058096346415149)
                ·
                  refine ⟨5905787021646786129905681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15748765391058096346415149 5905787021646786129905681)
                  ·
                    refine ⟨4429340266235089597429261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5905787021646786129905681 4429340266235089597429261)
                    ·
                      refine ⟨1661002599838158599035973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4429340266235089597429261 1661002599838158599035973)
                      ·
                        rfl

theorem cell23_3234791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3234791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234791 prefixEnd_3234791 := by exact prefixLift 3234791
  have htrace : WordTrace (prefixWord ++ tailWord_3234791) baseStart_3234791 baseEnd_3234791 := by
    simpa [prefixWord, tailWord_3234791, baseEnd_3234791] using wordTrace_append hprefix tailTrace_3234791
  have hstable : (prefixWord ++ tailWord_3234791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234791).length < 2 ^ (prefixWord ++ tailWord_3234791).sum := by decide
  have hdescent : baseEnd_3234791 < baseStart_3234791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234794 : List Nat := [3, 1, 3, 1, 2, 2, 3, 8]
def baseStart_3234794 : Nat := 118140960795 + 3234794 * 2 ^ 59
def prefixEnd_3234794 : Nat := 4983230072969 + 3 ^ 40 * 3234794 * 2
def baseEnd_3234794 : Nat := 61518671862226743974017

theorem tailTrace_3234794 : CollatzResearch.WordTrace tailWord_3234794 prefixEnd_3234794 61518671862226743974017 := by
  unfold tailWord_3234794
  simp only [CollatzResearch.WordTrace]
  refine ⟨29495657460725317919203859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78655086561934181117876957 29495657460725317919203859)
  ·
    refine ⟨44243486191087976878805789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29495657460725317919203859 44243486191087976878805789)
    ·
      refine ⟨16591307321657991329552171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44243486191087976878805789 16591307321657991329552171)
      ·
        refine ⟨24886960982486986994328257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16591307321657991329552171 24886960982486986994328257)
        ·
          refine ⟨18665220736865240245746193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24886960982486986994328257 18665220736865240245746193)
          ·
            refine ⟨13998915552648930184309645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18665220736865240245746193 13998915552648930184309645)
            ·
              refine ⟨5249593332243348819116117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13998915552648930184309645 5249593332243348819116117)
              ·
                refine ⟨61518671862226743974017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5249593332243348819116117 61518671862226743974017)
                ·
                  rfl

theorem cell23_3234794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 8].length) (baseStart_3234794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234794 prefixEnd_3234794 := by exact prefixLift 3234794
  have htrace : WordTrace (prefixWord ++ tailWord_3234794) baseStart_3234794 baseEnd_3234794 := by
    simpa [prefixWord, tailWord_3234794, baseEnd_3234794] using wordTrace_append hprefix tailTrace_3234794
  have hstable : (prefixWord ++ tailWord_3234794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234794).length < 2 ^ (prefixWord ++ tailWord_3234794).sum := by decide
  have hdescent : baseEnd_3234794 < baseStart_3234794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234801 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 1, 2, 4]
def baseStart_3234801 : Nat := 118140960795 + 3234801 * 2 ^ 59
def prefixEnd_3234801 : Nat := 4983230072969 + 3 ^ 40 * 3234801 * 2
def baseEnd_3234801 : Nat := 1661007734644703559910927

theorem tailTrace_3234801 : CollatzResearch.WordTrace tailWord_3234801 prefixEnd_3234801 1661007734644703559910927 := by
  unfold tailWord_3234801
  simp only [CollatzResearch.WordTrace]
  refine ⟨117982885153875911872320257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78655256769250607914880171 117982885153875911872320257)
  ·
    refine ⟨88487163865406933904240193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117982885153875911872320257 88487163865406933904240193)
    ·
      refine ⟨66365372899055200428180145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88487163865406933904240193 66365372899055200428180145)
      ·
        refine ⟨49774029674291400321135109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66365372899055200428180145 49774029674291400321135109)
        ·
          refine ⟨9332630563929637560212833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49774029674291400321135109 9332630563929637560212833)
          ·
            refine ⟨6999472922947228170159625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9332630563929637560212833 6999472922947228170159625)
            ·
              refine ⟨5249604692210421127619719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6999472922947228170159625 5249604692210421127619719)
              ·
                refine ⟨7874407038315631691429579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5249604692210421127619719 7874407038315631691429579)
                ·
                  refine ⟨11811610557473447537144369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7874407038315631691429579 11811610557473447537144369)
                  ·
                    refine ⟨8858707918105085652858277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11811610557473447537144369 8858707918105085652858277)
                    ·
                      refine ⟨1661007734644703559910927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8858707918105085652858277 1661007734644703559910927)
                      ·
                        rfl

theorem cell23_3234801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_3234801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234801 prefixEnd_3234801 := by exact prefixLift 3234801
  have htrace : WordTrace (prefixWord ++ tailWord_3234801) baseStart_3234801 baseEnd_3234801 := by
    simpa [prefixWord, tailWord_3234801, baseEnd_3234801] using wordTrace_append hprefix tailTrace_3234801
  have hstable : (prefixWord ++ tailWord_3234801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234801).length < 2 ^ (prefixWord ++ tailWord_3234801).sum := by decide
  have hdescent : baseEnd_3234801 < baseStart_3234801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234821 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 4, 1, 3]
def baseStart_3234821 : Nat := 118140960795 + 3234821 * 2 ^ 59
def prefixEnd_3234821 : Nat := 4983230072969 + 3 ^ 40 * 3234821 * 2
def baseEnd_3234821 : Nat := 1661018004257793481660835

theorem tailTrace_3234821 : CollatzResearch.WordTrace tailWord_3234821 prefixEnd_3234821 1661018004257793481660835 := by
  unfold tailWord_3234821
  simp only [CollatzResearch.WordTrace]
  refine ⟨117983614613803455288048317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78655743075868970192032211 117983614613803455288048317)
  ·
    refine ⟨44243855480176295733018119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117983614613803455288048317 44243855480176295733018119)
    ·
      refine ⟨66365783220264443599527179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44243855480176295733018119 66365783220264443599527179)
      ·
        refine ⟨99548674830396665399290769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66365783220264443599527179 99548674830396665399290769)
        ·
          refine ⟨74661506122797499049468077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99548674830396665399290769 74661506122797499049468077)
          ·
            refine ⟨27998064796049062143550529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74661506122797499049468077 27998064796049062143550529)
            ·
              refine ⟨20998548597036796607662897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27998064796049062143550529 20998548597036796607662897)
              ·
                refine ⟨15748911447777597455747173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20998548597036796607662897 15748911447777597455747173)
                ·
                  refine ⟨2952920896458299522952595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15748911447777597455747173 2952920896458299522952595)
                  ·
                    refine ⟨4429381344687449284428893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2952920896458299522952595 4429381344687449284428893)
                    ·
                      refine ⟨1661018004257793481660835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4429381344687449284428893 1661018004257793481660835)
                      ·
                        rfl

theorem cell23_3234821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_3234821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234821 prefixEnd_3234821 := by exact prefixLift 3234821
  have htrace : WordTrace (prefixWord ++ tailWord_3234821) baseStart_3234821 baseEnd_3234821 := by
    simpa [prefixWord, tailWord_3234821, baseEnd_3234821] using wordTrace_append hprefix tailTrace_3234821
  have hstable : (prefixWord ++ tailWord_3234821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234821).length < 2 ^ (prefixWord ++ tailWord_3234821).sum := by decide
  have hdescent : baseEnd_3234821 < baseStart_3234821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234855 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_3234855 : Nat := 118140960795 + 3234855 * 2 ^ 59
def prefixEnd_3234855 : Nat := 4983230072969 + 3 ^ 40 * 3234855 * 2
def baseEnd_3234855 : Nat := 1661035462600046348635679

theorem tailTrace_3234855 : CollatzResearch.WordTrace tailWord_3234855 prefixEnd_3234855 1661035462600046348635679 := by
  unfold tailWord_3234855
  simp only [CollatzResearch.WordTrace]
  refine ⟨117984854695680279094786019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78656569797120186063190679 117984854695680279094786019)
  ·
    refine ⟨176977282043520418642179029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117984854695680279094786019 176977282043520418642179029)
    ·
      refine ⟨4147905047895009811926071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 176977282043520418642179029 4147905047895009811926071)
      ·
        refine ⟨6221857571842514717889107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4147905047895009811926071 6221857571842514717889107)
        ·
          refine ⟨9332786357763772076833661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6221857571842514717889107 9332786357763772076833661)
          ·
            refine ⟨3499794884161414528812623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9332786357763772076833661 3499794884161414528812623)
            ·
              refine ⟨5249692326242121793218935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3499794884161414528812623 5249692326242121793218935)
              ·
                refine ⟨7874538489363182689828403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5249692326242121793218935 7874538489363182689828403)
                ·
                  refine ⟨11811807734044774034742605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7874538489363182689828403 11811807734044774034742605)
                  ·
                    refine ⟨4429427900266790263028477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11811807734044774034742605 4429427900266790263028477)
                    ·
                      refine ⟨1661035462600046348635679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4429427900266790263028477 1661035462600046348635679)
                      ·
                        rfl

theorem cell23_3234855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_3234855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234855 prefixEnd_3234855 := by exact prefixLift 3234855
  have htrace : WordTrace (prefixWord ++ tailWord_3234855) baseStart_3234855 baseEnd_3234855 := by
    simpa [prefixWord, tailWord_3234855, baseEnd_3234855] using wordTrace_append hprefix tailTrace_3234855
  have hstable : (prefixWord ++ tailWord_3234855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234855).length < 2 ^ (prefixWord ++ tailWord_3234855).sum := by decide
  have hdescent : baseEnd_3234855 < baseStart_3234855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234864 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 5]
def baseStart_3234864 : Nat := 118140960795 + 3234864 * 2 ^ 59
def prefixEnd_3234864 : Nat := 4983230072969 + 3 ^ 40 * 3234864 * 2
def baseEnd_3234864 : Nat := 1661040083925936813423137

theorem tailTrace_3234864 : CollatzResearch.WordTrace tailWord_3234864 prefixEnd_3234864 1661040083925936813423137 := by
  unfold tailWord_3234864
  simp only [CollatzResearch.WordTrace]
  refine ⟨58992591476323836815931823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78656788635098449087909097 58992591476323836815931823)
  ·
    refine ⟨88488887214485755223897735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58992591476323836815931823 88488887214485755223897735)
    ·
      refine ⟨132733330821728632835846603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88488887214485755223897735 132733330821728632835846603)
      ·
        refine ⟨199099996232592949253769905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132733330821728632835846603 199099996232592949253769905)
        ·
          refine ⟨149324997174444711940327429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199099996232592949253769905 149324997174444711940327429)
          ·
            refine ⟨27998436970208383488811393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149324997174444711940327429 27998436970208383488811393)
            ·
              refine ⟨20998827727656287616608545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27998436970208383488811393 20998827727656287616608545)
              ·
                refine ⟨15749120795742215712456409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20998827727656287616608545 15749120795742215712456409)
                ·
                  refine ⟨11811840596806661784342307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15749120795742215712456409 11811840596806661784342307)
                  ·
                    refine ⟨17717760895209992676513461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11811840596806661784342307 17717760895209992676513461)
                    ·
                      refine ⟨1661040083925936813423137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17717760895209992676513461 1661040083925936813423137)
                      ·
                        rfl

theorem cell23_3234864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_3234864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234864 prefixEnd_3234864 := by exact prefixLift 3234864
  have htrace : WordTrace (prefixWord ++ tailWord_3234864) baseStart_3234864 baseEnd_3234864 := by
    simpa [prefixWord, tailWord_3234864, baseEnd_3234864] using wordTrace_append hprefix tailTrace_3234864
  have hstable : (prefixWord ++ tailWord_3234864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234864).length < 2 ^ (prefixWord ++ tailWord_3234864).sum := by decide
  have hdescent : baseEnd_3234864 < baseStart_3234864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234874 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_3234874 : Nat := 118140960795 + 3234874 * 2 ^ 59
def prefixEnd_3234874 : Nat := 4983230072969 + 3 ^ 40 * 3234874 * 2
def baseEnd_3234874 : Nat := 1661045218732481774298091

theorem tailTrace_3234874 : CollatzResearch.WordTrace tailWord_3234874 prefixEnd_3234874 1661045218732481774298091 := by
  unfold tailWord_3234874
  simp only [CollatzResearch.WordTrace]
  refine ⟨29496386920652861334931919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78657031788407630226485117 29496386920652861334931919)
  ·
    refine ⟨44244580380979292002397879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29496386920652861334931919 44244580380979292002397879)
    ·
      refine ⟨66366870571468938003596819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44244580380979292002397879 66366870571468938003596819)
      ·
        refine ⟨99550305857203407005395229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66366870571468938003596819 99550305857203407005395229)
        ·
          refine ⟨37331364696451277627023211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99550305857203407005395229 37331364696451277627023211)
          ·
            refine ⟨55997047044676916440534817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37331364696451277627023211 55997047044676916440534817)
            ·
              refine ⟨41997785283507687330401113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55997047044676916440534817 41997785283507687330401113)
              ·
                refine ⟨31498338962630765497800835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41997785283507687330401113 31498338962630765497800835)
                ·
                  refine ⟨47247508443946148246701253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31498338962630765497800835 47247508443946148246701253)
                  ·
                    refine ⟨8858907833239902796256485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47247508443946148246701253 8858907833239902796256485)
                    ·
                      refine ⟨1661045218732481774298091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8858907833239902796256485 1661045218732481774298091)
                      ·
                        rfl

theorem cell23_3234874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_3234874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234874 prefixEnd_3234874 := by exact prefixLift 3234874
  have htrace : WordTrace (prefixWord ++ tailWord_3234874) baseStart_3234874 baseEnd_3234874 := by
    simpa [prefixWord, tailWord_3234874, baseEnd_3234874] using wordTrace_append hprefix tailTrace_3234874
  have hstable : (prefixWord ++ tailWord_3234874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234874).length < 2 ^ (prefixWord ++ tailWord_3234874).sum := by decide
  have hdescent : baseEnd_3234874 < baseStart_3234874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234894 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3234894 : Nat := 118140960795 + 3234894 * 2 ^ 59
def prefixEnd_3234894 : Nat := 4983230072969 + 3 ^ 40 * 3234894 * 2
def baseEnd_3234894 : Nat := 1661055488345571696047999

theorem tailTrace_3234894 : CollatzResearch.WordTrace tailWord_3234894 prefixEnd_3234894 1661055488345571696047999 := by
  unfold tailWord_3234894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14748284642817373594431967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78657518095025992503637157 14748284642817373594431967)
  ·
    refine ⟨22122426964226060391647951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14748284642817373594431967 22122426964226060391647951)
    ·
      refine ⟨33183640446339090587471927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22122426964226060391647951 33183640446339090587471927)
      ·
        refine ⟨49775460669508635881207891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33183640446339090587471927 49775460669508635881207891)
        ·
          refine ⟨74663191004262953821811837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49775460669508635881207891 74663191004262953821811837)
          ·
            refine ⟨27998696626598607683179439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74663191004262953821811837 27998696626598607683179439)
            ·
              refine ⟨41998044939897911524769159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27998696626598607683179439 41998044939897911524769159)
              ·
                refine ⟨62997067409846867287153739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41998044939897911524769159 62997067409846867287153739)
                ·
                  refine ⟨94495601114770300930730609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62997067409846867287153739 94495601114770300930730609)
                  ·
                    refine ⟨70871700836077725698047957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94495601114770300930730609 70871700836077725698047957)
                    ·
                      refine ⟨1661055488345571696047999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70871700836077725698047957 1661055488345571696047999)
                      ·
                        rfl

theorem cell23_3234894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3234894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234894 prefixEnd_3234894 := by exact prefixLift 3234894
  have htrace : WordTrace (prefixWord ++ tailWord_3234894) baseStart_3234894 baseEnd_3234894 := by
    simpa [prefixWord, tailWord_3234894, baseEnd_3234894] using wordTrace_append hprefix tailTrace_3234894
  have hstable : (prefixWord ++ tailWord_3234894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234894).length < 2 ^ (prefixWord ++ tailWord_3234894).sum := by decide
  have hdescent : baseEnd_3234894 < baseStart_3234894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234924 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_3234924 : Nat := 118140960795 + 3234924 * 2 ^ 59
def prefixEnd_3234924 : Nat := 4983230072969 + 3 ^ 40 * 3234924 * 2
def baseEnd_3234924 : Nat := 1661070892765206578672861

theorem tailTrace_3234924 : CollatzResearch.WordTrace tailWord_3234924 prefixEnd_3234924 1661070892765206578672861 := by
  unfold tailWord_3234924
  simp only [CollatzResearch.WordTrace]
  refine ⟨58993685666215151939523913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78658247554953535919365217 58993685666215151939523913)
  ·
    refine ⟨44245264249661363954642935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58993685666215151939523913 44245264249661363954642935)
    ·
      refine ⟨66367896374492045931964403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44245264249661363954642935 66367896374492045931964403)
      ·
        refine ⟨99551844561738068897946605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66367896374492045931964403 99551844561738068897946605)
        ·
          refine ⟨37331941710651775836729977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99551844561738068897946605 37331941710651775836729977)
          ·
            refine ⟨27998956282988831877547483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37331941710651775836729977 27998956282988831877547483)
            ·
              refine ⟨41998434424483247816321225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27998956282988831877547483 41998434424483247816321225)
              ·
                refine ⟨31498825818362435862240919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41998434424483247816321225 31498825818362435862240919)
                ·
                  refine ⟨47248238727543653793361379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31498825818362435862240919 47248238727543653793361379)
                  ·
                    refine ⟨70872358091315480690042069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47248238727543653793361379 70872358091315480690042069)
                    ·
                      refine ⟨1661070892765206578672861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70872358091315480690042069 1661070892765206578672861)
                      ·
                        rfl

theorem cell23_3234924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_3234924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234924 prefixEnd_3234924 := by exact prefixLift 3234924
  have htrace : WordTrace (prefixWord ++ tailWord_3234924) baseStart_3234924 baseEnd_3234924 := by
    simpa [prefixWord, tailWord_3234924, baseEnd_3234924] using wordTrace_append hprefix tailTrace_3234924
  have hstable : (prefixWord ++ tailWord_3234924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234924).length < 2 ^ (prefixWord ++ tailWord_3234924).sum := by decide
  have hdescent : baseEnd_3234924 < baseStart_3234924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234952 : List Nat := [2, 1, 3, 4, 2, 2, 2, 2, 5]
def baseStart_3234952 : Nat := 118140960795 + 3234952 * 2 ^ 59
def prefixEnd_3234952 : Nat := 4983230072969 + 3 ^ 40 * 3234952 * 2
def baseEnd_3234952 : Nat := 184565030024836941013637

theorem tailTrace_3234952 : CollatzResearch.WordTrace tailWord_3234952 prefixEnd_3234952 184565030024836941013637 := by
  unfold tailWord_3234952
  simp only [CollatzResearch.WordTrace]
  refine ⟨58994196288164432330533555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78658928384219243107378073 58994196288164432330533555)
  ·
    refine ⟨88491294432246648495800333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58994196288164432330533555 88491294432246648495800333)
    ·
      refine ⟨33184235412092493185925125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88491294432246648495800333 33184235412092493185925125)
      ·
        refine ⟨6222044139767342472360961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33184235412092493185925125 6222044139767342472360961)
        ·
          refine ⟨4666533104825506854270721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6222044139767342472360961 4666533104825506854270721)
          ·
            refine ⟨3499899828619130140703041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4666533104825506854270721 3499899828619130140703041)
            ·
              refine ⟨2624924871464347605527281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3499899828619130140703041 2624924871464347605527281)
              ·
                refine ⟨1968693653598260704145461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2624924871464347605527281 1968693653598260704145461)
                ·
                  refine ⟨184565030024836941013637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1968693653598260704145461 184565030024836941013637)
                  ·
                    rfl

theorem cell23_3234952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 5].length) (baseStart_3234952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234952 prefixEnd_3234952 := by exact prefixLift 3234952
  have htrace : WordTrace (prefixWord ++ tailWord_3234952) baseStart_3234952 baseEnd_3234952 := by
    simpa [prefixWord, tailWord_3234952, baseEnd_3234952] using wordTrace_append hprefix tailTrace_3234952
  have hstable : (prefixWord ++ tailWord_3234952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234952).length < 2 ^ (prefixWord ++ tailWord_3234952).sum := by decide
  have hdescent : baseEnd_3234952 < baseStart_3234952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3234968 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 1, 6, 2]
def baseStart_3234968 : Nat := 118140960795 + 3234968 * 2 ^ 59
def prefixEnd_3234968 : Nat := 4983230072969 + 3 ^ 40 * 3234968 * 2
def baseEnd_3234968 : Nat := 1661093485914004406522659

theorem tailTrace_3234968 : CollatzResearch.WordTrace tailWord_3234968 prefixEnd_3234968 1661093485914004406522659 := by
  unfold tailWord_3234968
  simp only [CollatzResearch.WordTrace]
  refine ⟨58994488072135449696824779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78659317429513932929099705 58994488072135449696824779)
  ·
    refine ⟨88491732108203174545237169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58994488072135449696824779 88491732108203174545237169)
    ·
      refine ⟨66368799081152380908927877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88491732108203174545237169 66368799081152380908927877)
      ·
        refine ⟨12444149827716071420423977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66368799081152380908927877 12444149827716071420423977)
        ·
          refine ⟨9333112370787053565317983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12444149827716071420423977 9333112370787053565317983)
          ·
            refine ⟨13999668556180580347976975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9333112370787053565317983 13999668556180580347976975)
            ·
              refine ⟨20999502834270870521965463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13999668556180580347976975 20999502834270870521965463)
              ·
                refine ⟨31499254251406305782948195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20999502834270870521965463 31499254251406305782948195)
                ·
                  refine ⟨47248881377109458674422293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31499254251406305782948195 47248881377109458674422293)
                  ·
                    refine ⟨2214791314552005875363545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47248881377109458674422293 2214791314552005875363545)
                    ·
                      refine ⟨1661093485914004406522659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2214791314552005875363545 1661093485914004406522659)
                      ·
                        rfl

theorem cell23_3234968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_3234968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3234968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3234968 prefixEnd_3234968 := by exact prefixLift 3234968
  have htrace : WordTrace (prefixWord ++ tailWord_3234968) baseStart_3234968 baseEnd_3234968 := by
    simpa [prefixWord, tailWord_3234968, baseEnd_3234968] using wordTrace_append hprefix tailTrace_3234968
  have hstable : (prefixWord ++ tailWord_3234968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3234968).length < 2 ^ (prefixWord ++ tailWord_3234968).sum := by decide
  have hdescent : baseEnd_3234968 < baseStart_3234968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3234968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235052 : List Nat := [2, 2, 1, 1, 2, 4, 3, 3, 1, 1, 3]
def baseStart_3235052 : Nat := 118140960795 + 3235052 * 2 ^ 59
def prefixEnd_3235052 : Nat := 4983230072969 + 3 ^ 40 * 3235052 * 2
def baseEnd_3235052 : Nat := 1661136618288982077872273

theorem tailTrace_3235052 : CollatzResearch.WordTrace tailWord_3235052 prefixEnd_3235052 1661136618288982077872273 := by
  unfold tailWord_3235052
  simp only [CollatzResearch.WordTrace]
  refine ⟨58996019937983290869853705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78661359917311054493138273 58996019937983290869853705)
  ·
    refine ⟨44247014953487468152390279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58996019937983290869853705 44247014953487468152390279)
    ·
      refine ⟨66370522430231202228585419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44247014953487468152390279 66370522430231202228585419)
      ·
        refine ⟨99555783645346803342878129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66370522430231202228585419 99555783645346803342878129)
        ·
          refine ⟨74666837734010102507158597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99555783645346803342878129 74666837734010102507158597)
          ·
            refine ⟨14000032075126894220092237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74666837734010102507158597 14000032075126894220092237)
            ·
              refine ⟨5250012028172585332534589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14000032075126894220092237 5250012028172585332534589)
              ·
                refine ⟨1968754510564719499700471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5250012028172585332534589 1968754510564719499700471)
                ·
                  refine ⟨2953131765847079249550707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968754510564719499700471 2953131765847079249550707)
                  ·
                    refine ⟨4429697648770618874326061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2953131765847079249550707 4429697648770618874326061)
                    ·
                      refine ⟨1661136618288982077872273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4429697648770618874326061 1661136618288982077872273)
                      ·
                        rfl

theorem cell23_3235052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 1, 1, 3].length) (baseStart_3235052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235052 prefixEnd_3235052 := by exact prefixLift 3235052
  have htrace : WordTrace (prefixWord ++ tailWord_3235052) baseStart_3235052 baseEnd_3235052 := by
    simpa [prefixWord, tailWord_3235052, baseEnd_3235052] using wordTrace_append hprefix tailTrace_3235052
  have hstable : (prefixWord ++ tailWord_3235052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235052).length < 2 ^ (prefixWord ++ tailWord_3235052).sum := by decide
  have hdescent : baseEnd_3235052 < baseStart_3235052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235071 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 6]
def baseStart_3235071 : Nat := 118140960795 + 3235071 * 2 ^ 59
def prefixEnd_3235071 : Nat := 4983230072969 + 3 ^ 40 * 3235071 * 2
def baseEnd_3235071 : Nat := 1661146374421417503534685

theorem tailTrace_3235071 : CollatzResearch.WordTrace tailWord_3235071 prefixEnd_3235071 1661146374421417503534685 := by
  unfold tailWord_3235071
  simp only [CollatzResearch.WordTrace]
  refine ⟨117992732862897747984649067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78661821908598498656432711 117992732862897747984649067)
  ·
    refine ⟨176989099294346621976973601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117992732862897747984649067 176989099294346621976973601)
    ·
      refine ⟨132741824470759966482730201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176989099294346621976973601 132741824470759966482730201)
      ·
        refine ⟨99556368353069974862047651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132741824470759966482730201 99556368353069974862047651)
        ·
          refine ⟨149334552529604962293071477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99556368353069974862047651 149334552529604962293071477)
          ·
            refine ⟨14000114299650465214975451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149334552529604962293071477 14000114299650465214975451)
            ·
              refine ⟨21000171449475697822463177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14000114299650465214975451 21000171449475697822463177)
              ·
                refine ⟨15750128587106773366847383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21000171449475697822463177 15750128587106773366847383)
                ·
                  refine ⟨23625192880660160050271075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15750128587106773366847383 23625192880660160050271075)
                  ·
                    refine ⟨35437789320990240075406613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23625192880660160050271075 35437789320990240075406613)
                    ·
                      refine ⟨1661146374421417503534685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35437789320990240075406613 1661146374421417503534685)
                      ·
                        rfl

theorem cell23_3235071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_3235071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235071 prefixEnd_3235071 := by exact prefixLift 3235071
  have htrace : WordTrace (prefixWord ++ tailWord_3235071) baseStart_3235071 baseEnd_3235071 := by
    simpa [prefixWord, tailWord_3235071, baseEnd_3235071] using wordTrace_append hprefix tailTrace_3235071
  have hstable : (prefixWord ++ tailWord_3235071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235071).length < 2 ^ (prefixWord ++ tailWord_3235071).sum := by decide
  have hdescent : baseEnd_3235071 < baseStart_3235071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235081 : List Nat := [1, 2, 1, 1, 3, 3, 4, 8]
def baseStart_3235081 : Nat := 118140960795 + 3235081 * 2 ^ 59
def prefixEnd_3235081 : Nat := 4983230072969 + 3 ^ 40 * 3235081 * 2
def baseEnd_3235081 : Nat := 61524129971406017200357

theorem tailTrace_3235081 : CollatzResearch.WordTrace tailWord_3235081 prefixEnd_3235081 61524129971406017200357 := by
  unfold tailWord_3235081
  simp only [CollatzResearch.WordTrace]
  refine ⟨117993097592861519692513097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78662065061907679795008731 117993097592861519692513097)
  ·
    refine ⟨88494823194646139769384823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117993097592861519692513097 88494823194646139769384823)
    ·
      refine ⟨132742234791969209654077235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88494823194646139769384823 132742234791969209654077235)
      ·
        refine ⟨199113352187953814481115853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132742234791969209654077235 199113352187953814481115853)
        ·
          refine ⟨74667507070482680430418445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199113352187953814481115853 74667507070482680430418445)
          ·
            refine ⟨28000315151431005161406917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74667507070482680430418445 28000315151431005161406917)
            ·
              refine ⟨5250059090893313467763797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28000315151431005161406917 5250059090893313467763797)
              ·
                refine ⟨61524129971406017200357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5250059090893313467763797 61524129971406017200357)
                ·
                  rfl

theorem cell23_3235081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 8].length) (baseStart_3235081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235081 prefixEnd_3235081 := by exact prefixLift 3235081
  have htrace : WordTrace (prefixWord ++ tailWord_3235081) baseStart_3235081 baseEnd_3235081 := by
    simpa [prefixWord, tailWord_3235081, baseEnd_3235081] using wordTrace_append hprefix tailTrace_3235081
  have hstable : (prefixWord ++ tailWord_3235081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235081).length < 2 ^ (prefixWord ++ tailWord_3235081).sum := by decide
  have hdescent : baseEnd_3235081 < baseStart_3235081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235102 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3235102 : Nat := 118140960795 + 3235102 * 2 ^ 59
def prefixEnd_3235102 : Nat := 4983230072969 + 3 ^ 40 * 3235102 * 2
def baseEnd_3235102 : Nat := 553720764107235627415681

theorem tailTrace_3235102 : CollatzResearch.WordTrace tailWord_3235102 prefixEnd_3235102 553720764107235627415681 := by
  unfold tailWord_3235102
  simp only [CollatzResearch.WordTrace]
  refine ⟨14749232940723180034878445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78662575683856960186018373 14749232940723180034878445)
  ·
    refine ⟨5530962352771192513079417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14749232940723180034878445 5530962352771192513079417)
    ·
      refine ⟨4148221764578394384809563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5530962352771192513079417 4148221764578394384809563)
      ·
        refine ⟨6222332646867591577214345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4148221764578394384809563 6222332646867591577214345)
        ·
          refine ⟨4666749485150693682910759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6222332646867591577214345 4666749485150693682910759)
          ·
            refine ⟨7000124227726040524366139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4666749485150693682910759 7000124227726040524366139)
            ·
              refine ⟨10500186341589060786549209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7000124227726040524366139 10500186341589060786549209)
              ·
                refine ⟨7875139756191795589911907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10500186341589060786549209 7875139756191795589911907)
                ·
                  refine ⟨11812709634287693384867861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7875139756191795589911907 11812709634287693384867861)
                  ·
                    refine ⟨553720764107235627415681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11812709634287693384867861 553720764107235627415681)
                    ·
                      rfl

theorem cell23_3235102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3235102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235102 prefixEnd_3235102 := by exact prefixLift 3235102
  have htrace : WordTrace (prefixWord ++ tailWord_3235102) baseStart_3235102 baseEnd_3235102 := by
    simpa [prefixWord, tailWord_3235102, baseEnd_3235102] using wordTrace_append hprefix tailTrace_3235102
  have hstable : (prefixWord ++ tailWord_3235102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235102).length < 2 ^ (prefixWord ++ tailWord_3235102).sum := by decide
  have hdescent : baseEnd_3235102 < baseStart_3235102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235135 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 3, 3, 2]
def baseStart_3235135 : Nat := 118140960795 + 3235135 * 2 ^ 59
def prefixEnd_3235135 : Nat := 4983230072969 + 3 ^ 40 * 3235135 * 2
def baseEnd_3235135 : Nat := 1661179237183305253134391

theorem tailTrace_3235135 : CollatzResearch.WordTrace tailWord_3235135 prefixEnd_3235135 1661179237183305253134391 := by
  unfold tailWord_3235135
  simp only [CollatzResearch.WordTrace]
  refine ⟨117995067134665886914978859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78663378089777257943319239 117995067134665886914978859)
  ·
    refine ⟨176992600701998830372468289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117995067134665886914978859 176992600701998830372468289)
    ·
      refine ⟨132744450526499122779351217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176992600701998830372468289 132744450526499122779351217)
      ·
        refine ⟨99558337894874342084513413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132744450526499122779351217 99558337894874342084513413)
        ·
          refine ⟨18667188355288939140846265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99558337894874342084513413 18667188355288939140846265)
          ·
            refine ⟨14000391266466704355634699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18667188355288939140846265 14000391266466704355634699)
            ·
              refine ⟨21000586899700056533452049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14000391266466704355634699 21000586899700056533452049)
              ·
                refine ⟨15750440174775042400089037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21000586899700056533452049 15750440174775042400089037)
                ·
                  refine ⟨5906415065540640900033389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15750440174775042400089037 5906415065540640900033389)
                  ·
                    refine ⟨2214905649577740337512521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5906415065540640900033389 2214905649577740337512521)
                    ·
                      refine ⟨1661179237183305253134391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2214905649577740337512521 1661179237183305253134391)
                      ·
                        rfl

theorem cell23_3235135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 3, 2].length) (baseStart_3235135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235135 prefixEnd_3235135 := by exact prefixLift 3235135
  have htrace : WordTrace (prefixWord ++ tailWord_3235135) baseStart_3235135 baseEnd_3235135 := by
    simpa [prefixWord, tailWord_3235135, baseEnd_3235135] using wordTrace_append hprefix tailTrace_3235135
  have hstable : (prefixWord ++ tailWord_3235135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235135).length < 2 ^ (prefixWord ++ tailWord_3235135).sum := by decide
  have hdescent : baseEnd_3235135 < baseStart_3235135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235176 : List Nat := [2, 1, 4, 2, 4, 1, 1, 2, 2, 1, 3]
def baseStart_3235176 : Nat := 118140960795 + 3235176 * 2 ^ 59
def prefixEnd_3235176 : Nat := 4983230072969 + 3 ^ 40 * 3235176 * 2
def baseEnd_3235176 : Nat := 1661200289890139592721703

theorem tailTrace_3235176 : CollatzResearch.WordTrace tailWord_3235176 prefixEnd_3235176 1661200289890139592721703 := by
  unfold tailWord_3235176
  simp only [CollatzResearch.WordTrace]
  refine ⟨58998281263758675458610691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78664375018344900611480921 58998281263758675458610691)
  ·
    refine ⟨88497421895638013187916037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58998281263758675458610691 88497421895638013187916037)
    ·
      refine ⟨16593266605432127472734257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88497421895638013187916037 16593266605432127472734257)
      ·
        refine ⟨12444949954074095604550693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16593266605432127472734257 12444949954074095604550693)
        ·
          refine ⟨2333428116388892925853255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12444949954074095604550693 2333428116388892925853255)
          ·
            refine ⟨3500142174583339388779883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333428116388892925853255 3500142174583339388779883)
            ·
              refine ⟨5250213261875009083169825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3500142174583339388779883 5250213261875009083169825)
              ·
                refine ⟨3937659946406256812377369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5250213261875009083169825 3937659946406256812377369)
                ·
                  refine ⟨2953244959804692609283027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3937659946406256812377369 2953244959804692609283027)
                  ·
                    refine ⟨4429867439707038913924541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2953244959804692609283027 4429867439707038913924541)
                    ·
                      refine ⟨1661200289890139592721703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4429867439707038913924541 1661200289890139592721703)
                      ·
                        rfl

theorem cell23_3235176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_3235176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235176 prefixEnd_3235176 := by exact prefixLift 3235176
  have htrace : WordTrace (prefixWord ++ tailWord_3235176) baseStart_3235176 baseEnd_3235176 := by
    simpa [prefixWord, tailWord_3235176, baseEnd_3235176] using wordTrace_append hprefix tailTrace_3235176
  have hstable : (prefixWord ++ tailWord_3235176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235176).length < 2 ^ (prefixWord ++ tailWord_3235176).sum := by decide
  have hdescent : baseEnd_3235176 < baseStart_3235176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235245 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3235245 : Nat := 118140960795 + 3235245 * 2 ^ 59
def prefixEnd_3235245 : Nat := 4983230072969 + 3 ^ 40 * 3235245 * 2
def baseEnd_3235245 : Nat := 1661235720055299822758885

theorem tailTrace_3235245 : CollatzResearch.WordTrace tailWord_3235245 prefixEnd_3235245 1661235720055299822758885 := by
  unfold tailWord_3235245
  simp only [CollatzResearch.WordTrace]
  refine ⟨117999079164267375701483189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78666052776178250467655459 117999079164267375701483189)
  ·
    refine ⟨11062413671650066472014049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117999079164267375701483189 11062413671650066472014049)
    ·
      refine ⟨8296810253737549854010537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11062413671650066472014049 8296810253737549854010537)
      ·
        refine ⟨6222607690303162390507903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8296810253737549854010537 6222607690303162390507903)
        ·
          refine ⟨9333911535454743585761855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6222607690303162390507903 9333911535454743585761855)
          ·
            refine ⟨14000867303182115378642783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9333911535454743585761855 14000867303182115378642783)
            ·
              refine ⟨21001300954773173067964175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14000867303182115378642783 21001300954773173067964175)
              ·
                refine ⟨31501951432159759601946263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21001300954773173067964175 31501951432159759601946263)
                ·
                  refine ⟨47252927148239639402919395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31501951432159759601946263 47252927148239639402919395)
                  ·
                    refine ⟨70879390722359459104379093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47252927148239639402919395 70879390722359459104379093)
                    ·
                      refine ⟨1661235720055299822758885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70879390722359459104379093 1661235720055299822758885)
                      ·
                        rfl

theorem cell23_3235245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3235245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235245 prefixEnd_3235245 := by exact prefixLift 3235245
  have htrace : WordTrace (prefixWord ++ tailWord_3235245) baseStart_3235245 baseEnd_3235245 := by
    simpa [prefixWord, tailWord_3235245, baseEnd_3235245] using wordTrace_append hprefix tailTrace_3235245
  have hstable : (prefixWord ++ tailWord_3235245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235245).length < 2 ^ (prefixWord ++ tailWord_3235245).sum := by decide
  have hdescent : baseEnd_3235245 < baseStart_3235245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235255 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 1, 6, 2]
def baseStart_3235255 : Nat := 118140960795 + 3235255 * 2 ^ 59
def prefixEnd_3235255 : Nat := 4983230072969 + 3 ^ 40 * 3235255 * 2
def baseEnd_3235255 : Nat := 1661240854861844783633839

theorem tailTrace_3235255 : CollatzResearch.WordTrace tailWord_3235255 prefixEnd_3235255 1661240854861844783633839 := by
  unfold tailWord_3235255
  simp only [CollatzResearch.WordTrace]
  refine ⟨117999443894231147409347219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78666295929487431606231479 117999443894231147409347219)
  ·
    refine ⟨176999165841346721114020829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117999443894231147409347219 176999165841346721114020829)
    ·
      refine ⟨66374687190505020417757811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176999165841346721114020829 66374687190505020417757811)
      ·
        refine ⟨99562030785757530626636717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66374687190505020417757811 99562030785757530626636717)
        ·
          refine ⟨37335761544659073984988769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99562030785757530626636717 37335761544659073984988769)
          ·
            refine ⟨28001821158494305488741577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37335761544659073984988769 28001821158494305488741577)
            ·
              refine ⟨21001365868870729116556183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28001821158494305488741577 21001365868870729116556183)
              ·
                refine ⟨31502048803306093674834275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21001365868870729116556183 31502048803306093674834275)
                ·
                  refine ⟨47253073204959140512251413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31502048803306093674834275 47253073204959140512251413)
                  ·
                    refine ⟨2214987806482459711511785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47253073204959140512251413 2214987806482459711511785)
                    ·
                      refine ⟨1661240854861844783633839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2214987806482459711511785 1661240854861844783633839)
                      ·
                        rfl

theorem cell23_3235255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 6, 2].length) (baseStart_3235255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235255 prefixEnd_3235255 := by exact prefixLift 3235255
  have htrace : WordTrace (prefixWord ++ tailWord_3235255) baseStart_3235255 baseEnd_3235255 := by
    simpa [prefixWord, tailWord_3235255, baseEnd_3235255] using wordTrace_append hprefix tailTrace_3235255
  have hstable : (prefixWord ++ tailWord_3235255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235255).length < 2 ^ (prefixWord ++ tailWord_3235255).sum := by decide
  have hdescent : baseEnd_3235255 < baseStart_3235255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235275 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 3]
def baseStart_3235275 : Nat := 118140960795 + 3235275 * 2 ^ 59
def prefixEnd_3235275 : Nat := 4983230072969 + 3 ^ 40 * 3235275 * 2
def baseEnd_3235275 : Nat := 1661251124474934705383747

theorem tailTrace_3235275 : CollatzResearch.WordTrace tailWord_3235275 prefixEnd_3235275 1661251124474934705383747 := by
  unfold tailWord_3235275
  simp only [CollatzResearch.WordTrace]
  refine ⟨118000173354158690825075279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78666782236105793883383519 118000173354158690825075279)
  ·
    refine ⟨177000260031238036237612919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118000173354158690825075279 177000260031238036237612919)
    ·
      refine ⟨265500390046857054356419379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177000260031238036237612919 265500390046857054356419379)
      ·
        refine ⟨398250585070285581534629069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265500390046857054356419379 398250585070285581534629069)
        ·
          refine ⟨149343969401357093075485901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398250585070285581534629069 149343969401357093075485901)
          ·
            refine ⟨56003988525508909903307213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149343969401357093075485901 56003988525508909903307213)
            ·
              refine ⟨21001495697065841213740205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56003988525508909903307213 21001495697065841213740205)
              ·
                refine ⟨7875560886399690455152577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21001495697065841213740205 7875560886399690455152577)
                ·
                  refine ⟨5906670664799767841364433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7875560886399690455152577 5906670664799767841364433)
                  ·
                    refine ⟨4430002998599825881023325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5906670664799767841364433 4430002998599825881023325)
                    ·
                      refine ⟨1661251124474934705383747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4430002998599825881023325 1661251124474934705383747)
                      ·
                        rfl

theorem cell23_3235275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 3].length) (baseStart_3235275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235275 prefixEnd_3235275 := by exact prefixLift 3235275
  have htrace : WordTrace (prefixWord ++ tailWord_3235275) baseStart_3235275 baseEnd_3235275 := by
    simpa [prefixWord, tailWord_3235275, baseEnd_3235275] using wordTrace_append hprefix tailTrace_3235275
  have hstable : (prefixWord ++ tailWord_3235275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235275).length < 2 ^ (prefixWord ++ tailWord_3235275).sum := by decide
  have hdescent : baseEnd_3235275 < baseStart_3235275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235278 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 10]
def baseStart_3235278 : Nat := 118140960795 + 3235278 * 2 ^ 59
def prefixEnd_3235278 : Nat := 4983230072969 + 3 ^ 40 * 3235278 * 2
def baseEnd_3235278 : Nat := 184583629435210910405137

theorem tailTrace_3235278 : CollatzResearch.WordTrace tailWord_3235278 prefixEnd_3235278 184583629435210910405137 := by
  unfold tailWord_3235278
  simp only [CollatzResearch.WordTrace]
  refine ⟨14750035346643477792179311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78666855182098548224956325 14750035346643477792179311)
  ·
    refine ⟨22125053019965216688268967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14750035346643477792179311 22125053019965216688268967)
    ·
      refine ⟨33187579529947825032403451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22125053019965216688268967 33187579529947825032403451)
      ·
        refine ⟨49781369294921737548605177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33187579529947825032403451 49781369294921737548605177)
        ·
          refine ⟨37336026971191303161453883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49781369294921737548605177 37336026971191303161453883)
          ·
            refine ⟨56004040456786954742180825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37336026971191303161453883 56004040456786954742180825)
            ·
              refine ⟨42003030342590216056635619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56004040456786954742180825 42003030342590216056635619)
              ·
                refine ⟨63004545513885324084953429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42003030342590216056635619 63004545513885324084953429)
                ·
                  refine ⟨184583629435210910405137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 63004545513885324084953429 184583629435210910405137)
                  ·
                    rfl

theorem cell23_3235278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_3235278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235278 prefixEnd_3235278 := by exact prefixLift 3235278
  have htrace : WordTrace (prefixWord ++ tailWord_3235278) baseStart_3235278 baseEnd_3235278 := by
    simpa [prefixWord, tailWord_3235278, baseEnd_3235278] using wordTrace_append hprefix tailTrace_3235278
  have hstable : (prefixWord ++ tailWord_3235278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235278).length < 2 ^ (prefixWord ++ tailWord_3235278).sum := by decide
  have hdescent : baseEnd_3235278 < baseStart_3235278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235295 : List Nat := [1, 1, 2, 3, 3, 1, 4, 2, 6]
def baseStart_3235295 : Nat := 118140960795 + 3235295 * 2 ^ 59
def prefixEnd_3235295 : Nat := 4983230072969 + 3 ^ 40 * 3235295 * 2
def baseEnd_3235295 : Nat := 184584599343113847459295

theorem tailTrace_3235295 : CollatzResearch.WordTrace tailWord_3235295 prefixEnd_3235295 184584599343113847459295 := by
  unfold tailWord_3235295
  simp only [CollatzResearch.WordTrace]
  refine ⟨118000902814086234240803339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78667268542724156160535559 118000902814086234240803339)
  ·
    refine ⟨177001354221129351361205009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118000902814086234240803339 177001354221129351361205009)
    ·
      refine ⟨132751015665847013520903757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177001354221129351361205009 132751015665847013520903757)
      ·
        refine ⟨49781630874692630070338909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132751015665847013520903757 49781630874692630070338909)
        ·
          refine ⟨18668111578009736276377091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49781630874692630070338909 18668111578009736276377091)
          ·
            refine ⟨28002167367014604414565637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18668111578009736276377091 28002167367014604414565637)
            ·
              refine ⟨5250406381315238327731057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28002167367014604414565637 5250406381315238327731057)
              ·
                refine ⟨3937804785986428745798293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5250406381315238327731057 3937804785986428745798293)
                ·
                  refine ⟨184584599343113847459295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3937804785986428745798293 184584599343113847459295)
                  ·
                    rfl

theorem cell23_3235295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 6].length) (baseStart_3235295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235295 prefixEnd_3235295 := by exact prefixLift 3235295
  have htrace : WordTrace (prefixWord ++ tailWord_3235295) baseStart_3235295 baseEnd_3235295 := by
    simpa [prefixWord, tailWord_3235295, baseEnd_3235295] using wordTrace_append hprefix tailTrace_3235295
  have hstable : (prefixWord ++ tailWord_3235295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235295).length < 2 ^ (prefixWord ++ tailWord_3235295).sum := by decide
  have hdescent : baseEnd_3235295 < baseStart_3235295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235299 : List Nat := [1, 1, 1, 6, 2, 2, 1, 4, 1, 4]
def baseStart_3235299 : Nat := 118140960795 + 3235299 * 2 ^ 59
def prefixEnd_3235299 : Nat := 4983230072969 + 3 ^ 40 * 3235299 * 2
def baseEnd_3235299 : Nat := 553754482670214203827879

theorem tailTrace_3235299 : CollatzResearch.WordTrace tailWord_3235299 prefixEnd_3235299 553754482670214203827879 := by
  unfold tailWord_3235299
  simp only [CollatzResearch.WordTrace]
  refine ⟨118001048706071742923948951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78667365804047828615965967 118001048706071742923948951)
  ·
    refine ⟨177001573059107614385923427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118001048706071742923948951 177001573059107614385923427)
    ·
      refine ⟨265502359588661421578885141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177001573059107614385923427 265502359588661421578885141)
      ·
        refine ⟨12445423105718504136510241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 265502359588661421578885141 12445423105718504136510241)
        ·
          refine ⟨9334067329288878102382681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12445423105718504136510241 9334067329288878102382681)
          ·
            refine ⟨7000550496966658576787011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9334067329288878102382681 7000550496966658576787011)
            ·
              refine ⟨10500825745449987865180517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7000550496966658576787011 10500825745449987865180517)
              ·
                refine ⟨1968904827271872724721347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10500825745449987865180517 1968904827271872724721347)
                ·
                  refine ⟨2953357240907809087082021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968904827271872724721347 2953357240907809087082021)
                  ·
                    refine ⟨553754482670214203827879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2953357240907809087082021 553754482670214203827879)
                    ·
                      rfl

theorem cell23_3235299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 1, 4].length) (baseStart_3235299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235299 prefixEnd_3235299 := by exact prefixLift 3235299
  have htrace : WordTrace (prefixWord ++ tailWord_3235299) baseStart_3235299 baseEnd_3235299 := by
    simpa [prefixWord, tailWord_3235299, baseEnd_3235299] using wordTrace_append hprefix tailTrace_3235299
  have hstable : (prefixWord ++ tailWord_3235299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235299).length < 2 ^ (prefixWord ++ tailWord_3235299).sum := by decide
  have hdescent : baseEnd_3235299 < baseStart_3235299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235322 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3]
def baseStart_3235322 : Nat := 118140960795 + 3235322 * 2 ^ 59
def prefixEnd_3235322 : Nat := 4983230072969 + 3 ^ 40 * 3235322 * 2
def baseEnd_3235322 : Nat := 1661275258065696021496031

theorem tailTrace_3235322 : CollatzResearch.WordTrace tailWord_3235322 prefixEnd_3235322 1661275258065696021496031 := by
  unfold tailWord_3235322
  simp only [CollatzResearch.WordTrace]
  refine ⟨29500471896247104463009055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78667925056658945234690813 29500471896247104463009055)
  ·
    refine ⟨44250707844370656694513583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29500471896247104463009055 44250707844370656694513583)
    ·
      refine ⟨66376061766555985041770375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44250707844370656694513583 66376061766555985041770375)
      ·
        refine ⟨99564092649833977562655563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66376061766555985041770375 99564092649833977562655563)
        ·
          refine ⟨149346138974750966343983345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99564092649833977562655563 149346138974750966343983345)
          ·
            refine ⟨112009604231063224757987509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149346138974750966343983345 112009604231063224757987509)
            ·
              refine ⟨10500900396662177321061329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112009604231063224757987509 10500900396662177321061329)
              ·
                refine ⟨7875675297496632990795997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10500900396662177321061329 7875675297496632990795997)
                ·
                  refine ⟨2953378236561237371548499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7875675297496632990795997 2953378236561237371548499)
                  ·
                    refine ⟨4430067354841856057322749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2953378236561237371548499 4430067354841856057322749)
                    ·
                      refine ⟨1661275258065696021496031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4430067354841856057322749 1661275258065696021496031)
                      ·
                        rfl

theorem cell23_3235322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_3235322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235322 prefixEnd_3235322 := by exact prefixLift 3235322
  have htrace : WordTrace (prefixWord ++ tailWord_3235322) baseStart_3235322 baseEnd_3235322 := by
    simpa [prefixWord, tailWord_3235322, baseEnd_3235322] using wordTrace_append hprefix tailTrace_3235322
  have hstable : (prefixWord ++ tailWord_3235322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235322).length < 2 ^ (prefixWord ++ tailWord_3235322).sum := by decide
  have hdescent : baseEnd_3235322 < baseStart_3235322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235325 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_3235325 : Nat := 118140960795 + 3235325 * 2 ^ 59
def prefixEnd_3235325 : Nat := 4983230072969 + 3 ^ 40 * 3235325 * 2
def baseEnd_3235325 : Nat := 553758932835886503252839

theorem tailTrace_3235325 : CollatzResearch.WordTrace tailWord_3235325 prefixEnd_3235325 553758932835886503252839 := by
  unfold tailWord_3235325
  simp only [CollatzResearch.WordTrace]
  refine ⟨118001997003977549364395429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78667998002651699576263619 118001997003977549364395429)
  ·
    refine ⟨22125374438245790505824143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118001997003977549364395429 22125374438245790505824143)
    ·
      refine ⟨33188061657368685758736215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22125374438245790505824143 33188061657368685758736215)
      ·
        refine ⟨49782092486053028638104323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33188061657368685758736215 49782092486053028638104323)
        ·
          refine ⟨74673138729079542957156485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49782092486053028638104323 74673138729079542957156485)
          ·
            refine ⟨14001213511702414304466841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74673138729079542957156485 14001213511702414304466841)
            ·
              refine ⟨10500910133776810728350131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14001213511702414304466841 10500910133776810728350131)
              ·
                refine ⟨15751365200665216092525197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10500910133776810728350131 15751365200665216092525197)
                ·
                  refine ⟨5906761950249456034696949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15751365200665216092525197 5906761950249456034696949)
                  ·
                    refine ⟨553758932835886503252839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5906761950249456034696949 553758932835886503252839)
                    ·
                      rfl

theorem cell23_3235325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_3235325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235325 prefixEnd_3235325 := by exact prefixLift 3235325
  have htrace : WordTrace (prefixWord ++ tailWord_3235325) baseStart_3235325 baseEnd_3235325 := by
    simpa [prefixWord, tailWord_3235325, baseEnd_3235325] using wordTrace_append hprefix tailTrace_3235325
  have hstable : (prefixWord ++ tailWord_3235325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235325).length < 2 ^ (prefixWord ++ tailWord_3235325).sum := by decide
  have hdescent : baseEnd_3235325 < baseStart_3235325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235379 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 3, 2, 2]
def baseStart_3235379 : Nat := 118140960795 + 3235379 * 2 ^ 59
def prefixEnd_3235379 : Nat := 4983230072969 + 3 ^ 40 * 3235379 * 2
def baseEnd_3235379 : Nat := 1661304526463002298483269

theorem tailTrace_3235379 : CollatzResearch.WordTrace tailWord_3235379 prefixEnd_3235379 1661304526463002298483269 := by
  unfold tailWord_3235379
  simp only [CollatzResearch.WordTrace]
  refine ⟨118003966545781916586861191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78669311030521277724574127 118003966545781916586861191)
  ·
    refine ⟨177005949818672874880291787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118003966545781916586861191 177005949818672874880291787)
    ·
      refine ⟨265508924728009312320437681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177005949818672874880291787 265508924728009312320437681)
      ·
        refine ⟨199131693546006984240328261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265508924728009312320437681 199131693546006984240328261)
        ·
          refine ⟨37337192539876309545061549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199131693546006984240328261 37337192539876309545061549)
          ·
            refine ⟨14001447202453616079398081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37337192539876309545061549 14001447202453616079398081)
            ·
              refine ⟨10501085401840212059548561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14001447202453616079398081 10501085401840212059548561)
              ·
                refine ⟨7875814051380159044661421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10501085401840212059548561 7875814051380159044661421)
                ·
                  refine ⟨2953430269267559641748033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7875814051380159044661421 2953430269267559641748033)
                  ·
                    refine ⟨2215072701950669731311025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2953430269267559641748033 2215072701950669731311025)
                    ·
                      refine ⟨1661304526463002298483269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2215072701950669731311025 1661304526463002298483269)
                      ·
                        rfl

theorem cell23_3235379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 2, 2].length) (baseStart_3235379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235379 prefixEnd_3235379 := by exact prefixLift 3235379
  have htrace : WordTrace (prefixWord ++ tailWord_3235379) baseStart_3235379 baseEnd_3235379 := by
    simpa [prefixWord, tailWord_3235379, baseEnd_3235379] using wordTrace_append hprefix tailTrace_3235379
  have hstable : (prefixWord ++ tailWord_3235379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235379).length < 2 ^ (prefixWord ++ tailWord_3235379).sum := by decide
  have hdescent : baseEnd_3235379 < baseStart_3235379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235385 : List Nat := [1, 2, 1, 5, 1, 3, 1, 9]
def baseStart_3235385 : Nat := 118140960795 + 3235385 * 2 ^ 59
def prefixEnd_3235385 : Nat := 4983230072969 + 3 ^ 40 * 3235385 * 2
def baseEnd_3235385 : Nat := 61529911383219602778083

theorem tailTrace_3235385 : CollatzResearch.WordTrace tailWord_3235385 prefixEnd_3235385 61529911383219602778083 := by
  unfold tailWord_3235385
  simp only [CollatzResearch.WordTrace]
  refine ⟨118004185383760179611579609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78669456922506786407719739 118004185383760179611579609)
  ·
    refine ⟨88503139037820134708684707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118004185383760179611579609 88503139037820134708684707)
    ·
      refine ⟨132754708556730202063027061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88503139037820134708684707 132754708556730202063027061)
      ·
        refine ⟨12445753927193456443408787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132754708556730202063027061 12445753927193456443408787)
        ·
          refine ⟨18668630890790184665113181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12445753927193456443408787 18668630890790184665113181)
          ·
            refine ⟨7000736584046319249417443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18668630890790184665113181 7000736584046319249417443)
            ·
              refine ⟨10501104876069478874126165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7000736584046319249417443 10501104876069478874126165)
              ·
                refine ⟨61529911383219602778083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10501104876069478874126165 61529911383219602778083)
                ·
                  rfl

theorem cell23_3235385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 9].length) (baseStart_3235385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235385 prefixEnd_3235385 := by exact prefixLift 3235385
  have htrace : WordTrace (prefixWord ++ tailWord_3235385) baseStart_3235385 baseEnd_3235385 := by
    simpa [prefixWord, tailWord_3235385, baseEnd_3235385] using wordTrace_append hprefix tailTrace_3235385
  have hstable : (prefixWord ++ tailWord_3235385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235385).length < 2 ^ (prefixWord ++ tailWord_3235385).sum := by decide
  have hdescent : baseEnd_3235385 < baseStart_3235385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235456 : List Nat := [2, 1, 1, 2, 1, 4, 5, 1, 1, 3, 2]
def baseStart_3235456 : Nat := 118140960795 + 3235456 * 2 ^ 59
def prefixEnd_3235456 : Nat := 4983230072969 + 3 ^ 40 * 3235456 * 2
def baseEnd_3235456 : Nat := 1661344064473398497220415

theorem tailTrace_3235456 : CollatzResearch.WordTrace tailWord_3235456 prefixEnd_3235456 1661344064473398497220415 := by
  unfold tailWord_3235456
  simp only [CollatzResearch.WordTrace]
  refine ⟨59003387483251479368707111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78671183311001972491609481 59003387483251479368707111)
  ·
    refine ⟨88505081224877219053060667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59003387483251479368707111 88505081224877219053060667)
    ·
      refine ⟨132757621837315828579591001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88505081224877219053060667 132757621837315828579591001)
      ·
        refine ⟨99568216377986871434693251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132757621837315828579591001 99568216377986871434693251)
        ·
          refine ⟨149352324566980307152039877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99568216377986871434693251 149352324566980307152039877)
          ·
            refine ⟨28003560856308807591007477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149352324566980307152039877 28003560856308807591007477)
            ·
              refine ⟨2625333830278950711656951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28003560856308807591007477 2625333830278950711656951)
              ·
                refine ⟨3938000745418426067485427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2625333830278950711656951 3938000745418426067485427)
                ·
                  refine ⟨5907001118127639101228141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3938000745418426067485427 5907001118127639101228141)
                  ·
                    refine ⟨2215125419297864662960553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5907001118127639101228141 2215125419297864662960553)
                    ·
                      refine ⟨1661344064473398497220415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2215125419297864662960553 1661344064473398497220415)
                      ·
                        rfl

theorem cell23_3235456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 1, 3, 2].length) (baseStart_3235456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235456 prefixEnd_3235456 := by exact prefixLift 3235456
  have htrace : WordTrace (prefixWord ++ tailWord_3235456) baseStart_3235456 baseEnd_3235456 := by
    simpa [prefixWord, tailWord_3235456, baseEnd_3235456] using wordTrace_append hprefix tailTrace_3235456
  have hstable : (prefixWord ++ tailWord_3235456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235456).length < 2 ^ (prefixWord ++ tailWord_3235456).sum := by decide
  have hdescent : baseEnd_3235456 < baseStart_3235456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235464 : List Nat := [2, 1, 3, 5, 2, 1, 2, 2, 1, 2, 2]
def baseStart_3235464 : Nat := 118140960795 + 3235464 * 2 ^ 59
def prefixEnd_3235464 : Nat := 4983230072969 + 3 ^ 40 * 3235464 * 2
def baseEnd_3235464 : Nat := 1661348172318634465920379

theorem tailTrace_3235464 : CollatzResearch.WordTrace tailWord_3235464 prefixEnd_3235464 1661348172318634465920379 := by
  unfold tailWord_3235464
  simp only [CollatzResearch.WordTrace]
  refine ⟨59003533375236988051852723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78671377833649317402470297 59003533375236988051852723)
  ·
    refine ⟨88505300062855482077779085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59003533375236988051852723 88505300062855482077779085)
    ·
      refine ⟨33189487523570805779167157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88505300062855482077779085 33189487523570805779167157)
      ·
        refine ⟨3111514455334763041796921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33189487523570805779167157 3111514455334763041796921)
        ·
          refine ⟨2333635841501072281347691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3111514455334763041796921 2333635841501072281347691)
          ·
            refine ⟨3500453762251608422021537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333635841501072281347691 3500453762251608422021537)
            ·
              refine ⟨2625340321688706316516153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3500453762251608422021537 2625340321688706316516153)
              ·
                refine ⟨1969005241266529737387115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2625340321688706316516153 1969005241266529737387115)
                ·
                  refine ⟨2953507861899794606080673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969005241266529737387115 2953507861899794606080673)
                  ·
                    refine ⟨2215130896424845954560505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2953507861899794606080673 2215130896424845954560505)
                    ·
                      refine ⟨1661348172318634465920379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2215130896424845954560505 1661348172318634465920379)
                      ·
                        rfl

theorem cell23_3235464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_3235464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235464 prefixEnd_3235464 := by exact prefixLift 3235464
  have htrace : WordTrace (prefixWord ++ tailWord_3235464) baseStart_3235464 baseEnd_3235464 := by
    simpa [prefixWord, tailWord_3235464, baseEnd_3235464] using wordTrace_append hprefix tailTrace_3235464
  have hstable : (prefixWord ++ tailWord_3235464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235464).length < 2 ^ (prefixWord ++ tailWord_3235464).sum := by decide
  have hdescent : baseEnd_3235464 < baseStart_3235464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235486 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_3235486 : Nat := 118140960795 + 3235486 * 2 ^ 59
def prefixEnd_3235486 : Nat := 4983230072969 + 3 ^ 40 * 3235486 * 2
def baseEnd_3235486 : Nat := 1661359468893033379845277

theorem tailTrace_3235486 : CollatzResearch.WordTrace tailWord_3235486 prefixEnd_3235486 1661359468893033379845277 := by
  unfold tailWord_3235486
  simp only [CollatzResearch.WordTrace]
  refine ⟨14750983644549284232625789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78671912770929515907337541 14750983644549284232625789)
  ·
    refine ⟨5531618866705981587234671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14750983644549284232625789 5531618866705981587234671)
    ·
      refine ⟨8297428300058972380852007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5531618866705981587234671 8297428300058972380852007)
      ·
        refine ⟨12446142450088458571278011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8297428300058972380852007 12446142450088458571278011)
        ·
          refine ⟨18669213675132687856917017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12446142450088458571278011 18669213675132687856917017)
          ·
            refine ⟨14001910256349515892687763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18669213675132687856917017 14001910256349515892687763)
            ·
              refine ⟨21002865384524273839031645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14001910256349515892687763 21002865384524273839031645)
              ·
                refine ⟨7876074519196602689636867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21002865384524273839031645 7876074519196602689636867)
                ·
                  refine ⟨11814111778794904034455301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7876074519196602689636867 11814111778794904034455301)
                  ·
                    refine ⟨2215145958524044506460369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11814111778794904034455301 2215145958524044506460369)
                    ·
                      refine ⟨1661359468893033379845277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2215145958524044506460369 1661359468893033379845277)
                      ·
                        rfl

theorem cell23_3235486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_3235486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235486 prefixEnd_3235486 := by exact prefixLift 3235486
  have htrace : WordTrace (prefixWord ++ tailWord_3235486) baseStart_3235486 baseEnd_3235486 := by
    simpa [prefixWord, tailWord_3235486, baseEnd_3235486] using wordTrace_append hprefix tailTrace_3235486
  have hstable : (prefixWord ++ tailWord_3235486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235486).length < 2 ^ (prefixWord ++ tailWord_3235486).sum := by decide
  have hdescent : baseEnd_3235486 < baseStart_3235486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235492 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 7]
def baseStart_3235492 : Nat := 118140960795 + 3235492 * 2 ^ 59
def prefixEnd_3235492 : Nat := 4983230072969 + 3 ^ 40 * 3235492 * 2
def baseEnd_3235492 : Nat := 184595838864106706263361

theorem tailTrace_3235492 : CollatzResearch.WordTrace tailWord_3235492 prefixEnd_3235492 184595838864106706263361 := by
  unfold tailWord_3235492
  simp only [CollatzResearch.WordTrace]
  refine ⟨59004043997186268442862365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78672058662915024590483153 59004043997186268442862365)
  ·
    refine ⟨22126516498944850666073387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59004043997186268442862365 22126516498944850666073387)
    ·
      refine ⟨33189774748417275999110081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22126516498944850666073387 33189774748417275999110081)
      ·
        refine ⟨24892331061312956999332561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33189774748417275999110081 24892331061312956999332561)
        ·
          refine ⟨18669248295984717749499421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24892331061312956999332561 18669248295984717749499421)
          ·
            refine ⟨7000968110994269156062283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18669248295984717749499421 7000968110994269156062283)
            ·
              refine ⟨10501452166491403734093425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7000968110994269156062283 10501452166491403734093425)
              ·
                refine ⟨7876089124868552800570069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10501452166491403734093425 7876089124868552800570069)
                ·
                  refine ⟨184595838864106706263361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7876089124868552800570069 184595838864106706263361)
                  ·
                    rfl

theorem cell23_3235492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_3235492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235492 prefixEnd_3235492 := by exact prefixLift 3235492
  have htrace : WordTrace (prefixWord ++ tailWord_3235492) baseStart_3235492 baseEnd_3235492 := by
    simpa [prefixWord, tailWord_3235492, baseEnd_3235492] using wordTrace_append hprefix tailTrace_3235492
  have hstable : (prefixWord ++ tailWord_3235492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235492).length < 2 ^ (prefixWord ++ tailWord_3235492).sum := by decide
  have hdescent : baseEnd_3235492 < baseStart_3235492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235515 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 5]
def baseStart_3235515 : Nat := 118140960795 + 3235515 * 2 ^ 59
def prefixEnd_3235515 : Nat := 4983230072969 + 3 ^ 40 * 3235515 * 2
def baseEnd_3235515 : Nat := 1661374359832013766382643

theorem tailTrace_3235515 : CollatzResearch.WordTrace tailWord_3235515 prefixEnd_3235515 1661374359832013766382643 := by
  unfold tailWord_3235515
  simp only [CollatzResearch.WordTrace]
  refine ⟨118008926873289211813811999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78672617915526141209207999 118008926873289211813811999)
  ·
    refine ⟨177013390309933817720717999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118008926873289211813811999 177013390309933817720717999)
    ·
      refine ⟨265520085464900726581076999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177013390309933817720717999 265520085464900726581076999)
      ·
        refine ⟨398280128197351089871615499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265520085464900726581076999 398280128197351089871615499)
        ·
          refine ⟨597420192296026634807423249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398280128197351089871615499 597420192296026634807423249)
          ·
            refine ⟨448065144222019976105567437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597420192296026634807423249 448065144222019976105567437)
            ·
              refine ⟨168024429083257491039587789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 448065144222019976105567437 168024429083257491039587789)
              ·
                refine ⟨63009160906221559139845421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168024429083257491039587789 63009160906221559139845421)
                ·
                  refine ⟨23628435339833084677442033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63009160906221559139845421 23628435339833084677442033)
                  ·
                    refine ⟨17721326504874813508081525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23628435339833084677442033 17721326504874813508081525)
                    ·
                      refine ⟨1661374359832013766382643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17721326504874813508081525 1661374359832013766382643)
                      ·
                        rfl

theorem cell23_3235515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 5].length) (baseStart_3235515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235515 prefixEnd_3235515 := by exact prefixLift 3235515
  have htrace : WordTrace (prefixWord ++ tailWord_3235515) baseStart_3235515 baseEnd_3235515 := by
    simpa [prefixWord, tailWord_3235515, baseEnd_3235515] using wordTrace_append hprefix tailTrace_3235515
  have hstable : (prefixWord ++ tailWord_3235515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235515).length < 2 ^ (prefixWord ++ tailWord_3235515).sum := by decide
  have hdescent : baseEnd_3235515 < baseStart_3235515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235526 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_3235526 : Nat := 118140960795 + 3235526 * 2 ^ 59
def prefixEnd_3235526 : Nat := 4983230072969 + 3 ^ 40 * 3235526 * 2
def baseEnd_3235526 : Nat := 184597778679912580371677

theorem tailTrace_3235526 : CollatzResearch.WordTrace tailWord_3235526 prefixEnd_3235526 184597778679912580371677 := by
  unfold tailWord_3235526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3687791502382792521639451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78672885384166240461641621 3687791502382792521639451)
  ·
    refine ⟨5531687253574188782459177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3687791502382792521639451 5531687253574188782459177)
    ·
      refine ⟨4148765440180641586844383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5531687253574188782459177 4148765440180641586844383)
      ·
        refine ⟨6223148160270962380266575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4148765440180641586844383 6223148160270962380266575)
        ·
          refine ⟨9334722240406443570399863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6223148160270962380266575 9334722240406443570399863)
          ·
            refine ⟨14002083360609665355599795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9334722240406443570399863 14002083360609665355599795)
            ·
              refine ⟨21003125040914498033399693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14002083360609665355599795 21003125040914498033399693)
              ·
                refine ⟨7876171890342936762524885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21003125040914498033399693 7876171890342936762524885)
                ·
                  refine ⟨184597778679912580371677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7876171890342936762524885 184597778679912580371677)
                  ·
                    rfl

theorem cell23_3235526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_3235526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235526 prefixEnd_3235526 := by exact prefixLift 3235526
  have htrace : WordTrace (prefixWord ++ tailWord_3235526) baseStart_3235526 baseEnd_3235526 := by
    simpa [prefixWord, tailWord_3235526, baseEnd_3235526] using wordTrace_append hprefix tailTrace_3235526
  have hstable : (prefixWord ++ tailWord_3235526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235526).length < 2 ^ (prefixWord ++ tailWord_3235526).sum := by decide
  have hdescent : baseEnd_3235526 < baseStart_3235526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235619 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 1, 5, 2]
def baseStart_3235619 : Nat := 118140960795 + 3235619 * 2 ^ 59
def prefixEnd_3235619 : Nat := 4983230072969 + 3 ^ 40 * 3235619 * 2
def baseEnd_3235619 : Nat := 1661427761820081359482165

theorem tailTrace_3235619 : CollatzResearch.WordTrace tailWord_3235619 prefixEnd_3235619 1661427761820081359482165 := by
  unfold tailWord_3235619
  simp only [CollatzResearch.WordTrace]
  refine ⟨118012720064912437575597911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78675146709941625050398607 118012720064912437575597911)
  ·
    refine ⟨177019080097368656363396867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118012720064912437575597911 177019080097368656363396867)
    ·
      refine ⟨265528620146052984545095301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177019080097368656363396867 265528620146052984545095301)
      ·
        refine ⟨49786616277384934602205369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265528620146052984545095301 49786616277384934602205369)
        ·
          refine ⟨37339962208038700951654027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49786616277384934602205369 37339962208038700951654027)
          ·
            refine ⟨56009943312058051427481041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37339962208038700951654027 56009943312058051427481041)
            ·
              refine ⟨42007457484043538570610781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56009943312058051427481041 42007457484043538570610781)
              ·
                refine ⟨15752796556516326963979043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42007457484043538570610781 15752796556516326963979043)
                ·
                  refine ⟨23629194834774490445968565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15752796556516326963979043 23629194834774490445968565)
                  ·
                    refine ⟨2215237015760108479309553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23629194834774490445968565 2215237015760108479309553)
                    ·
                      refine ⟨1661427761820081359482165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2215237015760108479309553 1661427761820081359482165)
                      ·
                        rfl

theorem cell23_3235619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_3235619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235619 prefixEnd_3235619 := by exact prefixLift 3235619
  have htrace : WordTrace (prefixWord ++ tailWord_3235619) baseStart_3235619 baseEnd_3235619 := by
    simpa [prefixWord, tailWord_3235619, baseEnd_3235619] using wordTrace_append hprefix tailTrace_3235619
  have hstable : (prefixWord ++ tailWord_3235619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235619).length < 2 ^ (prefixWord ++ tailWord_3235619).sum := by decide
  have hdescent : baseEnd_3235619 < baseStart_3235619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235637 : List Nat := [1, 3, 3, 1, 5, 1, 2, 2, 1, 4]
def baseStart_3235637 : Nat := 118140960795 + 3235637 * 2 ^ 59
def prefixEnd_3235637 : Nat := 4983230072969 + 3 ^ 40 * 3235637 * 2
def baseEnd_3235637 : Nat := 553812334823954096352361

theorem tailTrace_3235637 : CollatzResearch.WordTrace tailWord_3235637 prefixEnd_3235637 553812334823954096352361 := by
  unfold tailWord_3235637
  simp only [CollatzResearch.WordTrace]
  refine ⟨118013376578847226649753165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78675584385898151099835443 118013376578847226649753165)
  ·
    refine ⟨44255016217067709993657437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118013376578847226649753165 44255016217067709993657437)
    ·
      refine ⟨16595631081400391247621539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44255016217067709993657437 16595631081400391247621539)
      ·
        refine ⟨24893446622100586871432309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16595631081400391247621539 24893446622100586871432309)
        ·
          refine ⟨2333760620821930019196779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24893446622100586871432309 2333760620821930019196779)
          ·
            refine ⟨3500640931232895028795169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333760620821930019196779 3500640931232895028795169)
            ·
              refine ⟨2625480698424671271596377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3500640931232895028795169 2625480698424671271596377)
              ·
                refine ⟨1969110523818503453697283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2625480698424671271596377 1969110523818503453697283)
                ·
                  refine ⟨2953665785727755180545925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969110523818503453697283 2953665785727755180545925)
                  ·
                    refine ⟨553812334823954096352361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2953665785727755180545925 553812334823954096352361)
                    ·
                      rfl

theorem cell23_3235637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_3235637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235637 prefixEnd_3235637 := by exact prefixLift 3235637
  have htrace : WordTrace (prefixWord ++ tailWord_3235637) baseStart_3235637 baseEnd_3235637 := by
    simpa [prefixWord, tailWord_3235637, baseEnd_3235637] using wordTrace_append hprefix tailTrace_3235637
  have hstable : (prefixWord ++ tailWord_3235637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235637).length < 2 ^ (prefixWord ++ tailWord_3235637).sum := by decide
  have hdescent : baseEnd_3235637 < baseStart_3235637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235679 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 4]
def baseStart_3235679 : Nat := 118140960795 + 3235679 * 2 ^ 59
def prefixEnd_3235679 : Nat := 4983230072969 + 3 ^ 40 * 3235679 * 2
def baseEnd_3235679 : Nat := 1661458570659351124731889

theorem tailTrace_3235679 : CollatzResearch.WordTrace tailWord_3235679 prefixEnd_3235679 1661458570659351124731889 := by
  unfold tailWord_3235679
  simp only [CollatzResearch.WordTrace]
  refine ⟨118014908444695067822782091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78676605629796711881854727 118014908444695067822782091)
  ·
    refine ⟨177022362667042601734173137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118014908444695067822782091 177022362667042601734173137)
    ·
      refine ⟨132766772000281951300629853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177022362667042601734173137 132766772000281951300629853)
      ·
        refine ⟨49787539500105731737736195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132766772000281951300629853 49787539500105731737736195)
        ·
          refine ⟨74681309250158597606604293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49787539500105731737736195 74681309250158597606604293)
          ·
            refine ⟨14002745484404737051238305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74681309250158597606604293 14002745484404737051238305)
            ·
              refine ⟨10502059113303552788428729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14002745484404737051238305 10502059113303552788428729)
              ·
                refine ⟨7876544334977664591321547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10502059113303552788428729 7876544334977664591321547)
                ·
                  refine ⟨11814816502466496886982321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7876544334977664591321547 11814816502466496886982321)
                  ·
                    refine ⟨8861112376849872665236741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11814816502466496886982321 8861112376849872665236741)
                    ·
                      refine ⟨1661458570659351124731889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8861112376849872665236741 1661458570659351124731889)
                      ·
                        rfl

theorem cell23_3235679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_3235679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235679 prefixEnd_3235679 := by exact prefixLift 3235679
  have htrace : WordTrace (prefixWord ++ tailWord_3235679) baseStart_3235679 baseEnd_3235679 := by
    simpa [prefixWord, tailWord_3235679, baseEnd_3235679] using wordTrace_append hprefix tailTrace_3235679
  have hstable : (prefixWord ++ tailWord_3235679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235679).length < 2 ^ (prefixWord ++ tailWord_3235679).sum := by decide
  have hdescent : baseEnd_3235679 < baseStart_3235679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235716 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_3235716 : Nat := 118140960795 + 3235716 * 2 ^ 59
def prefixEnd_3235716 : Nat := 4983230072969 + 3 ^ 40 * 3235716 * 2
def baseEnd_3235716 : Nat := 1661477569443567479969219

theorem tailTrace_3235716 : CollatzResearch.WordTrace tailWord_3235716 prefixEnd_3235716 1661477569443567479969219 := by
  unfold tailWord_3235716
  simp only [CollatzResearch.WordTrace]
  refine ⟨59008128972780511570939501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78677505297040682094586001 59008128972780511570939501)
  ·
    refine ⟨22128048364792691839102313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59008128972780511570939501 22128048364792691839102313)
    ·
      refine ⟨16596036273594518879326735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22128048364792691839102313 16596036273594518879326735)
      ·
        refine ⟨24894054410391778318990103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16596036273594518879326735 24894054410391778318990103)
        ·
          refine ⟨37341081615587667478485155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24894054410391778318990103 37341081615587667478485155)
          ·
            refine ⟨56011622423381501217727733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37341081615587667478485155 56011622423381501217727733)
            ·
              refine ⟨5251089602192015739161975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56011622423381501217727733 5251089602192015739161975)
              ·
                refine ⟨7876634403288023608742963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5251089602192015739161975 7876634403288023608742963)
                ·
                  refine ⟨11814951604932035413114445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7876634403288023608742963 11814951604932035413114445)
                  ·
                    refine ⟨4430606851849513279917917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11814951604932035413114445 4430606851849513279917917)
                    ·
                      refine ⟨1661477569443567479969219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4430606851849513279917917 1661477569443567479969219)
                      ·
                        rfl

theorem cell23_3235716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_3235716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235716 prefixEnd_3235716 := by exact prefixLift 3235716
  have htrace : WordTrace (prefixWord ++ tailWord_3235716) baseStart_3235716 baseEnd_3235716 := by
    simpa [prefixWord, tailWord_3235716, baseEnd_3235716] using wordTrace_append hprefix tailTrace_3235716
  have hstable : (prefixWord ++ tailWord_3235716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235716).length < 2 ^ (prefixWord ++ tailWord_3235716).sum := by decide
  have hdescent : baseEnd_3235716 < baseStart_3235716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235759 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 3]
def baseStart_3235759 : Nat := 118140960795 + 3235759 * 2 ^ 59
def prefixEnd_3235759 : Nat := 4983230072969 + 3 ^ 40 * 3235759 * 2
def baseEnd_3235759 : Nat := 1661499649111710811731521

theorem tailTrace_3235759 : CollatzResearch.WordTrace tailWord_3235759 prefixEnd_3235759 1661499649111710811731521 := by
  unfold tailWord_3235759
  simp only [CollatzResearch.WordTrace]
  refine ⟨118017826284405241485694331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78678550856270160990462887 118017826284405241485694331)
  ·
    refine ⟨177026739426607862228541497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118017826284405241485694331 177026739426607862228541497)
    ·
      refine ⟨132770054569955896671406123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177026739426607862228541497 132770054569955896671406123)
      ·
        refine ⟨199155081854933845007109185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132770054569955896671406123 199155081854933845007109185)
        ·
          refine ⟨149366311391200383755331889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199155081854933845007109185 149366311391200383755331889)
          ·
            refine ⟨112024733543400287816498917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149366311391200383755331889 112024733543400287816498917)
            ·
              refine ⟨21004637539387553965593547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112024733543400287816498917 21004637539387553965593547)
              ·
                refine ⟨31506956309081330948390321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21004637539387553965593547 31506956309081330948390321)
                ·
                  refine ⟨23630217231810998211292741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31506956309081330948390321 23630217231810998211292741)
                  ·
                    refine ⟨4430665730964562164617389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23630217231810998211292741 4430665730964562164617389)
                    ·
                      refine ⟨1661499649111710811731521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4430665730964562164617389 1661499649111710811731521)
                      ·
                        rfl

theorem cell23_3235759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 3].length) (baseStart_3235759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235759 prefixEnd_3235759 := by exact prefixLift 3235759
  have htrace : WordTrace (prefixWord ++ tailWord_3235759) baseStart_3235759 baseEnd_3235759 := by
    simpa [prefixWord, tailWord_3235759, baseEnd_3235759] using wordTrace_append hprefix tailTrace_3235759
  have hstable : (prefixWord ++ tailWord_3235759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235759).length < 2 ^ (prefixWord ++ tailWord_3235759).sum := by decide
  have hdescent : baseEnd_3235759 < baseStart_3235759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235769 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3235769 : Nat := 118140960795 + 3235769 * 2 ^ 59
def prefixEnd_3235769 : Nat := 4983230072969 + 3 ^ 40 * 3235769 * 2
def baseEnd_3235769 : Nat := 1661504783918255772606475

theorem tailTrace_3235769 : CollatzResearch.WordTrace tailWord_3235769 prefixEnd_3235769 1661504783918255772606475 := by
  unfold tailWord_3235769
  simp only [CollatzResearch.WordTrace]
  refine ⟨118018191014369013193558361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78678794009579342129038907 118018191014369013193558361)
  ·
    refine ⟨88513643260776759895168771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118018191014369013193558361 88513643260776759895168771)
    ·
      refine ⟨132770464891165139842753157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88513643260776759895168771 132770464891165139842753157)
      ·
        refine ⟨24894462167093463720516217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132770464891165139842753157 24894462167093463720516217)
        ·
          refine ⟨18670846625320097790387163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24894462167093463720516217 18670846625320097790387163)
          ·
            refine ⟨28006269937980146685580745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18670846625320097790387163 28006269937980146685580745)
            ·
              refine ⟨21004702453485110014185559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28006269937980146685580745 21004702453485110014185559)
              ·
                refine ⟨31507053680227665021278339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21004702453485110014185559 31507053680227665021278339)
                ·
                  refine ⟨47260580520341497531917509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31507053680227665021278339 47260580520341497531917509)
                  ·
                    refine ⟨8861358847564030787234533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47260580520341497531917509 8861358847564030787234533)
                    ·
                      refine ⟨1661504783918255772606475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8861358847564030787234533 1661504783918255772606475)
                      ·
                        rfl

theorem cell23_3235769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3235769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235769 prefixEnd_3235769 := by exact prefixLift 3235769
  have htrace : WordTrace (prefixWord ++ tailWord_3235769) baseStart_3235769 baseEnd_3235769 := by
    simpa [prefixWord, tailWord_3235769, baseEnd_3235769] using wordTrace_append hprefix tailTrace_3235769
  have hstable : (prefixWord ++ tailWord_3235769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235769).length < 2 ^ (prefixWord ++ tailWord_3235769).sum := by decide
  have hdescent : baseEnd_3235769 < baseStart_3235769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235859 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 6]
def baseStart_3235859 : Nat := 118140960795 + 3235859 * 2 ^ 59
def prefixEnd_3235859 : Nat := 4983230072969 + 3 ^ 40 * 3235859 * 2
def baseEnd_3235859 : Nat := 1661550997177160420481061

theorem tailTrace_3235859 : CollatzResearch.WordTrace tailWord_3235859 prefixEnd_3235859 1661550997177160420481061 := by
  unfold tailWord_3235859
  simp only [CollatzResearch.WordTrace]
  refine ⟨118021473584042958564334631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78680982389361972376223087 118021473584042958564334631)
  ·
    refine ⟨177032210376064437846501947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118021473584042958564334631 177032210376064437846501947)
    ·
      refine ⟨265548315564096656769752921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177032210376064437846501947 265548315564096656769752921)
      ·
        refine ⟨199161236673072492577314691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265548315564096656769752921 199161236673072492577314691)
        ·
          refine ⟨298741855009608738865972037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199161236673072492577314691 298741855009608738865972037)
          ·
            refine ⟨56014097814301638537369757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 298741855009608738865972037 56014097814301638537369757)
            ·
              refine ⟨21005286680363114451513659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56014097814301638537369757 21005286680363114451513659)
              ·
                refine ⟨31507930020544671677270489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21005286680363114451513659 31507930020544671677270489)
                ·
                  refine ⟨23630947515408503757952867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31507930020544671677270489 23630947515408503757952867)
                  ·
                    refine ⟨35446421273112755636929301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23630947515408503757952867 35446421273112755636929301)
                    ·
                      refine ⟨1661550997177160420481061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35446421273112755636929301 1661550997177160420481061)
                      ·
                        rfl

theorem cell23_3235859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_3235859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235859 prefixEnd_3235859 := by exact prefixLift 3235859
  have htrace : WordTrace (prefixWord ++ tailWord_3235859) baseStart_3235859 baseEnd_3235859 := by
    simpa [prefixWord, tailWord_3235859, baseEnd_3235859] using wordTrace_append hprefix tailTrace_3235859
  have hstable : (prefixWord ++ tailWord_3235859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235859).length < 2 ^ (prefixWord ++ tailWord_3235859).sum := by decide
  have hdescent : baseEnd_3235859 < baseStart_3235859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235973 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 1, 1, 5]
def baseStart_3235973 : Nat := 118140960795 + 3235973 * 2 ^ 59
def prefixEnd_3235973 : Nat := 4983230072969 + 3 ^ 40 * 3235973 * 2
def baseEnd_3235973 : Nat := 1661609533971772974455537

theorem tailTrace_3235973 : CollatzResearch.WordTrace tailWord_3235973 prefixEnd_3235973 1661609533971772974455537 := by
  unfold tailWord_3235973
  simp only [CollatzResearch.WordTrace]
  refine ⟨118025631505629956033984573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78683754337086637355989715 118025631505629956033984573)
  ·
    refine ⟨44259611814611233512744215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118025631505629956033984573 44259611814611233512744215)
    ·
      refine ⟨66389417721916850269116323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44259611814611233512744215 66389417721916850269116323)
      ·
        refine ⟨99584126582875275403674485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66389417721916850269116323 99584126582875275403674485)
        ·
          refine ⟨9336011867144557069094483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99584126582875275403674485 9336011867144557069094483)
          ·
            refine ⟨14004017800716835603641725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9336011867144557069094483 14004017800716835603641725)
            ·
              refine ⟨5251506675268813351365647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14004017800716835603641725 5251506675268813351365647)
              ·
                refine ⟨7877260012903220027048471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5251506675268813351365647 7877260012903220027048471)
                ·
                  refine ⟨11815890019354830040572707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7877260012903220027048471 11815890019354830040572707)
                  ·
                    refine ⟨17723835029032245060859061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11815890019354830040572707 17723835029032245060859061)
                    ·
                      refine ⟨1661609533971772974455537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17723835029032245060859061 1661609533971772974455537)
                      ·
                        rfl

theorem cell23_3235973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_3235973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235973 prefixEnd_3235973 := by exact prefixLift 3235973
  have htrace : WordTrace (prefixWord ++ tailWord_3235973) baseStart_3235973 baseEnd_3235973 := by
    simpa [prefixWord, tailWord_3235973, baseEnd_3235973] using wordTrace_append hprefix tailTrace_3235973
  have hstable : (prefixWord ++ tailWord_3235973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235973).length < 2 ^ (prefixWord ++ tailWord_3235973).sum := by decide
  have hdescent : baseEnd_3235973 < baseStart_3235973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3235976 : List Nat := [2, 1, 3, 4, 1, 12]
def baseStart_3235976 : Nat := 118140960795 + 3235976 * 2 ^ 59
def prefixEnd_3235976 : Nat := 4983230072969 + 3 ^ 40 * 3235976 * 2
def baseEnd_3235976 : Nat := 6837905656023606842461

theorem tailTrace_3235976 : CollatzResearch.WordTrace tailWord_3235976 prefixEnd_3235976 6837905656023606842461 := by
  unfold tailWord_3235976
  simp only [CollatzResearch.WordTrace]
  refine ⟨59012870462309543773171891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78683827283079391697562521 59012870462309543773171891)
  ·
    refine ⟨88519305693464315659757837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59012870462309543773171891 88519305693464315659757837)
    ·
      refine ⟨33194739635049118372409189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88519305693464315659757837 33194739635049118372409189)
      ·
        refine ⟨6224013681571709694826723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33194739635049118372409189 6224013681571709694826723)
        ·
          refine ⟨9336020522357564542240085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224013681571709694826723 9336020522357564542240085)
          ·
            refine ⟨6837905656023606842461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9336020522357564542240085 6837905656023606842461)
            ·
              rfl

theorem cell23_3235976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 12].length) (baseStart_3235976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3235976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3235976 prefixEnd_3235976 := by exact prefixLift 3235976
  have htrace : WordTrace (prefixWord ++ tailWord_3235976) baseStart_3235976 baseEnd_3235976 := by
    simpa [prefixWord, tailWord_3235976, baseEnd_3235976] using wordTrace_append hprefix tailTrace_3235976
  have hstable : (prefixWord ++ tailWord_3235976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3235976).length < 2 ^ (prefixWord ++ tailWord_3235976).sum := by decide
  have hdescent : baseEnd_3235976 < baseStart_3235976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3235976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236003 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 8, 1, 3]
def baseStart_3236003 : Nat := 118140960795 + 3236003 * 2 ^ 59
def prefixEnd_3236003 : Nat := 4983230072969 + 3 ^ 40 * 3236003 * 2
def baseEnd_3236003 : Nat := 1661624938391407857080399

theorem tailTrace_3236003 : CollatzResearch.WordTrace tailWord_3236003 prefixEnd_3236003 1661624938391407857080399 := by
  unfold tailWord_3236003
  simp only [CollatzResearch.WordTrace]
  refine ⟨118026725695521271157576663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78684483797014180771717775 118026725695521271157576663)
  ·
    refine ⟨177040088543281906736364995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118026725695521271157576663 177040088543281906736364995)
    ·
      refine ⟨265560132814922860104547493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177040088543281906736364995 265560132814922860104547493)
      ·
        refine ⟨49792524902798036269602655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265560132814922860104547493 49792524902798036269602655)
        ·
          refine ⟨74688787354197054404403983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49792524902798036269602655 74688787354197054404403983)
          ·
            refine ⟨112033181031295581606605975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74688787354197054404403983 112033181031295581606605975)
            ·
              refine ⟨168049771546943372409908963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112033181031295581606605975 168049771546943372409908963)
              ·
                refine ⟨252074657320415058614863445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168049771546943372409908963 252074657320415058614863445)
                ·
                  refine ⟨2953999890473613968142931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 252074657320415058614863445 2953999890473613968142931)
                  ·
                    refine ⟨4430999835710420952214397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2953999890473613968142931 4430999835710420952214397)
                    ·
                      refine ⟨1661624938391407857080399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4430999835710420952214397 1661624938391407857080399)
                      ·
                        rfl

theorem cell23_3236003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_3236003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236003 prefixEnd_3236003 := by exact prefixLift 3236003
  have htrace : WordTrace (prefixWord ++ tailWord_3236003) baseStart_3236003 baseEnd_3236003 := by
    simpa [prefixWord, tailWord_3236003, baseEnd_3236003] using wordTrace_append hprefix tailTrace_3236003
  have hstable : (prefixWord ++ tailWord_3236003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236003).length < 2 ^ (prefixWord ++ tailWord_3236003).sum := by decide
  have hdescent : baseEnd_3236003 < baseStart_3236003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236021 : List Nat := [1, 3, 3, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_3236021 : Nat := 118140960795 + 3236021 * 2 ^ 59
def prefixEnd_3236021 : Nat := 4983230072969 + 3 ^ 40 * 3236021 * 2
def baseEnd_3236021 : Nat := 1661634181043188786655317

theorem tailTrace_3236021 : CollatzResearch.WordTrace tailWord_3236021 prefixEnd_3236021 1661634181043188786655317 := by
  unfold tailWord_3236021
  simp only [CollatzResearch.WordTrace]
  refine ⟨118027382209456060231731917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78684921472970706821154611 118027382209456060231731917)
  ·
    refine ⟨44260268328546022586899469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118027382209456060231731917 44260268328546022586899469)
    ·
      refine ⟨16597600623204758470087301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44260268328546022586899469 16597600623204758470087301)
      ·
        refine ⟨3112050116850892213141369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16597600623204758470087301 3112050116850892213141369)
        ·
          refine ⟨2334037587638169159856027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3112050116850892213141369 2334037587638169159856027)
          ·
            refine ⟨3501056381457253739784041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334037587638169159856027 3501056381457253739784041)
            ·
              refine ⟨2625792286092940304838031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3501056381457253739784041 2625792286092940304838031)
              ·
                refine ⟨3938688429139410457257047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2625792286092940304838031 3938688429139410457257047)
                ·
                  refine ⟨5908032643709115685885571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3938688429139410457257047 5908032643709115685885571)
                  ·
                    refine ⟨8862048965563673528828357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5908032643709115685885571 8862048965563673528828357)
                    ·
                      refine ⟨1661634181043188786655317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8862048965563673528828357 1661634181043188786655317)
                      ·
                        rfl

theorem cell23_3236021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_3236021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236021 prefixEnd_3236021 := by exact prefixLift 3236021
  have htrace : WordTrace (prefixWord ++ tailWord_3236021) baseStart_3236021 baseEnd_3236021 := by
    simpa [prefixWord, tailWord_3236021, baseEnd_3236021] using wordTrace_append hprefix tailTrace_3236021
  have hstable : (prefixWord ++ tailWord_3236021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236021).length < 2 ^ (prefixWord ++ tailWord_3236021).sum := by decide
  have hdescent : baseEnd_3236021 < baseStart_3236021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236054 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_3236054 : Nat := 118140960795 + 3236054 * 2 ^ 59
def prefixEnd_3236054 : Nat := 4983230072969 + 3 ^ 40 * 3236054 * 2
def baseEnd_3236054 : Nat := 1661651125904787157542665

theorem tailTrace_3236054 : CollatzResearch.WordTrace tailWord_3236054 prefixEnd_3236054 1661651125904787157542665 := by
  unfold tailWord_3236054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7376786613646031679230201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78685723878891004578455477 7376786613646031679230201)
  ·
    refine ⟨5532589960234523759422651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7376786613646031679230201 5532589960234523759422651)
    ·
      refine ⟨8298884940351785639133977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5532589960234523759422651 8298884940351785639133977)
      ·
        refine ⟨6224163705263839229350483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8298884940351785639133977 6224163705263839229350483)
        ·
          refine ⟨9336245557895758844025725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224163705263839229350483 9336245557895758844025725)
          ·
            refine ⟨3501092084210909566509647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9336245557895758844025725 3501092084210909566509647)
            ·
              refine ⟨5251638126316364349764471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501092084210909566509647 5251638126316364349764471)
              ·
                refine ⟨7877457189474546524646707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5251638126316364349764471 7877457189474546524646707)
                ·
                  refine ⟨11816185784211819786970061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7877457189474546524646707 11816185784211819786970061)
                  ·
                    refine ⟨4431069669079432420113773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11816185784211819786970061 4431069669079432420113773)
                    ·
                      refine ⟨1661651125904787157542665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4431069669079432420113773 1661651125904787157542665)
                      ·
                        rfl

theorem cell23_3236054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_3236054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236054 prefixEnd_3236054 := by exact prefixLift 3236054
  have htrace : WordTrace (prefixWord ++ tailWord_3236054) baseStart_3236054 baseEnd_3236054 := by
    simpa [prefixWord, tailWord_3236054, baseEnd_3236054] using wordTrace_append hprefix tailTrace_3236054
  have hstable : (prefixWord ++ tailWord_3236054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236054).length < 2 ^ (prefixWord ++ tailWord_3236054).sum := by decide
  have hdescent : baseEnd_3236054 < baseStart_3236054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236093 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_3236093 : Nat := 118140960795 + 3236093 * 2 ^ 59
def prefixEnd_3236093 : Nat := 4983230072969 + 3 ^ 40 * 3236093 * 2
def baseEnd_3236093 : Nat := 1661671151650312504954985

theorem tailTrace_3236093 : CollatzResearch.WordTrace tailWord_3236093 prefixEnd_3236093 1661671151650312504954985 := by
  unfold tailWord_3236093
  simp only [CollatzResearch.WordTrace]
  refine ⟨118030008265195216528352933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78686672176796811018901955 118030008265195216528352933)
  ·
    refine ⟨22130626549724103099066175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118030008265195216528352933 22130626549724103099066175)
    ·
      refine ⟨33195939824586154648599263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22130626549724103099066175 33195939824586154648599263)
      ·
        refine ⟨49793909736879231972898895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33195939824586154648599263 49793909736879231972898895)
        ·
          refine ⟨74690864605318847959348343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49793909736879231972898895 74690864605318847959348343)
          ·
            refine ⟨112036296907978271939022515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74690864605318847959348343 112036296907978271939022515)
            ·
              refine ⟨168054445361967407908533773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112036296907978271939022515 168054445361967407908533773)
              ·
                refine ⟨63020417010737777965700165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168054445361967407908533773 63020417010737777965700165)
                ·
                  refine ⟨11816328189513333368568781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63020417010737777965700165 11816328189513333368568781)
                  ·
                    refine ⟨4431123071067500013213293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11816328189513333368568781 4431123071067500013213293)
                    ·
                      refine ⟨1661671151650312504954985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4431123071067500013213293 1661671151650312504954985)
                      ·
                        rfl

theorem cell23_3236093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_3236093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236093 prefixEnd_3236093 := by exact prefixLift 3236093
  have htrace : WordTrace (prefixWord ++ tailWord_3236093) baseStart_3236093 baseEnd_3236093 := by
    simpa [prefixWord, tailWord_3236093, baseEnd_3236093] using wordTrace_append hprefix tailTrace_3236093
  have hstable : (prefixWord ++ tailWord_3236093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236093).length < 2 ^ (prefixWord ++ tailWord_3236093).sum := by decide
  have hdescent : baseEnd_3236093 < baseStart_3236093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236094 : List Nat := [4, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_3236094 : Nat := 118140960795 + 3236094 * 2 ^ 59
def prefixEnd_3236094 : Nat := 4983230072969 + 3 ^ 40 * 3236094 * 2
def baseEnd_3236094 : Nat := 1661671665130967001042481

theorem tailTrace_3236094 : CollatzResearch.WordTrace tailWord_3236094 prefixEnd_3236094 1661671665130967001042481 := by
  unfold tailWord_3236094
  simp only [CollatzResearch.WordTrace]
  refine ⟨14753755592273949212392417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78686696492127729132759557 14753755592273949212392417)
  ·
    refine ⟨11065316694205461909294313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14753755592273949212392417 11065316694205461909294313)
    ·
      refine ⟨8298987520654096431970735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11065316694205461909294313 8298987520654096431970735)
      ·
        refine ⟨12448481280981144647956103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8298987520654096431970735 12448481280981144647956103)
        ·
          refine ⟨18672721921471716971934155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12448481280981144647956103 18672721921471716971934155)
          ·
            refine ⟨28009082882207575457901233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18672721921471716971934155 28009082882207575457901233)
            ·
              refine ⟨21006812161655681593425925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28009082882207575457901233 21006812161655681593425925)
              ·
                refine ⟨3938777280310440298767361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21006812161655681593425925 3938777280310440298767361)
                ·
                  refine ⟨2954082960232830224075521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3938777280310440298767361 2954082960232830224075521)
                  ·
                    refine ⟨2215562220174622668056641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2954082960232830224075521 2215562220174622668056641)
                    ·
                      refine ⟨1661671665130967001042481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2215562220174622668056641 1661671665130967001042481)
                      ·
                        rfl

theorem cell23_3236094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_3236094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236094 prefixEnd_3236094 := by exact prefixLift 3236094
  have htrace : WordTrace (prefixWord ++ tailWord_3236094) baseStart_3236094 baseEnd_3236094 := by
    simpa [prefixWord, tailWord_3236094, baseEnd_3236094] using wordTrace_append hprefix tailTrace_3236094
  have hstable : (prefixWord ++ tailWord_3236094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236094).length < 2 ^ (prefixWord ++ tailWord_3236094).sum := by decide
  have hdescent : baseEnd_3236094 < baseStart_3236094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236130 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_3236130 : Nat := 118140960795 + 3236130 * 2 ^ 59
def prefixEnd_3236130 : Nat := 4983230072969 + 3 ^ 40 * 3236130 * 2
def baseEnd_3236130 : Nat := 553896716811509620064105

theorem tailTrace_3236130 : CollatzResearch.WordTrace tailWord_3236130 prefixEnd_3236130 553896716811509620064105 := by
  unfold tailWord_3236130
  simp only [CollatzResearch.WordTrace]
  refine ⟨29507839441515292961862461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78687571844040781231633229 29507839441515292961862461)
  ·
    refine ⟨11065439790568234860698423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29507839441515292961862461 11065439790568234860698423)
    ·
      refine ⟨16598159685852352291047635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11065439790568234860698423 16598159685852352291047635)
      ·
        refine ⟨24897239528778528436571453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16598159685852352291047635 24897239528778528436571453)
        ·
          refine ⟨9336464823291948163714295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24897239528778528436571453 9336464823291948163714295)
          ·
            refine ⟨14004697234937922245571443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9336464823291948163714295 14004697234937922245571443)
            ·
              refine ⟨21007045852406883368357165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14004697234937922245571443 21007045852406883368357165)
              ·
                refine ⟨7877642194652581263133937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21007045852406883368357165 7877642194652581263133937)
                ·
                  refine ⟨5908231645989435947350453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7877642194652581263133937 5908231645989435947350453)
                  ·
                    refine ⟨553896716811509620064105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5908231645989435947350453 553896716811509620064105)
                    ·
                      rfl

theorem cell23_3236130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_3236130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236130 prefixEnd_3236130 := by exact prefixLift 3236130
  have htrace : WordTrace (prefixWord ++ tailWord_3236130) baseStart_3236130 baseEnd_3236130 := by
    simpa [prefixWord, tailWord_3236130, baseEnd_3236130] using wordTrace_append hprefix tailTrace_3236130
  have hstable : (prefixWord ++ tailWord_3236130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236130).length < 2 ^ (prefixWord ++ tailWord_3236130).sum := by decide
  have hdescent : baseEnd_3236130 < baseStart_3236130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236194 : List Nat := [3, 3, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3236194 : Nat := 118140960795 + 3236194 * 2 ^ 59
def prefixEnd_3236194 : Nat := 4983230072969 + 3 ^ 40 * 3236194 * 2
def baseEnd_3236194 : Nat := 553907671065472203264007

theorem tailTrace_3236194 : CollatzResearch.WordTrace tailWord_3236194 prefixEnd_3236194 553907671065472203264007 := by
  unfold tailWord_3236194
  simp only [CollatzResearch.WordTrace]
  refine ⟨29508423009457327694444909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78689128025219540518519757 29508423009457327694444909)
  ·
    refine ⟨11065658628546497885416841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29508423009457327694444909 11065658628546497885416841)
    ·
      refine ⟨8299243971409873414062631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11065658628546497885416841 8299243971409873414062631)
      ·
        refine ⟨12448865957114810121093947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8299243971409873414062631 12448865957114810121093947)
        ·
          refine ⟨18673298935672215181640921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12448865957114810121093947 18673298935672215181640921)
          ·
            refine ⟨14004974201754161386230691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18673298935672215181640921 14004974201754161386230691)
            ·
              refine ⟨21007461302631242079346037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14004974201754161386230691 21007461302631242079346037)
              ·
                refine ⟨1969449497121678944938691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21007461302631242079346037 1969449497121678944938691)
                ·
                  refine ⟨2954174245682518417408037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969449497121678944938691 2954174245682518417408037)
                  ·
                    refine ⟨553907671065472203264007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2954174245682518417408037 553907671065472203264007)
                    ·
                      rfl

theorem cell23_3236194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3236194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236194 prefixEnd_3236194 := by exact prefixLift 3236194
  have htrace : WordTrace (prefixWord ++ tailWord_3236194) baseStart_3236194 baseEnd_3236194 := by
    simpa [prefixWord, tailWord_3236194, baseEnd_3236194] using wordTrace_append hprefix tailTrace_3236194
  have hstable : (prefixWord ++ tailWord_3236194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236194).length < 2 ^ (prefixWord ++ tailWord_3236194).sum := by decide
  have hdescent : baseEnd_3236194 < baseStart_3236194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236254 : List Nat := [4, 3, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_3236254 : Nat := 118140960795 + 3236254 * 2 ^ 59
def prefixEnd_3236254 : Nat := 4983230072969 + 3 ^ 40 * 3236254 * 2
def baseEnd_3236254 : Nat := 553917940678562125013915

theorem tailTrace_3236254 : CollatzResearch.WordTrace tailWord_3236254 prefixEnd_3236254 553917940678562125013915 := by
  unfold tailWord_3236254
  simp only [CollatzResearch.WordTrace]
  refine ⟨14754485052201492628120477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78690586945074627349975877 14754485052201492628120477)
  ·
    refine ⟨5532931894575559735545179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14754485052201492628120477 5532931894575559735545179)
    ·
      refine ⟨8299397841863339603317769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5532931894575559735545179 8299397841863339603317769)
      ·
        refine ⟨6224548381397504702488327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8299397841863339603317769 6224548381397504702488327)
        ·
          refine ⟨9336822572096257053732491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224548381397504702488327 9336822572096257053732491)
          ·
            refine ⟨14005233858144385580598737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9336822572096257053732491 14005233858144385580598737)
            ·
              refine ⟨10503925393608289185449053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14005233858144385580598737 10503925393608289185449053)
              ·
                refine ⟨3938972022603108444543395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10503925393608289185449053 3938972022603108444543395)
                ·
                  refine ⟨5908458033904662666815093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3938972022603108444543395 5908458033904662666815093)
                  ·
                    refine ⟨553917940678562125013915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5908458033904662666815093 553917940678562125013915)
                    ·
                      rfl

theorem cell23_3236254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_3236254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236254 prefixEnd_3236254 := by exact prefixLift 3236254
  have htrace : WordTrace (prefixWord ++ tailWord_3236254) baseStart_3236254 baseEnd_3236254 := by
    simpa [prefixWord, tailWord_3236254, baseEnd_3236254] using wordTrace_append hprefix tailTrace_3236254
  have hstable : (prefixWord ++ tailWord_3236254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236254).length < 2 ^ (prefixWord ++ tailWord_3236254).sum := by decide
  have hdescent : baseEnd_3236254 < baseStart_3236254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236260 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_3236260 : Nat := 118140960795 + 3236260 * 2 ^ 59
def prefixEnd_3236260 : Nat := 4983230072969 + 3 ^ 40 * 3236260 * 2
def baseEnd_3236260 : Nat := 1661756902919613351566717

theorem tailTrace_3236260 : CollatzResearch.WordTrace tailWord_3236260 prefixEnd_3236260 1661756902919613351566717 := by
  unfold tailWord_3236260
  simp only [CollatzResearch.WordTrace]
  refine ⟨59018049627795102024841117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78690732837060136033121489 59018049627795102024841117)
  ·
    refine ⟨22131768610423163259315419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59018049627795102024841117 22131768610423163259315419)
    ·
      refine ⟨33197652915634744888973129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22131768610423163259315419 33197652915634744888973129)
      ·
        refine ⟨24898239686726058666729847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33197652915634744888973129 24898239686726058666729847)
        ·
          refine ⟨37347359530089088000094771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24898239686726058666729847 37347359530089088000094771)
          ·
            refine ⟨56021039295133632000142157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37347359530089088000094771 56021039295133632000142157)
            ·
              refine ⟨21007889735675112000053309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56021039295133632000142157 21007889735675112000053309)
              ·
                refine ⟨7877958650878167000019991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21007889735675112000053309 7877958650878167000019991)
                ·
                  refine ⟨11816937976317250500029987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7877958650878167000019991 11816937976317250500029987)
                  ·
                    refine ⟨17725406964475875750044981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11816937976317250500029987 17725406964475875750044981)
                    ·
                      refine ⟨1661756902919613351566717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17725406964475875750044981 1661756902919613351566717)
                      ·
                        rfl

theorem cell23_3236260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_3236260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236260 prefixEnd_3236260 := by exact prefixLift 3236260
  have htrace : WordTrace (prefixWord ++ tailWord_3236260) baseStart_3236260 baseEnd_3236260 := by
    simpa [prefixWord, tailWord_3236260, baseEnd_3236260] using wordTrace_append hprefix tailTrace_3236260
  have hstable : (prefixWord ++ tailWord_3236260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236260).length < 2 ^ (prefixWord ++ tailWord_3236260).sum := by decide
  have hdescent : baseEnd_3236260 < baseStart_3236260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236284 : List Nat := [2, 2, 2, 4, 1, 2, 1, 3, 2, 4]
def baseStart_3236284 : Nat := 118140960795 + 3236284 * 2 ^ 59
def prefixEnd_3236284 : Nat := 4983230072969 + 3 ^ 40 * 3236284 * 2
def baseEnd_3236284 : Nat := 553923075485107085888869

theorem tailTrace_3236284 : CollatzResearch.WordTrace tailWord_3236284 prefixEnd_3236284 553923075485107085888869 := by
  unfold tailWord_3236284
  simp only [CollatzResearch.WordTrace]
  refine ⟨59018487303751628074277953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78691316405002170765703937 59018487303751628074277953)
  ·
    refine ⟨44263865477813721055708465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59018487303751628074277953 44263865477813721055708465)
    ·
      refine ⟨33197899108360290791781349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44263865477813721055708465 33197899108360290791781349)
      ·
        refine ⟨6224606082817554523459003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33197899108360290791781349 6224606082817554523459003)
        ·
          refine ⟨9336909124226331785188505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224606082817554523459003 9336909124226331785188505)
          ·
            refine ⟨7002681843169748838891379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9336909124226331785188505 7002681843169748838891379)
            ·
              refine ⟨10504022764754623258337069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7002681843169748838891379 10504022764754623258337069)
              ·
                refine ⟨3939008536782983721876401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10504022764754623258337069 3939008536782983721876401)
                ·
                  refine ⟨2954256402587237791407301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3939008536782983721876401 2954256402587237791407301)
                  ·
                    refine ⟨553923075485107085888869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2954256402587237791407301 553923075485107085888869)
                    ·
                      rfl

theorem cell23_3236284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_3236284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236284 prefixEnd_3236284 := by exact prefixLift 3236284
  have htrace : WordTrace (prefixWord ++ tailWord_3236284) baseStart_3236284 baseEnd_3236284 := by
    simpa [prefixWord, tailWord_3236284, baseEnd_3236284] using wordTrace_append hprefix tailTrace_3236284
  have hstable : (prefixWord ++ tailWord_3236284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236284).length < 2 ^ (prefixWord ++ tailWord_3236284).sum := by decide
  have hdescent : baseEnd_3236284 < baseStart_3236284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236334 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_3236334 : Nat := 118140960795 + 3236334 * 2 ^ 59
def prefixEnd_3236334 : Nat := 4983230072969 + 3 ^ 40 * 3236334 * 2
def baseEnd_3236334 : Nat := 1661794900488046062041377

theorem tailTrace_3236334 : CollatzResearch.WordTrace tailWord_3236334 prefixEnd_3236334 1661794900488046062041377 := by
  unfold tailWord_3236334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14754849782165264335984507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78692532171548076458584037 14754849782165264335984507)
  ·
    refine ⟨22132274673247896503976761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14754849782165264335984507 22132274673247896503976761)
    ·
      refine ⟨16599206004935922377982571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22132274673247896503976761 16599206004935922377982571)
      ·
        refine ⟨24898809007403883566973857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16599206004935922377982571 24898809007403883566973857)
        ·
          refine ⟨18674106755552912675230393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24898809007403883566973857 18674106755552912675230393)
          ·
            refine ⟨14005580066664684506422795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18674106755552912675230393 14005580066664684506422795)
            ·
              refine ⟨21008370099997026759634193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14005580066664684506422795 21008370099997026759634193)
              ·
                refine ⟨15756277574997770069725645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21008370099997026759634193 15756277574997770069725645)
                ·
                  refine ⟨5908604090624163776147117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15756277574997770069725645 5908604090624163776147117)
                  ·
                    refine ⟨2215726533984061416055169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5908604090624163776147117 2215726533984061416055169)
                    ·
                      refine ⟨1661794900488046062041377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2215726533984061416055169 1661794900488046062041377)
                      ·
                        rfl

theorem cell23_3236334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_3236334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236334 prefixEnd_3236334 := by exact prefixLift 3236334
  have htrace : WordTrace (prefixWord ++ tailWord_3236334) baseStart_3236334 baseEnd_3236334 := by
    simpa [prefixWord, tailWord_3236334, baseEnd_3236334] using wordTrace_append hprefix tailTrace_3236334
  have hstable : (prefixWord ++ tailWord_3236334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236334).length < 2 ^ (prefixWord ++ tailWord_3236334).sum := by decide
  have hdescent : baseEnd_3236334 < baseStart_3236334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236341 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3236341 : Nat := 118140960795 + 3236341 * 2 ^ 59
def prefixEnd_3236341 : Nat := 4983230072969 + 3 ^ 40 * 3236341 * 2
def baseEnd_3236341 : Nat := 1661798494852627534653845

theorem tailTrace_3236341 : CollatzResearch.WordTrace tailWord_3236341 prefixEnd_3236341 1661798494852627534653845 := by
  unfold tailWord_3236341
  simp only [CollatzResearch.WordTrace]
  refine ⟨118039053568296754883380877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78692702378864503255587251 118039053568296754883380877)
  ·
    refine ⟨44264645088111283081267829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118039053568296754883380877 44264645088111283081267829)
    ·
      refine ⟨4149810477010432788868859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44264645088111283081267829 4149810477010432788868859)
      ·
        refine ⟨6224715715515649183303289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4149810477010432788868859 6224715715515649183303289)
        ·
          refine ⟨4668536786636736887477467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6224715715515649183303289 4668536786636736887477467)
          ·
            refine ⟨7002805179955105331216201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4668536786636736887477467 7002805179955105331216201)
            ·
              refine ⟨5252103884966328998412151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7002805179955105331216201 5252103884966328998412151)
              ·
                refine ⟨7878155827449493497618227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5252103884966328998412151 7878155827449493497618227)
                ·
                  refine ⟨11817233741174240246427341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7878155827449493497618227 11817233741174240246427341)
                  ·
                    refine ⟨4431462652940340092410253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11817233741174240246427341 4431462652940340092410253)
                    ·
                      refine ⟨1661798494852627534653845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4431462652940340092410253 1661798494852627534653845)
                      ·
                        rfl

theorem cell23_3236341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3236341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236341 prefixEnd_3236341 := by exact prefixLift 3236341
  have htrace : WordTrace (prefixWord ++ tailWord_3236341) baseStart_3236341 baseEnd_3236341 := by
    simpa [prefixWord, tailWord_3236341, baseEnd_3236341] using wordTrace_append hprefix tailTrace_3236341
  have hstable : (prefixWord ++ tailWord_3236341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236341).length < 2 ^ (prefixWord ++ tailWord_3236341).sum := by decide
  have hdescent : baseEnd_3236341 < baseStart_3236341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236358 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_3236358 : Nat := 118140960795 + 3236358 * 2 ^ 59
def prefixEnd_3236358 : Nat := 4983230072969 + 3 ^ 40 * 3236358 * 2
def baseEnd_3236358 : Nat := 1661807224023753968141267

theorem tailTrace_3236358 : CollatzResearch.WordTrace tailWord_3236358 prefixEnd_3236358 1661807224023753968141267 := by
  unfold tailWord_3236358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3688739800288598962085929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78693115739490111191166485 3688739800288598962085929)
  ·
    refine ⟨2766554850216449221564447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3688739800288598962085929 2766554850216449221564447)
    ·
      refine ⟨4149832275324673832346671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2766554850216449221564447 4149832275324673832346671)
      ·
        refine ⟨6224748412987010748520007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4149832275324673832346671 6224748412987010748520007)
        ·
          refine ⟨9337122619480516122780011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6224748412987010748520007 9337122619480516122780011)
          ·
            refine ⟨14005683929220774184170017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9337122619480516122780011 14005683929220774184170017)
            ·
              refine ⟨10504262946915580638127513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14005683929220774184170017 10504262946915580638127513)
              ·
                refine ⟨7878197210186685478595635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10504262946915580638127513 7878197210186685478595635)
                ·
                  refine ⟨11817295815280028217893453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7878197210186685478595635 11817295815280028217893453)
                  ·
                    refine ⟨4431485930730010581710045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11817295815280028217893453 4431485930730010581710045)
                    ·
                      refine ⟨1661807224023753968141267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4431485930730010581710045 1661807224023753968141267)
                      ·
                        rfl

theorem cell23_3236358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_3236358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236358 prefixEnd_3236358 := by exact prefixLift 3236358
  have htrace : WordTrace (prefixWord ++ tailWord_3236358) baseStart_3236358 baseEnd_3236358 := by
    simpa [prefixWord, tailWord_3236358, baseEnd_3236358] using wordTrace_append hprefix tailTrace_3236358
  have hstable : (prefixWord ++ tailWord_3236358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236358).length < 2 ^ (prefixWord ++ tailWord_3236358).sum := by decide
  have hdescent : baseEnd_3236358 < baseStart_3236358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236360 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_3236360 : Nat := 118140960795 + 3236360 * 2 ^ 59
def prefixEnd_3236360 : Nat := 4983230072969 + 3 ^ 40 * 3236360 * 2
def baseEnd_3236360 : Nat := 1661808250985062960316257

theorem tailTrace_3236360 : CollatzResearch.WordTrace tailWord_3236360 prefixEnd_3236360 1661808250985062960316257 := by
  unfold tailWord_3236360
  simp only [CollatzResearch.WordTrace]
  refine ⟨59019873277613960564161267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78693164370151947418881689 59019873277613960564161267)
  ·
    refine ⟨88529809916420940846241901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59019873277613960564161267 88529809916420940846241901)
    ·
      refine ⟨33198678718657852817340713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88529809916420940846241901 33198678718657852817340713)
      ·
        refine ⟨24899009038993389613005535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33198678718657852817340713 24899009038993389613005535)
        ·
          refine ⟨37348513558490084419508303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24899009038993389613005535 37348513558490084419508303)
          ·
            refine ⟨56022770337735126629262455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37348513558490084419508303 56022770337735126629262455)
            ·
              refine ⟨84034155506602689943893683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56022770337735126629262455 84034155506602689943893683)
              ·
                refine ⟨126051233259904034915840525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84034155506602689943893683 126051233259904034915840525)
                ·
                  refine ⟨47269212472464013093440197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126051233259904034915840525 47269212472464013093440197)
                  ·
                    refine ⟨8862977338587002455020037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47269212472464013093440197 8862977338587002455020037)
                    ·
                      refine ⟨1661808250985062960316257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8862977338587002455020037 1661808250985062960316257)
                      ·
                        rfl

theorem cell23_3236360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_3236360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236360 prefixEnd_3236360 := by exact prefixLift 3236360
  have htrace : WordTrace (prefixWord ++ tailWord_3236360) baseStart_3236360 baseEnd_3236360 := by
    simpa [prefixWord, tailWord_3236360, baseEnd_3236360] using wordTrace_append hprefix tailTrace_3236360
  have hstable : (prefixWord ++ tailWord_3236360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236360).length < 2 ^ (prefixWord ++ tailWord_3236360).sum := by decide
  have hdescent : baseEnd_3236360 < baseStart_3236360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236364 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 1, 4, 2]
def baseStart_3236364 : Nat := 118140960795 + 3236364 * 2 ^ 59
def prefixEnd_3236364 : Nat := 4983230072969 + 3 ^ 40 * 3236364 * 2
def baseEnd_3236364 : Nat := 1661810304907680944666239

theorem tailTrace_3236364 : CollatzResearch.WordTrace tailWord_3236364 prefixEnd_3236364 1661810304907680944666239 := by
  unfold tailWord_3236364
  simp only [CollatzResearch.WordTrace]
  refine ⟨59019946223606714905734073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78693261631475619874312097 59019946223606714905734073)
  ·
    refine ⟨44264959667705036179300555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59019946223606714905734073 44264959667705036179300555)
    ·
      refine ⟨66397439501557554268950833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44264959667705036179300555 66397439501557554268950833)
      ·
        refine ⟨49798079626168165701713125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66397439501557554268950833 49798079626168165701713125)
        ·
          refine ⟨9337139929906531069071211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49798079626168165701713125 9337139929906531069071211)
          ·
            refine ⟨14005709894859796603606817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9337139929906531069071211 14005709894859796603606817)
            ·
              refine ⟨10504282421144847452705113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14005709894859796603606817 10504282421144847452705113)
              ·
                refine ⟨7878211815858635589528835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10504282421144847452705113 7878211815858635589528835)
                ·
                  refine ⟨11817317723787953384293253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7878211815858635589528835 11817317723787953384293253)
                  ·
                    refine ⟨2215747073210241259554985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11817317723787953384293253 2215747073210241259554985)
                    ·
                      refine ⟨1661810304907680944666239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2215747073210241259554985 1661810304907680944666239)
                      ·
                        rfl

theorem cell23_3236364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_3236364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236364 prefixEnd_3236364 := by exact prefixLift 3236364
  have htrace : WordTrace (prefixWord ++ tailWord_3236364) baseStart_3236364 baseEnd_3236364 := by
    simpa [prefixWord, tailWord_3236364, baseEnd_3236364] using wordTrace_append hprefix tailTrace_3236364
  have hstable : (prefixWord ++ tailWord_3236364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236364).length < 2 ^ (prefixWord ++ tailWord_3236364).sum := by decide
  have hdescent : baseEnd_3236364 < baseStart_3236364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236375 : List Nat := [1, 1, 3, 6, 2, 1, 1, 2, 2, 1, 3]
def baseStart_3236375 : Nat := 118140960795 + 3236375 * 2 ^ 59
def prefixEnd_3236375 : Nat := 4983230072969 + 3 ^ 40 * 3236375 * 2
def baseEnd_3236375 : Nat := 1661815953194880401628689

theorem tailTrace_3236375 : CollatzResearch.WordTrace tailWord_3236375 prefixEnd_3236375 1661815953194880401628689 := by
  unfold tailWord_3236375
  simp only [CollatzResearch.WordTrace]
  refine ⟨118040293650173578690118579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78693529100115719126745719 118040293650173578690118579)
  ·
    refine ⟨177060440475260368035177869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118040293650173578690118579 177060440475260368035177869)
    ·
      refine ⟨66397665178222638013191701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177060440475260368035177869 66397665178222638013191701)
      ·
        refine ⟨3112390555229186156868361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66397665178222638013191701 3112390555229186156868361)
        ·
          refine ⟨2334292916421889617651271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3112390555229186156868361 2334292916421889617651271)
          ·
            refine ⟨3501439374632834426476907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334292916421889617651271 3501439374632834426476907)
            ·
              refine ⟨5252159061949251639715361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501439374632834426476907 5252159061949251639715361)
              ·
                refine ⟨3939119296461938729786521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5252159061949251639715361 3939119296461938729786521)
                ·
                  refine ⟨2954339472346454047339891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3939119296461938729786521 2954339472346454047339891)
                  ·
                    refine ⟨4431509208519681071009837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2954339472346454047339891 4431509208519681071009837)
                    ·
                      refine ⟨1661815953194880401628689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4431509208519681071009837 1661815953194880401628689)
                      ·
                        rfl

theorem cell23_3236375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_3236375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236375 prefixEnd_3236375 := by exact prefixLift 3236375
  have htrace : WordTrace (prefixWord ++ tailWord_3236375) baseStart_3236375 baseEnd_3236375 := by
    simpa [prefixWord, tailWord_3236375, baseEnd_3236375] using wordTrace_append hprefix tailTrace_3236375
  have hstable : (prefixWord ++ tailWord_3236375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236375).length < 2 ^ (prefixWord ++ tailWord_3236375).sum := by decide
  have hdescent : baseEnd_3236375 < baseStart_3236375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236381 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_3236381 : Nat := 118140960795 + 3236381 * 2 ^ 59
def prefixEnd_3236381 : Nat := 4983230072969 + 3 ^ 40 * 3236381 * 2
def baseEnd_3236381 : Nat := 1661819034078807378153661

theorem tailTrace_3236381 : CollatzResearch.WordTrace tailWord_3236381 prefixEnd_3236381 1661819034078807378153661 := by
  unfold tailWord_3236381
  simp only [CollatzResearch.WordTrace]
  refine ⟨118040512488151841714836997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78693674992101227809891331 118040512488151841714836997)
  ·
    refine ⟨22132596091528470321531937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118040512488151841714836997 22132596091528470321531937)
    ·
      refine ⟨16599447068646352741148953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22132596091528470321531937 16599447068646352741148953)
      ·
        refine ⟨12449585301484764555861715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16599447068646352741148953 12449585301484764555861715)
        ·
          refine ⟨18674377952227146833792573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12449585301484764555861715 18674377952227146833792573)
          ·
            refine ⟨7002891732085180062672215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18674377952227146833792573 7002891732085180062672215)
            ·
              refine ⟨10504337598127770094008323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7002891732085180062672215 10504337598127770094008323)
              ·
                refine ⟨15756506397191655141012485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10504337598127770094008323 15756506397191655141012485)
                ·
                  refine ⟨2954344949473435338939841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15756506397191655141012485 2954344949473435338939841)
                  ·
                    refine ⟨2215758712105076504204881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2954344949473435338939841 2215758712105076504204881)
                    ·
                      refine ⟨1661819034078807378153661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2215758712105076504204881 1661819034078807378153661)
                      ·
                        rfl

theorem cell23_3236381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_3236381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236381 prefixEnd_3236381 := by exact prefixLift 3236381
  have htrace : WordTrace (prefixWord ++ tailWord_3236381) baseStart_3236381 baseEnd_3236381 := by
    simpa [prefixWord, tailWord_3236381, baseEnd_3236381] using wordTrace_append hprefix tailTrace_3236381
  have hstable : (prefixWord ++ tailWord_3236381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236381).length < 2 ^ (prefixWord ++ tailWord_3236381).sum := by decide
  have hdescent : baseEnd_3236381 < baseStart_3236381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236387 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 7]
def baseStart_3236387 : Nat := 118140960795 + 3236387 * 2 ^ 59
def prefixEnd_3236387 : Nat := 4983230072969 + 3 ^ 40 * 3236387 * 2
def baseEnd_3236387 : Nat := 184646901662526039408737

theorem tailTrace_3236387 : CollatzResearch.WordTrace tailWord_3236387 prefixEnd_3236387 184646901662526039408737 := by
  unfold tailWord_3236387
  simp only [CollatzResearch.WordTrace]
  refine ⟨118040731326130104739555415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78693820884086736493036943 118040731326130104739555415)
  ·
    refine ⟨177061096989195157109333123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118040731326130104739555415 177061096989195157109333123)
    ·
      refine ⟨265591645483792735663999685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177061096989195157109333123 265591645483792735663999685)
      ·
        refine ⟨49798433528211137936999941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265591645483792735663999685 49798433528211137936999941)
        ·
          refine ⟨9337206286539588363187489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49798433528211137936999941 9337206286539588363187489)
          ·
            refine ⟨7002904714904691272390617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9337206286539588363187489 7002904714904691272390617)
            ·
              refine ⟨5252178536178518454292963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7002904714904691272390617 5252178536178518454292963)
              ·
                refine ⟨7878267804267777681439445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5252178536178518454292963 7878267804267777681439445)
                ·
                  refine ⟨184646901662526039408737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7878267804267777681439445 184646901662526039408737)
                  ·
                    rfl

theorem cell23_3236387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 7].length) (baseStart_3236387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236387 prefixEnd_3236387 := by exact prefixLift 3236387
  have htrace : WordTrace (prefixWord ++ tailWord_3236387) baseStart_3236387 baseEnd_3236387 := by
    simpa [prefixWord, tailWord_3236387, baseEnd_3236387] using wordTrace_append hprefix tailTrace_3236387
  have hstable : (prefixWord ++ tailWord_3236387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236387).length < 2 ^ (prefixWord ++ tailWord_3236387).sum := by decide
  have hdescent : baseEnd_3236387 < baseStart_3236387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236398 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_3236398 : Nat := 118140960795 + 3236398 * 2 ^ 59
def prefixEnd_3236398 : Nat := 4983230072969 + 3 ^ 40 * 3236398 * 2
def baseEnd_3236398 : Nat := 1661827763249933811641083

theorem tailTrace_3236398 : CollatzResearch.WordTrace tailWord_3236398 prefixEnd_3236398 1661827763249933811641083 := by
  unfold tailWord_3236398
  simp only [CollatzResearch.WordTrace]
  refine ⟨14755141566136281702275731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78694088352726835745470565 14755141566136281702275731)
  ·
    refine ⟨22132712349204422553413597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14755141566136281702275731 22132712349204422553413597)
    ·
      refine ⟨8299767130951658457530099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22132712349204422553413597 8299767130951658457530099)
      ·
        refine ⟨12449650696427487686295149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8299767130951658457530099 12449650696427487686295149)
        ·
          refine ⟨4668619011160307882360681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12449650696427487686295149 4668619011160307882360681)
          ·
            refine ⟨3501464258370230911770511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4668619011160307882360681 3501464258370230911770511)
            ·
              refine ⟨5252196387555346367655767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501464258370230911770511 5252196387555346367655767)
              ·
                refine ⟨7878294581333019551483651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5252196387555346367655767 7878294581333019551483651)
                ·
                  refine ⟨11817441871999529327225477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7878294581333019551483651 11817441871999529327225477)
                  ·
                    refine ⟨2215770350999911748854777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11817441871999529327225477 2215770350999911748854777)
                    ·
                      refine ⟨1661827763249933811641083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2215770350999911748854777 1661827763249933811641083)
                      ·
                        rfl

theorem cell23_3236398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_3236398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236398 prefixEnd_3236398 := by exact prefixLift 3236398
  have htrace : WordTrace (prefixWord ++ tailWord_3236398) baseStart_3236398 baseEnd_3236398 := by
    simpa [prefixWord, tailWord_3236398, baseEnd_3236398] using wordTrace_append hprefix tailTrace_3236398
  have hstable : (prefixWord ++ tailWord_3236398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236398).length < 2 ^ (prefixWord ++ tailWord_3236398).sum := by decide
  have hdescent : baseEnd_3236398 < baseStart_3236398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236400 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 1, 7]
def baseStart_3236400 : Nat := 118140960795 + 3236400 * 2 ^ 59
def prefixEnd_3236400 : Nat := 4983230072969 + 3 ^ 40 * 3236400 * 2
def baseEnd_3236400 : Nat := 553942930070414267938691

theorem tailTrace_3236400 : CollatzResearch.WordTrace tailWord_3236400 prefixEnd_3236400 553942930070414267938691 := by
  unfold tailWord_3236400
  simp only [CollatzResearch.WordTrace]
  refine ⟨59020602737541503979889327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78694136983388671973185769 59020602737541503979889327)
  ·
    refine ⟨88530904106312255969833991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59020602737541503979889327 88530904106312255969833991)
    ·
      refine ⟨132796356159468383954750987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88530904106312255969833991 132796356159468383954750987)
      ·
        refine ⟨199194534239202575932126481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132796356159468383954750987 199194534239202575932126481)
        ·
          refine ⟨149395900679401931949094861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199194534239202575932126481 149395900679401931949094861)
          ·
            refine ⟨56023462754775724480910573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149395900679401931949094861 56023462754775724480910573)
            ·
              refine ⟨21008798533040896680341465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56023462754775724480910573 21008798533040896680341465)
              ·
                refine ⟨15756598899780672510256099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21008798533040896680341465 15756598899780672510256099)
                ·
                  refine ⟨23634898349671008765384149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15756598899780672510256099 23634898349671008765384149)
                  ·
                    refine ⟨553942930070414267938691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23634898349671008765384149 553942930070414267938691)
                    ·
                      rfl

theorem cell23_3236400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 7].length) (baseStart_3236400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236400 prefixEnd_3236400 := by exact prefixLift 3236400
  have htrace : WordTrace (prefixWord ++ tailWord_3236400) baseStart_3236400 baseEnd_3236400 := by
    simpa [prefixWord, tailWord_3236400, baseEnd_3236400] using wordTrace_append hprefix tailTrace_3236400
  have hstable : (prefixWord ++ tailWord_3236400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236400).length < 2 ^ (prefixWord ++ tailWord_3236400).sum := by decide
  have hdescent : baseEnd_3236400 < baseStart_3236400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236417 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 1, 7]
def baseStart_3236417 : Nat := 118140960795 + 3236417 * 2 ^ 59
def prefixEnd_3236417 : Nat := 4983230072969 + 3 ^ 40 * 3236417 * 2
def baseEnd_3236417 : Nat := 553945839794123079101165

theorem tailTrace_3236417 : CollatzResearch.WordTrace tailWord_3236417 prefixEnd_3236417 553945839794123079101165 := by
  unfold tailWord_3236417
  simp only [CollatzResearch.WordTrace]
  refine ⟨118041825516021419863147505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78694550344014279908765003 118041825516021419863147505)
  ·
    refine ⟨88531369137016064897360629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118041825516021419863147505 88531369137016064897360629)
    ·
      refine ⟨8299815856595256084127559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88531369137016064897360629 8299815856595256084127559)
      ·
        refine ⟨12449723784892884126191339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8299815856595256084127559 12449723784892884126191339)
        ·
          refine ⟨18674585677339326189287009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12449723784892884126191339 18674585677339326189287009)
          ·
            refine ⟨14005939258004494641965257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18674585677339326189287009 14005939258004494641965257)
            ·
              refine ⟨10504454443503370981473943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14005939258004494641965257 10504454443503370981473943)
              ·
                refine ⟨15756681665255056472210915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10504454443503370981473943 15756681665255056472210915)
                ·
                  refine ⟨23635022497882584708316373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15756681665255056472210915 23635022497882584708316373)
                  ·
                    refine ⟨553945839794123079101165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23635022497882584708316373 553945839794123079101165)
                    ·
                      rfl

theorem cell23_3236417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_3236417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236417 prefixEnd_3236417 := by exact prefixLift 3236417
  have htrace : WordTrace (prefixWord ++ tailWord_3236417) baseStart_3236417 baseEnd_3236417 := by
    simpa [prefixWord, tailWord_3236417, baseEnd_3236417] using wordTrace_append hprefix tailTrace_3236417
  have hstable : (prefixWord ++ tailWord_3236417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236417).length < 2 ^ (prefixWord ++ tailWord_3236417).sum := by decide
  have hdescent : baseEnd_3236417 < baseStart_3236417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236437 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_3236437 : Nat := 118140960795 + 3236437 * 2 ^ 59
def prefixEnd_3236437 : Nat := 4983230072969 + 3 ^ 40 * 3236437 * 2
def baseEnd_3236437 : Nat := 1661847788995459159053403

theorem tailTrace_3236437 : CollatzResearch.WordTrace tailWord_3236437 prefixEnd_3236437 1661847788995459159053403 := by
  unfold tailWord_3236437
  simp only [CollatzResearch.WordTrace]
  refine ⟨118042554975948963278875565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78695036650632642185917043 118042554975948963278875565)
  ·
    refine ⟨44265958115980861229578337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118042554975948963278875565 44265958115980861229578337)
    ·
      refine ⟨33199468586985645922183753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44265958115980861229578337 33199468586985645922183753)
      ·
        refine ⟨24899601440239234441637815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33199468586985645922183753 24899601440239234441637815)
        ·
          refine ⟨37349402160358851662456723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24899601440239234441637815 37349402160358851662456723)
          ·
            refine ⟨56024103240538277493685085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37349402160358851662456723 56024103240538277493685085)
            ·
              refine ⟨21009038715201854060131907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56024103240538277493685085 21009038715201854060131907)
              ·
                refine ⟨31513558072802781090197861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21009038715201854060131907 31513558072802781090197861)
                ·
                  refine ⟨5908792138650521454412099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31513558072802781090197861 5908792138650521454412099)
                  ·
                    refine ⟨8863188207975782181618149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5908792138650521454412099 8863188207975782181618149)
                    ·
                      refine ⟨1661847788995459159053403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8863188207975782181618149 1661847788995459159053403)
                      ·
                        rfl

theorem cell23_3236437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_3236437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236437 prefixEnd_3236437 := by exact prefixLift 3236437
  have htrace : WordTrace (prefixWord ++ tailWord_3236437) baseStart_3236437 baseEnd_3236437 := by
    simpa [prefixWord, tailWord_3236437, baseEnd_3236437] using wordTrace_append hprefix tailTrace_3236437
  have hstable : (prefixWord ++ tailWord_3236437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236437).length < 2 ^ (prefixWord ++ tailWord_3236437).sum := by decide
  have hdescent : baseEnd_3236437 < baseStart_3236437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236444 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_3236444 : Nat := 118140960795 + 3236444 * 2 ^ 59
def prefixEnd_3236444 : Nat := 4983230072969 + 3 ^ 40 * 3236444 * 2
def baseEnd_3236444 : Nat := 1661851383360040631665871

theorem tailTrace_3236444 : CollatzResearch.WordTrace tailWord_3236444 prefixEnd_3236444 1661851383360040631665871 := by
  unfold tailWord_3236444
  simp only [CollatzResearch.WordTrace]
  refine ⟨59021405143461801737190193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78695206857949068982920257 59021405143461801737190193)
  ·
    refine ⟨44266053857596351302892645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59021405143461801737190193 44266053857596351302892645)
    ·
      refine ⟨8299885098299315869292371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44266053857596351302892645 8299885098299315869292371)
      ·
        refine ⟨12449827647448973803938557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8299885098299315869292371 12449827647448973803938557)
        ·
          refine ⟨4668685367793365176476959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12449827647448973803938557 4668685367793365176476959)
          ·
            refine ⟨7003028051690047764715439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4668685367793365176476959 7003028051690047764715439)
            ·
              refine ⟨10504542077535071647073159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7003028051690047764715439 10504542077535071647073159)
              ·
                refine ⟨15756813116302607470609739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10504542077535071647073159 15756813116302607470609739)
                ·
                  refine ⟨23635219674453911205914609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15756813116302607470609739 23635219674453911205914609)
                  ·
                    refine ⟨17726414755840433404435957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23635219674453911205914609 17726414755840433404435957)
                    ·
                      refine ⟨1661851383360040631665871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17726414755840433404435957 1661851383360040631665871)
                      ·
                        rfl

theorem cell23_3236444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_3236444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236444 prefixEnd_3236444 := by exact prefixLift 3236444
  have htrace : WordTrace (prefixWord ++ tailWord_3236444) baseStart_3236444 baseEnd_3236444 := by
    simpa [prefixWord, tailWord_3236444, baseEnd_3236444] using wordTrace_append hprefix tailTrace_3236444
  have hstable : (prefixWord ++ tailWord_3236444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236444).length < 2 ^ (prefixWord ++ tailWord_3236444).sum := by decide
  have hdescent : baseEnd_3236444 < baseStart_3236444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236457 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 6, 2, 3]
def baseStart_3236457 : Nat := 118140960795 + 3236457 * 2 ^ 59
def prefixEnd_3236457 : Nat := 4983230072969 + 3 ^ 40 * 3236457 * 2
def baseEnd_3236457 : Nat := 1661858058608549080803311

theorem tailTrace_3236457 : CollatzResearch.WordTrace tailWord_3236457 prefixEnd_3236457 1661858058608549080803311 := by
  unfold tailWord_3236457
  simp only [CollatzResearch.WordTrace]
  refine ⟨118043284435876506694603625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78695522957251004463069083 118043284435876506694603625)
  ·
    refine ⟨88532463326907380020952719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118043284435876506694603625 88532463326907380020952719)
    ·
      refine ⟨132798694990361070031429079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88532463326907380020952719 132798694990361070031429079)
      ·
        refine ⟨199198042485541605047143619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132798694990361070031429079 199198042485541605047143619)
        ·
          refine ⟨298797063728312407570715429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199198042485541605047143619 298797063728312407570715429)
          ·
            refine ⟨56024449449058576419509143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 298797063728312407570715429 56024449449058576419509143)
            ·
              refine ⟨84036674173587864629263715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56024449449058576419509143 84036674173587864629263715)
              ·
                refine ⟨126055011260381796943895573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84036674173587864629263715 126055011260381796943895573)
                ·
                  refine ⟨5908828652830396731745105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126055011260381796943895573 5908828652830396731745105)
                  ·
                    refine ⟨4431621489622797548808829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5908828652830396731745105 4431621489622797548808829)
                    ·
                      refine ⟨1661858058608549080803311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4431621489622797548808829 1661858058608549080803311)
                      ·
                        rfl

theorem cell23_3236457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 2, 3].length) (baseStart_3236457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236457 prefixEnd_3236457 := by exact prefixLift 3236457
  have htrace : WordTrace (prefixWord ++ tailWord_3236457) baseStart_3236457 baseEnd_3236457 := by
    simpa [prefixWord, tailWord_3236457, baseEnd_3236457] using wordTrace_append hprefix tailTrace_3236457
  have hstable : (prefixWord ++ tailWord_3236457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236457).length < 2 ^ (prefixWord ++ tailWord_3236457).sum := by decide
  have hdescent : baseEnd_3236457 < baseStart_3236457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236481 : List Nat := [1, 2, 4, 2, 1, 1, 2, 5, 1, 4]
def baseStart_3236481 : Nat := 118140960795 + 3236481 * 2 ^ 59
def prefixEnd_3236481 : Nat := 4983230072969 + 3 ^ 40 * 3236481 * 2
def baseEnd_3236481 : Nat := 553956794048085662301067

theorem tailTrace_3236481 : CollatzResearch.WordTrace tailWord_3236481 prefixEnd_3236481 553956794048085662301067 := by
  unfold tailWord_3236481
  simp only [CollatzResearch.WordTrace]
  refine ⟨118044159787789558793477297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78696106525193039195651531 118044159787789558793477297)
  ·
    refine ⟨88533119840842169095107973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118044159787789558793477297 88533119840842169095107973)
    ·
      refine ⟨16599959970157906705332745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88533119840842169095107973 16599959970157906705332745)
      ·
        refine ⟨12449969977618430028999559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16599959970157906705332745 12449969977618430028999559)
        ·
          refine ⟨18674954966427645043499339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12449969977618430028999559 18674954966427645043499339)
          ·
            refine ⟨28012432449641467565249009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18674954966427645043499339 28012432449641467565249009)
            ·
              refine ⟨21009324337231100673936757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28012432449641467565249009 21009324337231100673936757)
              ·
                refine ⟨1969624156615415688181571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21009324337231100673936757 1969624156615415688181571)
                ·
                  refine ⟨2954436234923123532272357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969624156615415688181571 2954436234923123532272357)
                  ·
                    refine ⟨553956794048085662301067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2954436234923123532272357 553956794048085662301067)
                    ·
                      rfl

theorem cell23_3236481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_3236481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236481 prefixEnd_3236481 := by exact prefixLift 3236481
  have htrace : WordTrace (prefixWord ++ tailWord_3236481) baseStart_3236481 baseEnd_3236481 := by
    simpa [prefixWord, tailWord_3236481, baseEnd_3236481] using wordTrace_append hprefix tailTrace_3236481
  have hstable : (prefixWord ++ tailWord_3236481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236481).length < 2 ^ (prefixWord ++ tailWord_3236481).sum := by decide
  have hdescent : baseEnd_3236481 < baseStart_3236481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236494 : List Nat := [4, 1, 1, 3, 1, 1, 4, 2, 6]
def baseStart_3236494 : Nat := 118140960795 + 3236494 * 2 ^ 59
def prefixEnd_3236494 : Nat := 4983230072969 + 3 ^ 40 * 3236494 * 2
def baseEnd_3236494 : Nat := 184653006376973937337849

theorem tailTrace_3236494 : CollatzResearch.WordTrace tailWord_3236494 prefixEnd_3236494 184653006376973937337849 := by
  unfold tailWord_3236494
  simp only [CollatzResearch.WordTrace]
  refine ⟨14755579242092807751712567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78696422624494974675800357 14755579242092807751712567)
  ·
    refine ⟨22133368863139211627568851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14755579242092807751712567 22133368863139211627568851)
    ·
      refine ⟨33200053294708817441353277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22133368863139211627568851 33200053294708817441353277)
      ·
        refine ⟨12450019985515806540507479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33200053294708817441353277 12450019985515806540507479)
        ·
          refine ⟨18675029978273709810761219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12450019985515806540507479 18675029978273709810761219)
          ·
            refine ⟨28012544967410564716141829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18675029978273709810761219 28012544967410564716141829)
            ·
              refine ⟨5252352181389480884276593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28012544967410564716141829 5252352181389480884276593)
              ·
                refine ⟨3939264136042110663207445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5252352181389480884276593 3939264136042110663207445)
                ·
                  refine ⟨184653006376973937337849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3939264136042110663207445 184653006376973937337849)
                  ·
                    rfl

theorem cell23_3236494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_3236494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236494 prefixEnd_3236494 := by exact prefixLift 3236494
  have htrace : WordTrace (prefixWord ++ tailWord_3236494) baseStart_3236494 baseEnd_3236494 := by
    simpa [prefixWord, tailWord_3236494, baseEnd_3236494] using wordTrace_append hprefix tailTrace_3236494
  have hstable : (prefixWord ++ tailWord_3236494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236494).length < 2 ^ (prefixWord ++ tailWord_3236494).sum := by decide
  have hdescent : baseEnd_3236494 < baseStart_3236494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236498 : List Nat := [3, 2, 3, 1, 2, 2, 1, 4, 1, 4]
def baseStart_3236498 : Nat := 118140960795 + 3236498 * 2 ^ 59
def prefixEnd_3236498 : Nat := 4983230072969 + 3 ^ 40 * 3236498 * 2
def baseEnd_3236498 : Nat := 553959703771794473463541

theorem tailTrace_3236498 : CollatzResearch.WordTrace tailWord_3236498 prefixEnd_3236498 553959703771794473463541 := by
  unfold tailWord_3236498
  simp only [CollatzResearch.WordTrace]
  refine ⟨29511194957181992674211537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78696519885818647131230765 29511194957181992674211537)
  ·
    refine ⟨22133396217886494505658653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29511194957181992674211537 22133396217886494505658653)
    ·
      refine ⟨8300023581707435439621995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22133396217886494505658653 8300023581707435439621995)
      ·
        refine ⟨12450035372561153159432993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8300023581707435439621995 12450035372561153159432993)
        ·
          refine ⟨9337526529420864869574745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12450035372561153159432993 9337526529420864869574745)
          ·
            refine ⟨7003144897065648652181059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9337526529420864869574745 7003144897065648652181059)
            ·
              refine ⟨10504717345598472978271589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7003144897065648652181059 10504717345598472978271589)
              ·
                refine ⟨1969634502299713683425923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10504717345598472978271589 1969634502299713683425923)
                ·
                  refine ⟨2954451753449570525138885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969634502299713683425923 2954451753449570525138885)
                  ·
                    refine ⟨553959703771794473463541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2954451753449570525138885 553959703771794473463541)
                    ·
                      rfl

theorem cell23_3236498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_3236498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236498 prefixEnd_3236498 := by exact prefixLift 3236498
  have htrace : WordTrace (prefixWord ++ tailWord_3236498) baseStart_3236498 baseEnd_3236498 := by
    simpa [prefixWord, tailWord_3236498, baseEnd_3236498] using wordTrace_append hprefix tailTrace_3236498
  have hstable : (prefixWord ++ tailWord_3236498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236498).length < 2 ^ (prefixWord ++ tailWord_3236498).sum := by decide
  have hdescent : baseEnd_3236498 < baseStart_3236498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236531 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 2, 3, 2]
def baseStart_3236531 : Nat := 118140960795 + 3236531 * 2 ^ 59
def prefixEnd_3236531 : Nat := 4983230072969 + 3 ^ 40 * 3236531 * 2
def baseEnd_3236531 : Nat := 1661896056176981791277971

theorem tailTrace_3236531 : CollatzResearch.WordTrace tailWord_3236531 prefixEnd_3236531 1661896056176981791277971 := by
  unfold tailWord_3236531
  simp only [CollatzResearch.WordTrace]
  refine ⟨118045983437608417332797447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78697322291738944888531631 118045983437608417332797447)
  ·
    refine ⟨177068975156412625999196171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118045983437608417332797447 177068975156412625999196171)
    ·
      refine ⟨265603462734618938998794257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177068975156412625999196171 265603462734618938998794257)
      ·
        refine ⟨199202597050964204249095693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265603462734618938998794257 199202597050964204249095693)
        ·
          refine ⟨74700973894111576593410885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199202597050964204249095693 74700973894111576593410885)
          ·
            refine ⟨14006432605145920611264541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74700973894111576593410885 14006432605145920611264541)
            ·
              refine ⟨5252412226929720229224203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14006432605145920611264541 5252412226929720229224203)
              ·
                refine ⟨7878618340394580343836305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5252412226929720229224203 7878618340394580343836305)
                ·
                  refine ⟨5908963755295935257877229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7878618340394580343836305 5908963755295935257877229)
                  ·
                    refine ⟨2215861408235975721703961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5908963755295935257877229 2215861408235975721703961)
                    ·
                      refine ⟨1661896056176981791277971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2215861408235975721703961 1661896056176981791277971)
                      ·
                        rfl

theorem cell23_3236531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 3, 2].length) (baseStart_3236531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236531 prefixEnd_3236531 := by exact prefixLift 3236531
  have htrace : WordTrace (prefixWord ++ tailWord_3236531) baseStart_3236531 baseEnd_3236531 := by
    simpa [prefixWord, tailWord_3236531, baseEnd_3236531] using wordTrace_append hprefix tailTrace_3236531
  have hstable : (prefixWord ++ tailWord_3236531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236531).length < 2 ^ (prefixWord ++ tailWord_3236531).sum := by decide
  have hdescent : baseEnd_3236531 < baseStart_3236531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236538 : List Nat := [3, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3]
def baseStart_3236538 : Nat := 118140960795 + 3236538 * 2 ^ 59
def prefixEnd_3236538 : Nat := 4983230072969 + 3 ^ 40 * 3236538 * 2
def baseEnd_3236538 : Nat := 1661899650541563263890439

theorem tailTrace_3236538 : CollatzResearch.WordTrace tailWord_3236538 prefixEnd_3236538 1661899650541563263890439 := by
  unfold tailWord_3236538
  simp only [CollatzResearch.WordTrace]
  refine ⟨29511559687145764382075567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78697492499055371685534845 29511559687145764382075567)
  ·
    refine ⟨44267339530718646573113351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29511559687145764382075567 44267339530718646573113351)
    ·
      refine ⟨66401009296077969859670027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44267339530718646573113351 66401009296077969859670027)
      ·
        refine ⟨99601513944116954789505041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66401009296077969859670027 99601513944116954789505041)
        ·
          refine ⟨74701135458087716092128781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99601513944116954789505041 74701135458087716092128781)
          ·
            refine ⟨28012925796782893534548293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74701135458087716092128781 28012925796782893534548293)
            ·
              refine ⟨5252423586896792537727805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28012925796782893534548293 5252423586896792537727805)
              ·
                refine ⟨1969658845086297201647927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5252423586896792537727805 1969658845086297201647927)
                ·
                  refine ⟨2954488267629445802471891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969658845086297201647927 2954488267629445802471891)
                  ·
                    refine ⟨4431732401444168703707837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2954488267629445802471891 4431732401444168703707837)
                    ·
                      refine ⟨1661899650541563263890439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4431732401444168703707837 1661899650541563263890439)
                      ·
                        rfl

theorem cell23_3236538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 1, 1, 3].length) (baseStart_3236538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236538 prefixEnd_3236538 := by exact prefixLift 3236538
  have htrace : WordTrace (prefixWord ++ tailWord_3236538) baseStart_3236538 baseEnd_3236538 := by
    simpa [prefixWord, tailWord_3236538, baseEnd_3236538] using wordTrace_append hprefix tailTrace_3236538
  have hstable : (prefixWord ++ tailWord_3236538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236538).length < 2 ^ (prefixWord ++ tailWord_3236538).sum := by decide
  have hdescent : baseEnd_3236538 < baseStart_3236538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236541 : List Nat := [1, 4, 1, 2, 1, 3, 4, 1, 1, 5]
def baseStart_3236541 : Nat := 118140960795 + 3236541 * 2 ^ 59
def prefixEnd_3236541 : Nat := 4983230072969 + 3 ^ 40 * 3236541 * 2
def baseEnd_3236541 : Nat := 553967063661175584050975

theorem tailTrace_3236541 : CollatzResearch.WordTrace tailWord_3236541 prefixEnd_3236541 553967063661175584050975 := by
  unfold tailWord_3236541
  simp only [CollatzResearch.WordTrace]
  refine ⟨118046348167572189040661477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78697565445048126027107651 118046348167572189040661477)
  ·
    refine ⟨22133690281419785445124027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118046348167572189040661477 22133690281419785445124027)
    ·
      refine ⟨33200535422129678167686041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22133690281419785445124027 33200535422129678167686041)
      ·
        refine ⟨24900401566597258625764531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33200535422129678167686041 24900401566597258625764531)
        ·
          refine ⟨37350602349895887938646797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24900401566597258625764531 37350602349895887938646797)
          ·
            refine ⟨14006475881210957976992549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37350602349895887938646797 14006475881210957976992549)
            ·
              refine ⟨2626214227727054620686103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14006475881210957976992549 2626214227727054620686103)
              ·
                refine ⟨3939321341590581931029155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626214227727054620686103 3939321341590581931029155)
                ·
                  refine ⟨5908982012385872896543733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3939321341590581931029155 5908982012385872896543733)
                  ·
                    refine ⟨553967063661175584050975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5908982012385872896543733 553967063661175584050975)
                    ·
                      rfl

theorem cell23_3236541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_3236541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236541 prefixEnd_3236541 := by exact prefixLift 3236541
  have htrace : WordTrace (prefixWord ++ tailWord_3236541) baseStart_3236541 baseEnd_3236541 := by
    simpa [prefixWord, tailWord_3236541, baseEnd_3236541] using wordTrace_append hprefix tailTrace_3236541
  have hstable : (prefixWord ++ tailWord_3236541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236541).length < 2 ^ (prefixWord ++ tailWord_3236541).sum := by decide
  have hdescent : baseEnd_3236541 < baseStart_3236541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236545 : List Nat := [1, 2, 6, 2, 2, 1, 1, 2, 6]
def baseStart_3236545 : Nat := 118140960795 + 3236545 * 2 ^ 59
def prefixEnd_3236545 : Nat := 4983230072969 + 3 ^ 40 * 3236545 * 2
def baseEnd_3236545 : Nat := 184655916100682748500323

theorem tailTrace_3236545 : CollatzResearch.WordTrace tailWord_3236545 prefixEnd_3236545 184655916100682748500323 := by
  unfold tailWord_3236545
  simp only [CollatzResearch.WordTrace]
  refine ⟨118046494059557697723807089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78697662706371798482538059 118046494059557697723807089)
  ·
    refine ⟨88534870544668273292855317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118046494059557697723807089 88534870544668273292855317)
    ·
      refine ⟨4150072056781325310602593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88534870544668273292855317 4150072056781325310602593)
      ·
        refine ⟨3112554042585993982951945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4150072056781325310602593 3112554042585993982951945)
        ·
          refine ⟨2334415531939495487213959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3112554042585993982951945 2334415531939495487213959)
          ·
            refine ⟨3501623297909243230820939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334415531939495487213959 3501623297909243230820939)
            ·
              refine ⟨5252434946863864846231409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501623297909243230820939 5252434946863864846231409)
              ·
                refine ⟨3939326210147898634673557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5252434946863864846231409 3939326210147898634673557)
                ·
                  refine ⟨184655916100682748500323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3939326210147898634673557 184655916100682748500323)
                  ·
                    rfl

theorem cell23_3236545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 6].length) (baseStart_3236545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236545 prefixEnd_3236545 := by exact prefixLift 3236545
  have htrace : WordTrace (prefixWord ++ tailWord_3236545) baseStart_3236545 baseEnd_3236545 := by
    simpa [prefixWord, tailWord_3236545, baseEnd_3236545] using wordTrace_append hprefix tailTrace_3236545
  have hstable : (prefixWord ++ tailWord_3236545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236545).length < 2 ^ (prefixWord ++ tailWord_3236545).sum := by decide
  have hdescent : baseEnd_3236545 < baseStart_3236545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236581 : List Nat := [1, 3, 1, 4, 1, 2, 1, 4, 1, 2, 3]
def baseStart_3236581 : Nat := 118140960795 + 3236581 * 2 ^ 59
def prefixEnd_3236581 : Nat := 4983230072969 + 3 ^ 40 * 3236581 * 2
def baseEnd_3236581 : Nat := 1661921730209706595652741

theorem tailTrace_3236581 : CollatzResearch.WordTrace tailWord_3236581 prefixEnd_3236581 1661921730209706595652741 := by
  unfold tailWord_3236581
  simp only [CollatzResearch.WordTrace]
  refine ⟨118047807087427275872117597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78698538058284850581411731 118047807087427275872117597)
  ·
    refine ⟨44267927657785228452044099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118047807087427275872117597 44267927657785228452044099)
    ·
      refine ⟨66401891486677842678066149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44267927657785228452044099 66401891486677842678066149)
      ·
        refine ⟨12450354653752095502137403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66401891486677842678066149 12450354653752095502137403)
        ·
          refine ⟨18675531980628143253206105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12450354653752095502137403 18675531980628143253206105)
          ·
            refine ⟨14006648985471107439904579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18675531980628143253206105 14006648985471107439904579)
            ·
              refine ⟨21009973478206661159856869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14006648985471107439904579 21009973478206661159856869)
              ·
                refine ⟨3939370027163748967473163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21009973478206661159856869 3939370027163748967473163)
                ·
                  refine ⟨5909055040745623451209745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3939370027163748967473163 5909055040745623451209745)
                  ·
                    refine ⟨4431791280559217588407309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5909055040745623451209745 4431791280559217588407309)
                    ·
                      refine ⟨1661921730209706595652741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4431791280559217588407309 1661921730209706595652741)
                      ·
                        rfl

theorem cell23_3236581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_3236581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236581 prefixEnd_3236581 := by exact prefixLift 3236581
  have htrace : WordTrace (prefixWord ++ tailWord_3236581) baseStart_3236581 baseEnd_3236581 := by
    simpa [prefixWord, tailWord_3236581, baseEnd_3236581] using wordTrace_append hprefix tailTrace_3236581
  have hstable : (prefixWord ++ tailWord_3236581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236581).length < 2 ^ (prefixWord ++ tailWord_3236581).sum := by decide
  have hdescent : baseEnd_3236581 < baseStart_3236581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236584 : List Nat := [2, 1, 4, 1, 4, 1, 1, 9]
def baseStart_3236584 : Nat := 118140960795 + 3236584 * 2 ^ 59
def prefixEnd_3236584 : Nat := 4983230072969 + 3 ^ 40 * 3236584 * 2
def baseEnd_3236584 : Nat := 61552713727839632737601

theorem tailTrace_3236584 : CollatzResearch.WordTrace tailWord_3236584 prefixEnd_3236584 61552713727839632737601 := by
  unfold tailWord_3236584
  simp only [CollatzResearch.WordTrace]
  refine ⟨59023958253208203692238403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78698611004277604922984537 59023958253208203692238403)
  ·
    refine ⟨88535937379812305538357605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59023958253208203692238403 88535937379812305538357605)
    ·
      refine ⟨16600488258714807288442051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88535937379812305538357605 16600488258714807288442051)
      ·
        refine ⟨24900732388072210932663077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16600488258714807288442051 24900732388072210932663077)
        ·
          refine ⟨4668887322763539549874327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24900732388072210932663077 4668887322763539549874327)
          ·
            refine ⟨7003330984145309324811491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4668887322763539549874327 7003330984145309324811491)
            ·
              refine ⟨10504996476217963987217237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7003330984145309324811491 10504996476217963987217237)
              ·
                refine ⟨61552713727839632737601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10504996476217963987217237 61552713727839632737601)
                ·
                  rfl

theorem cell23_3236584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 9].length) (baseStart_3236584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236584 prefixEnd_3236584 := by exact prefixLift 3236584
  have htrace : WordTrace (prefixWord ++ tailWord_3236584) baseStart_3236584 baseEnd_3236584 := by
    simpa [prefixWord, tailWord_3236584, baseEnd_3236584] using wordTrace_append hprefix tailTrace_3236584
  have hstable : (prefixWord ++ tailWord_3236584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236584).length < 2 ^ (prefixWord ++ tailWord_3236584).sum := by decide
  have hdescent : baseEnd_3236584 < baseStart_3236584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236607 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 5]
def baseStart_3236607 : Nat := 118140960795 + 3236607 * 2 ^ 59
def prefixEnd_3236607 : Nat := 4983230072969 + 3 ^ 40 * 3236607 * 2
def baseEnd_3236607 : Nat := 1661935080706723493927621

theorem tailTrace_3236607 : CollatzResearch.WordTrace tailWord_3236607 prefixEnd_3236607 1661935080706723493927621 := by
  unfold tailWord_3236607
  simp only [CollatzResearch.WordTrace]
  refine ⟨118048755385333082312564075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78699170256888721541709383 118048755385333082312564075)
  ·
    refine ⟨177073133077999623468846113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118048755385333082312564075 177073133077999623468846113)
    ·
      refine ⟨132804849808499717601634585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177073133077999623468846113 132804849808499717601634585)
      ·
        refine ⟨99603637356374788201225939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132804849808499717601634585 99603637356374788201225939)
        ·
          refine ⟨149405456034562182301838909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99603637356374788201225939 149405456034562182301838909)
          ·
            refine ⟨56027046012960818363189591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149405456034562182301838909 56027046012960818363189591)
            ·
              refine ⟨84040569019441227544784387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56027046012960818363189591 84040569019441227544784387)
              ·
                refine ⟨126060853529161841317176581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84040569019441227544784387 126060853529161841317176581)
                ·
                  refine ⟨23636410036717845246970609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126060853529161841317176581 23636410036717845246970609)
                  ·
                    refine ⟨17727307527538383935227957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23636410036717845246970609 17727307527538383935227957)
                    ·
                      refine ⟨1661935080706723493927621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17727307527538383935227957 1661935080706723493927621)
                      ·
                        rfl

theorem cell23_3236607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_3236607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236607 prefixEnd_3236607 := by exact prefixLift 3236607
  have htrace : WordTrace (prefixWord ++ tailWord_3236607) baseStart_3236607 baseEnd_3236607 := by
    simpa [prefixWord, tailWord_3236607, baseEnd_3236607] using wordTrace_append hprefix tailTrace_3236607
  have hstable : (prefixWord ++ tailWord_3236607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236607).length < 2 ^ (prefixWord ++ tailWord_3236607).sum := by decide
  have hdescent : baseEnd_3236607 < baseStart_3236607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236611 : List Nat := [1, 1, 1, 3, 2, 2, 1, 6, 2, 1, 3]
def baseStart_3236611 : Nat := 118140960795 + 3236611 * 2 ^ 59
def prefixEnd_3236611 : Nat := 4983230072969 + 3 ^ 40 * 3236611 * 2
def baseEnd_3236611 : Nat := 1661937134629341478277603

theorem tailTrace_3236611 : CollatzResearch.WordTrace tailWord_3236611 prefixEnd_3236611 1661937134629341478277603 := by
  unfold tailWord_3236611
  simp only [CollatzResearch.WordTrace]
  refine ⟨118048901277318590995709687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78699267518212393997139791 118048901277318590995709687)
  ·
    refine ⟨177073351915977886493564531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118048901277318590995709687 177073351915977886493564531)
    ·
      refine ⟨265610027873966829740346797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177073351915977886493564531 265610027873966829740346797)
      ·
        refine ⟨99603760452737561152630049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265610027873966829740346797 99603760452737561152630049)
        ·
          refine ⟨74702820339553170864472537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99603760452737561152630049 74702820339553170864472537)
          ·
            refine ⟨56027115254664878148354403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74702820339553170864472537 56027115254664878148354403)
            ·
              refine ⟨84040672881997317222531605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56027115254664878148354403 84040672881997317222531605)
              ·
                refine ⟨3939406541343624244806169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84040672881997317222531605 3939406541343624244806169)
                ·
                  refine ⟨2954554906007718183604627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3939406541343624244806169 2954554906007718183604627)
                  ·
                    refine ⟨4431832359011577275406941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2954554906007718183604627 4431832359011577275406941)
                    ·
                      refine ⟨1661937134629341478277603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4431832359011577275406941 1661937134629341478277603)
                      ·
                        rfl

theorem cell23_3236611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_3236611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236611 prefixEnd_3236611 := by exact prefixLift 3236611
  have htrace : WordTrace (prefixWord ++ tailWord_3236611) baseStart_3236611 baseEnd_3236611 := by
    simpa [prefixWord, tailWord_3236611, baseEnd_3236611] using wordTrace_append hprefix tailTrace_3236611
  have hstable : (prefixWord ++ tailWord_3236611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236611).length < 2 ^ (prefixWord ++ tailWord_3236611).sum := by decide
  have hdescent : baseEnd_3236611 < baseStart_3236611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236612 : List Nat := [2, 3, 2, 2, 1, 1, 5, 2, 1, 2, 2]
def baseStart_3236612 : Nat := 118140960795 + 3236612 * 2 ^ 59
def prefixEnd_3236612 : Nat := 4983230072969 + 3 ^ 40 * 3236612 * 2
def baseEnd_3236612 : Nat := 1661937648109995974365099

theorem tailTrace_3236612 : CollatzResearch.WordTrace tailWord_3236612 prefixEnd_3236612 1661937648109995974365099 := by
  unfold tailWord_3236612
  simp only [CollatzResearch.WordTrace]
  refine ⟨59024468875157484083248045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78699291833543312110997393 59024468875157484083248045)
  ·
    refine ⟨22134175828184056531218017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59024468875157484083248045 22134175828184056531218017)
    ·
      refine ⟨16600631871138042398413513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22134175828184056531218017 16600631871138042398413513)
      ·
        refine ⟨12450473903353531798810135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16600631871138042398413513 12450473903353531798810135)
        ·
          refine ⟨18675710855030297698215203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12450473903353531798810135 18675710855030297698215203)
          ·
            refine ⟨28013566282545446547322805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18675710855030297698215203 28013566282545446547322805)
            ·
              refine ⟨2626271838988635613811513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28013566282545446547322805 2626271838988635613811513)
              ·
                refine ⟨1969703879241476710358635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2626271838988635613811513 1969703879241476710358635)
                ·
                  refine ⟨2954555818862215065537953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969703879241476710358635 2954555818862215065537953)
                  ·
                    refine ⟨2215916864146661299153465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2954555818862215065537953 2215916864146661299153465)
                    ·
                      refine ⟨1661937648109995974365099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2215916864146661299153465 1661937648109995974365099)
                      ·
                        rfl

theorem cell23_3236612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_3236612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236612 prefixEnd_3236612 := by exact prefixLift 3236612
  have htrace : WordTrace (prefixWord ++ tailWord_3236612) baseStart_3236612 baseEnd_3236612 := by
    simpa [prefixWord, tailWord_3236612, baseEnd_3236612] using wordTrace_append hprefix tailTrace_3236612
  have hstable : (prefixWord ++ tailWord_3236612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236612).length < 2 ^ (prefixWord ++ tailWord_3236612).sum := by decide
  have hdescent : baseEnd_3236612 < baseStart_3236612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236627 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 1, 8]
def baseStart_3236627 : Nat := 118140960795 + 3236627 * 2 ^ 59
def prefixEnd_3236627 : Nat := 4983230072969 + 3 ^ 40 * 3236627 * 2
def baseEnd_3236627 : Nat := 553981783439937805225843

theorem tailTrace_3236627 : CollatzResearch.WordTrace tailWord_3236627 prefixEnd_3236627 553981783439937805225843 := by
  unfold tailWord_3236627
  simp only [CollatzResearch.WordTrace]
  refine ⟨118049484845260625728292135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78699656563507083818861423 118049484845260625728292135)
  ·
    refine ⟨177074227267890938592438203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118049484845260625728292135 177074227267890938592438203)
    ·
      refine ⟨265611340901836407888657305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177074227267890938592438203 265611340901836407888657305)
      ·
        refine ⟨199208505676377305916492979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265611340901836407888657305 199208505676377305916492979)
        ·
          refine ⟨298812758514565958874739469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199208505676377305916492979 298812758514565958874739469)
          ·
            refine ⟨112054784442962234578027301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 298812758514565958874739469 112054784442962234578027301)
            ·
              refine ⟨21010272083055418983380119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112054784442962234578027301 21010272083055418983380119)
              ·
                refine ⟨31515408124583128475070179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21010272083055418983380119 31515408124583128475070179)
                ·
                  refine ⟨47273112186874692712605269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31515408124583128475070179 47273112186874692712605269)
                  ·
                    refine ⟨553981783439937805225843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47273112186874692712605269 553981783439937805225843)
                    ·
                      rfl

theorem cell23_3236627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 8].length) (baseStart_3236627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236627 prefixEnd_3236627 := by exact prefixLift 3236627
  have htrace : WordTrace (prefixWord ++ tailWord_3236627) baseStart_3236627 baseEnd_3236627 := by
    simpa [prefixWord, tailWord_3236627, baseEnd_3236627] using wordTrace_append hprefix tailTrace_3236627
  have hstable : (prefixWord ++ tailWord_3236627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236627).length < 2 ^ (prefixWord ++ tailWord_3236627).sum := by decide
  have hdescent : baseEnd_3236627 < baseStart_3236627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236662 : List Nat := [5, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3236662 : Nat := 118140960795 + 3236662 * 2 ^ 59
def prefixEnd_3236662 : Nat := 4983230072969 + 3 ^ 40 * 3236662 * 2
def baseEnd_3236662 : Nat := 1661963322142720778739869

theorem tailTrace_3236662 : CollatzResearch.WordTrace tailWord_3236662 prefixEnd_3236662 1661963322142720778739869 := by
  unfold tailWord_3236662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7378172587508364169113515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78700507600089217803877493 7378172587508364169113515)
  ·
    refine ⟨11067258881262546253670273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7378172587508364169113515 11067258881262546253670273)
    ·
      refine ⟨8300444160946909690252705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11067258881262546253670273 8300444160946909690252705)
      ·
        refine ⟨6225333120710182267689529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8300444160946909690252705 6225333120710182267689529)
        ·
          refine ⟨4668999840532636700767147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6225333120710182267689529 4668999840532636700767147)
          ·
            refine ⟨7003499760798955051150721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4668999840532636700767147 7003499760798955051150721)
            ·
              refine ⟨5252624820599216288363041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7003499760798955051150721 5252624820599216288363041)
              ·
                refine ⟨3939468615449412216272281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5252624820599216288363041 3939468615449412216272281)
                ·
                  refine ⟨2954601461587059162204211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3939468615449412216272281 2954601461587059162204211)
                  ·
                    refine ⟨4431902192380588743306317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2954601461587059162204211 4431902192380588743306317)
                    ·
                      refine ⟨1661963322142720778739869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4431902192380588743306317 1661963322142720778739869)
                      ·
                        rfl

theorem cell23_3236662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3236662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236662 prefixEnd_3236662 := by exact prefixLift 3236662
  have htrace : WordTrace (prefixWord ++ tailWord_3236662) baseStart_3236662 baseEnd_3236662 := by
    simpa [prefixWord, tailWord_3236662, baseEnd_3236662] using wordTrace_append hprefix tailTrace_3236662
  have hstable : (prefixWord ++ tailWord_3236662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236662).length < 2 ^ (prefixWord ++ tailWord_3236662).sum := by decide
  have hdescent : baseEnd_3236662 < baseStart_3236662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236664 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_3236664 : Nat := 118140960795 + 3236664 * 2 ^ 59
def prefixEnd_3236664 : Nat := 4983230072969 + 3 ^ 40 * 3236664 * 2
def baseEnd_3236664 : Nat := 1661964349104029770914859

theorem tailTrace_3236664 : CollatzResearch.WordTrace tailWord_3236664 prefixEnd_3236664 1661964349104029770914859 := by
  unfold tailWord_3236664
  simp only [CollatzResearch.WordTrace]
  refine ⟨59025417173063290523694523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78700556230751054031592697 59025417173063290523694523)
  ·
    refine ⟨88538125759594935785541785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59025417173063290523694523 88538125759594935785541785)
    ·
      refine ⟨66403594319696201839156339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88538125759594935785541785 66403594319696201839156339)
      ·
        refine ⟨99605391479544302758734509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66403594319696201839156339 99605391479544302758734509)
        ·
          refine ⟨37352021804829113534525441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99605391479544302758734509 37352021804829113534525441)
          ·
            refine ⟨28014016353621835150894081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37352021804829113534525441 28014016353621835150894081)
            ·
              refine ⟨21010512265216376363170561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28014016353621835150894081 21010512265216376363170561)
              ·
                refine ⟨15757884198912282272377921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21010512265216376363170561 15757884198912282272377921)
                ·
                  refine ⟨11818413149184211704283441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15757884198912282272377921 11818413149184211704283441)
                  ·
                    refine ⟨8863809861888158778212581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11818413149184211704283441 8863809861888158778212581)
                    ·
                      refine ⟨1661964349104029770914859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8863809861888158778212581 1661964349104029770914859)
                      ·
                        rfl

theorem cell23_3236664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_3236664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236664 prefixEnd_3236664 := by exact prefixLift 3236664
  have htrace : WordTrace (prefixWord ++ tailWord_3236664) baseStart_3236664 baseEnd_3236664 := by
    simpa [prefixWord, tailWord_3236664, baseEnd_3236664] using wordTrace_append hprefix tailTrace_3236664
  have hstable : (prefixWord ++ tailWord_3236664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236664).length < 2 ^ (prefixWord ++ tailWord_3236664).sum := by decide
  have hdescent : baseEnd_3236664 < baseStart_3236664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236704 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 1, 7]
def baseStart_3236704 : Nat := 118140960795 + 3236704 * 2 ^ 59
def prefixEnd_3236704 : Nat := 4983230072969 + 3 ^ 40 * 3236704 * 2
def baseEnd_3236704 : Nat := 553994962776736538138225

theorem tailTrace_3236704 : CollatzResearch.WordTrace tailWord_3236704 prefixEnd_3236704 553994962776736538138225 := by
  unfold tailWord_3236704
  simp only [CollatzResearch.WordTrace]
  refine ⟨59026146632990833939422583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78701528843987778585896777 59026146632990833939422583)
  ·
    refine ⟨88539219949486250909133875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59026146632990833939422583 88539219949486250909133875)
    ·
      refine ⟨132808829924229376363700813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88539219949486250909133875 132808829924229376363700813)
      ·
        refine ⟨49803311221586016136387805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132808829924229376363700813 49803311221586016136387805)
        ·
          refine ⟨18676241708094756051145427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49803311221586016136387805 18676241708094756051145427)
          ·
            refine ⟨28014362562142134076718141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18676241708094756051145427 28014362562142134076718141)
            ·
              refine ⟨10505385960803300278769303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28014362562142134076718141 10505385960803300278769303)
              ·
                refine ⟨15758078941204950418153955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10505385960803300278769303 15758078941204950418153955)
                ·
                  refine ⟨23637118411807425627230933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15758078941204950418153955 23637118411807425627230933)
                  ·
                    refine ⟨553994962776736538138225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23637118411807425627230933 553994962776736538138225)
                    ·
                      rfl

theorem cell23_3236704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 7].length) (baseStart_3236704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236704 prefixEnd_3236704 := by exact prefixLift 3236704
  have htrace : WordTrace (prefixWord ++ tailWord_3236704) baseStart_3236704 baseEnd_3236704 := by
    simpa [prefixWord, tailWord_3236704, baseEnd_3236704] using wordTrace_append hprefix tailTrace_3236704
  have hstable : (prefixWord ++ tailWord_3236704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236704).length < 2 ^ (prefixWord ++ tailWord_3236704).sum := by decide
  have hdescent : baseEnd_3236704 < baseStart_3236704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236708 : List Nat := [2, 3, 1, 1, 4, 2, 2, 3, 5]
def baseStart_3236708 : Nat := 118140960795 + 3236708 * 2 ^ 59
def prefixEnd_3236708 : Nat := 4983230072969 + 3 ^ 40 * 3236708 * 2
def baseEnd_3236708 : Nat := 184665215805869733196073

theorem tailTrace_3236708 : CollatzResearch.WordTrace tailWord_3236708 prefixEnd_3236708 184665215805869733196073 := by
  unfold tailWord_3236708
  simp only [CollatzResearch.WordTrace]
  refine ⟨59026219578983588280995389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78701626105311451041327185 59026219578983588280995389)
  ·
    refine ⟨22134832342118845605373271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59026219578983588280995389 22134832342118845605373271)
    ·
      refine ⟨33202248513178268408059907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22134832342118845605373271 33202248513178268408059907)
      ·
        refine ⟨49803372769767402612089861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33202248513178268408059907 49803372769767402612089861)
        ·
          refine ⟨9338132394331387989766849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49803372769767402612089861 9338132394331387989766849)
          ·
            refine ⟨7003599295748540992325137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9338132394331387989766849 7003599295748540992325137)
            ·
              refine ⟨5252699471811405744243853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7003599295748540992325137 5252699471811405744243853)
              ·
                refine ⟨1969762301929277154091445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5252699471811405744243853 1969762301929277154091445)
                ·
                  refine ⟨184665215805869733196073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1969762301929277154091445 184665215805869733196073)
                  ·
                    rfl

theorem cell23_3236708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_3236708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236708 prefixEnd_3236708 := by exact prefixLift 3236708
  have htrace : WordTrace (prefixWord ++ tailWord_3236708) baseStart_3236708 baseEnd_3236708 := by
    simpa [prefixWord, tailWord_3236708, baseEnd_3236708] using wordTrace_append hprefix tailTrace_3236708
  have hstable : (prefixWord ++ tailWord_3236708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236708).length < 2 ^ (prefixWord ++ tailWord_3236708).sum := by decide
  have hdescent : baseEnd_3236708 < baseStart_3236708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236761 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 2, 2, 3]
def baseStart_3236761 : Nat := 118140960795 + 3236761 * 2 ^ 59
def prefixEnd_3236761 : Nat := 4983230072969 + 3 ^ 40 * 3236761 * 2
def baseEnd_3236761 : Nat := 1662014156727515891401913

theorem tailTrace_3236761 : CollatzResearch.WordTrace tailWord_3236761 prefixEnd_3236761 1662014156727515891401913 := by
  unfold tailWord_3236761
  simp only [CollatzResearch.WordTrace]
  refine ⟨118054372226775166613670137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78702914817850111075780091 118054372226775166613670137)
  ·
    refine ⟨88540779170081374960252603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118054372226775166613670137 88540779170081374960252603)
    ·
      refine ⟨132811168755122062440378905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88540779170081374960252603 132811168755122062440378905)
      ·
        refine ⟨99608376566341546830284179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132811168755122062440378905 99608376566341546830284179)
        ·
          refine ⟨149412564849512320245426269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99608376566341546830284179 149412564849512320245426269)
          ·
            refine ⟨56029711818567120092034851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149412564849512320245426269 56029711818567120092034851)
            ·
              refine ⟨84044567727850680138052277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56029711818567120092034851 84044567727850680138052277)
              ·
                refine ⟨7879178224486001262942401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84044567727850680138052277 7879178224486001262942401)
                ·
                  refine ⟨5909383668364500947206801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7879178224486001262942401 5909383668364500947206801)
                  ·
                    refine ⟨4432037751273375710405101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5909383668364500947206801 4432037751273375710405101)
                    ·
                      refine ⟨1662014156727515891401913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4432037751273375710405101 1662014156727515891401913)
                      ·
                        rfl

theorem cell23_3236761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_3236761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236761 prefixEnd_3236761 := by exact prefixLift 3236761
  have htrace : WordTrace (prefixWord ++ tailWord_3236761) baseStart_3236761 baseEnd_3236761 := by
    simpa [prefixWord, tailWord_3236761, baseEnd_3236761] using wordTrace_append hprefix tailTrace_3236761
  have hstable : (prefixWord ++ tailWord_3236761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236761).length < 2 ^ (prefixWord ++ tailWord_3236761).sum := by decide
  have hdescent : baseEnd_3236761 < baseStart_3236761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236785 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 3, 4]
def baseStart_3236785 : Nat := 118140960795 + 3236785 * 2 ^ 59
def prefixEnd_3236785 : Nat := 4983230072969 + 3 ^ 40 * 3236785 * 2
def baseEnd_3236785 : Nat := 554008826754407932500601

theorem tailTrace_3236785 : CollatzResearch.WordTrace tailWord_3236785 prefixEnd_3236785 554008826754407932500601 := by
  unfold tailWord_3236785
  simp only [CollatzResearch.WordTrace]
  refine ⟨118055247578688218712543809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78703498385792145808362539 118055247578688218712543809)
  ·
    refine ⟨88541435684016164034407857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118055247578688218712543809 88541435684016164034407857)
    ·
      refine ⟨66406076763012123025805893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88541435684016164034407857 66406076763012123025805893)
      ·
        refine ⟨12451139393064773067338605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66406076763012123025805893 12451139393064773067338605)
        ·
          refine ⟨4669177272399289900251977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12451139393064773067338605 4669177272399289900251977)
          ·
            refine ⟨3501882954299467425188983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4669177272399289900251977 3501882954299467425188983)
            ·
              refine ⟨5252824431449201137783475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501882954299467425188983 5252824431449201137783475)
              ·
                refine ⟨7879236647173801706675213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5252824431449201137783475 7879236647173801706675213)
                ·
                  refine ⟨2954713742690175640003205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7879236647173801706675213 2954713742690175640003205)
                  ·
                    refine ⟨554008826754407932500601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2954713742690175640003205 554008826754407932500601)
                    ·
                      rfl

theorem cell23_3236785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_3236785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236785 prefixEnd_3236785 := by exact prefixLift 3236785
  have htrace : WordTrace (prefixWord ++ tailWord_3236785) baseStart_3236785 baseEnd_3236785 := by
    simpa [prefixWord, tailWord_3236785, baseEnd_3236785] using wordTrace_append hprefix tailTrace_3236785
  have hstable : (prefixWord ++ tailWord_3236785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236785).length < 2 ^ (prefixWord ++ tailWord_3236785).sum := by decide
  have hdescent : baseEnd_3236785 < baseStart_3236785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236811 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 3, 5]
def baseStart_3236811 : Nat := 118140960795 + 3236811 * 2 ^ 59
def prefixEnd_3236811 : Nat := 4983230072969 + 3 ^ 40 * 3236811 * 2
def baseEnd_3236811 : Nat := 554013276920080231925561

theorem tailTrace_3236811 : CollatzResearch.WordTrace tailWord_3236811 prefixEnd_3236811 554013276920080231925561 := by
  unfold tailWord_3236811
  simp only [CollatzResearch.WordTrace]
  refine ⟨118056195876594025152990287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78704130584396016768660191 118056195876594025152990287)
  ·
    refine ⟨177084293814891037729485431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118056195876594025152990287 177084293814891037729485431)
    ·
      refine ⟨265626440722336556594228147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177084293814891037729485431 265626440722336556594228147)
      ·
        refine ⟨398439661083504834891342221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265626440722336556594228147 398439661083504834891342221)
        ·
          refine ⟨149414872906314313084253333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398439661083504834891342221 149414872906314313084253333)
          ·
            refine ⟨7003822167483483425824375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149414872906314313084253333 7003822167483483425824375)
            ·
              refine ⟨10505733251225225138736563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7003822167483483425824375 10505733251225225138736563)
              ·
                refine ⟨15758599876837837708104845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10505733251225225138736563 15758599876837837708104845)
                ·
                  refine ⟨5909474953814189140539317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15758599876837837708104845 5909474953814189140539317)
                  ·
                    refine ⟨554013276920080231925561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5909474953814189140539317 554013276920080231925561)
                    ·
                      rfl

theorem cell23_3236811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 5].length) (baseStart_3236811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236811 prefixEnd_3236811 := by exact prefixLift 3236811
  have htrace : WordTrace (prefixWord ++ tailWord_3236811) baseStart_3236811 baseEnd_3236811 := by
    simpa [prefixWord, tailWord_3236811, baseEnd_3236811] using wordTrace_append hprefix tailTrace_3236811
  have hstable : (prefixWord ++ tailWord_3236811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236811).length < 2 ^ (prefixWord ++ tailWord_3236811).sum := by decide
  have hdescent : baseEnd_3236811 < baseStart_3236811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236842 : List Nat := [3, 1, 3, 1, 2, 3, 1, 4, 1, 1, 3]
def baseStart_3236842 : Nat := 118140960795 + 3236842 * 2 ^ 59
def prefixEnd_3236842 : Nat := 4983230072969 + 3 ^ 40 * 3236842 * 2
def baseEnd_3236842 : Nat := 1662055748660530074489041

theorem tailTrace_3236842 : CollatzResearch.WordTrace tailWord_3236842 prefixEnd_3236842 1662055748660530074489041 := by
  unfold tailWord_3236842
  simp only [CollatzResearch.WordTrace]
  refine ⟨29514331634870429361842195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78704884359654478298245853 29514331634870429361842195)
  ·
    refine ⟨44271497452305644042763293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29514331634870429361842195 44271497452305644042763293)
    ·
      refine ⟨16601811544614616516036235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44271497452305644042763293 16601811544614616516036235)
      ·
        refine ⟨24902717316921924774054353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16601811544614616516036235 24902717316921924774054353)
        ·
          refine ⟨18677037987691443580540765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24902717316921924774054353 18677037987691443580540765)
          ·
            refine ⟨7003889245384291342702787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18677037987691443580540765 7003889245384291342702787)
            ·
              refine ⟨10505833868076437014054181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7003889245384291342702787 10505833868076437014054181)
              ·
                refine ⟨1969843850264331940135159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10505833868076437014054181 1969843850264331940135159)
                ·
                  refine ⟨2954765775396497910202739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969843850264331940135159 2954765775396497910202739)
                  ·
                    refine ⟨4432148663094746865304109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2954765775396497910202739 4432148663094746865304109)
                    ·
                      refine ⟨1662055748660530074489041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4432148663094746865304109 1662055748660530074489041)
                      ·
                        rfl

theorem cell23_3236842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_3236842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236842 prefixEnd_3236842 := by exact prefixLift 3236842
  have htrace : WordTrace (prefixWord ++ tailWord_3236842) baseStart_3236842 baseEnd_3236842 := by
    simpa [prefixWord, tailWord_3236842, baseEnd_3236842] using wordTrace_append hprefix tailTrace_3236842
  have hstable : (prefixWord ++ tailWord_3236842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236842).length < 2 ^ (prefixWord ++ tailWord_3236842).sum := by decide
  have hdescent : baseEnd_3236842 < baseStart_3236842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236865 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_3236865 : Nat := 118140960795 + 3236865 * 2 ^ 59
def prefixEnd_3236865 : Nat := 4983230072969 + 3 ^ 40 * 3236865 * 2
def baseEnd_3236865 : Nat := 1662067558715583484501435

theorem tailTrace_3236865 : CollatzResearch.WordTrace tailWord_3236865 prefixEnd_3236865 1662067558715583484501435 := by
  unfold tailWord_3236865
  simp only [CollatzResearch.WordTrace]
  refine ⟨118058165418398392375456049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78705443612265594916970699 118058165418398392375456049)
  ·
    refine ⟨88543624063798794281592037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118058165418398392375456049 88543624063798794281592037)
    ·
      refine ⟨16601929511962273927798507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88543624063798794281592037 16601929511962273927798507)
      ·
        refine ⟨24902894267943410891697761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16601929511962273927798507 24902894267943410891697761)
        ·
          refine ⟨18677170700957558168773321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24902894267943410891697761 18677170700957558168773321)
          ·
            refine ⟨14007878025718168626579991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18677170700957558168773321 14007878025718168626579991)
            ·
              refine ⟨21011817038577252939869987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14007878025718168626579991 21011817038577252939869987)
              ·
                refine ⟨31517725557865879409804981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21011817038577252939869987 31517725557865879409804981)
                ·
                  refine ⟨2954786771049926194669217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31517725557865879409804981 2954786771049926194669217)
                  ·
                    refine ⟨2216090078287444646001913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2954786771049926194669217 2216090078287444646001913)
                    ·
                      refine ⟨1662067558715583484501435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2216090078287444646001913 1662067558715583484501435)
                      ·
                        rfl

theorem cell23_3236865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_3236865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236865 prefixEnd_3236865 := by exact prefixLift 3236865
  have htrace : WordTrace (prefixWord ++ tailWord_3236865) baseStart_3236865 baseEnd_3236865 := by
    simpa [prefixWord, tailWord_3236865, baseEnd_3236865] using wordTrace_append hprefix tailTrace_3236865
  have hstable : (prefixWord ++ tailWord_3236865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236865).length < 2 ^ (prefixWord ++ tailWord_3236865).sum := by decide
  have hdescent : baseEnd_3236865 < baseStart_3236865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236878 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3236878 : Nat := 118140960795 + 3236878 * 2 ^ 59
def prefixEnd_3236878 : Nat := 4983230072969 + 3 ^ 40 * 3236878 * 2
def baseEnd_3236878 : Nat := 1662074233964091933638875

theorem tailTrace_3236878 : CollatzResearch.WordTrace tailWord_3236878 prefixEnd_3236878 1662074233964091933638875 := by
  unfold tailWord_3236878
  simp only [CollatzResearch.WordTrace]
  refine ⟨14757329945918911949459911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78705759711567530397119525 14757329945918911949459911)
  ·
    refine ⟨22135994918878367924189867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14757329945918911949459911 22135994918878367924189867)
    ·
      refine ⟨33203992378317551886284801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22135994918878367924189867 33203992378317551886284801)
      ·
        refine ⟨24902994283738163914713601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33203992378317551886284801 24902994283738163914713601)
        ·
          refine ⟨18677245712803622936035201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24902994283738163914713601 18677245712803622936035201)
          ·
            refine ⟨14007934284602717202026401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18677245712803622936035201 14007934284602717202026401)
            ·
              refine ⟨10505950713452037901519801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14007934284602717202026401 10505950713452037901519801)
              ·
                refine ⟨7879463035089028426139851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10505950713452037901519801 7879463035089028426139851)
                ·
                  refine ⟨11819194552633542639209777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7879463035089028426139851 11819194552633542639209777)
                  ·
                    refine ⟨8864395914475156979407333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11819194552633542639209777 8864395914475156979407333)
                    ·
                      refine ⟨1662074233964091933638875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8864395914475156979407333 1662074233964091933638875)
                      ·
                        rfl

theorem cell23_3236878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3236878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236878 prefixEnd_3236878 := by exact prefixLift 3236878
  have htrace : WordTrace (prefixWord ++ tailWord_3236878) baseStart_3236878 baseEnd_3236878 := by
    simpa [prefixWord, tailWord_3236878, baseEnd_3236878] using wordTrace_append hprefix tailTrace_3236878
  have hstable : (prefixWord ++ tailWord_3236878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236878).length < 2 ^ (prefixWord ++ tailWord_3236878).sum := by decide
  have hdescent : baseEnd_3236878 < baseStart_3236878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236885 : List Nat := [1, 3, 2, 1, 4, 2, 1, 3, 1, 2, 3]
def baseStart_3236885 : Nat := 118140960795 + 3236885 * 2 ^ 59
def prefixEnd_3236885 : Nat := 4983230072969 + 3 ^ 40 * 3236885 * 2
def baseEnd_3236885 : Nat := 1662077828328673406251343

theorem tailTrace_3236885 : CollatzResearch.WordTrace tailWord_3236885 prefixEnd_3236885 1662077828328673406251343 := by
  unfold tailWord_3236885
  simp only [CollatzResearch.WordTrace]
  refine ⟨118058894878325935791184109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78705929918883957194122739 118058894878325935791184109)
  ·
    refine ⟨44272085579372225921694041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118058894878325935791184109 44272085579372225921694041)
    ·
      refine ⟨33204064184529169441270531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44272085579372225921694041 33204064184529169441270531)
      ·
        refine ⟨49806096276793754161905797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33204064184529169441270531 49806096276793754161905797)
        ·
          refine ⟨9338643051898828905357337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49806096276793754161905797 9338643051898828905357337)
          ·
            refine ⟨7003982288924121679018003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9338643051898828905357337 7003982288924121679018003)
            ·
              refine ⟨10505973433386182518527005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7003982288924121679018003 10505973433386182518527005)
              ·
                refine ⟨3939740037519818444447627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10505973433386182518527005 3939740037519818444447627)
                ·
                  refine ⟨5909610056279727666671441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3939740037519818444447627 5909610056279727666671441)
                  ·
                    refine ⟨4432207542209795750003581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5909610056279727666671441 4432207542209795750003581)
                    ·
                      refine ⟨1662077828328673406251343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4432207542209795750003581 1662077828328673406251343)
                      ·
                        rfl

theorem cell23_3236885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_3236885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236885 prefixEnd_3236885 := by exact prefixLift 3236885
  have htrace : WordTrace (prefixWord ++ tailWord_3236885) baseStart_3236885 baseEnd_3236885 := by
    simpa [prefixWord, tailWord_3236885, baseEnd_3236885] using wordTrace_append hprefix tailTrace_3236885
  have hstable : (prefixWord ++ tailWord_3236885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236885).length < 2 ^ (prefixWord ++ tailWord_3236885).sum := by decide
  have hdescent : baseEnd_3236885 < baseStart_3236885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236892 : List Nat := [2, 2, 3, 1, 4, 2, 1, 2, 2, 4]
def baseStart_3236892 : Nat := 118140960795 + 3236892 * 2 ^ 59
def prefixEnd_3236892 : Nat := 4983230072969 + 3 ^ 40 * 3236892 * 2
def baseEnd_3236892 : Nat := 554027140897751626287937

theorem tailTrace_3236892 : CollatzResearch.WordTrace tailWord_3236892 prefixEnd_3236892 554027140897751626287937 := by
  unfold tailWord_3236892
  simp only [CollatzResearch.WordTrace]
  refine ⟨59029575094650287993344465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78706100126200383991125953 59029575094650287993344465)
  ·
    refine ⟨44272181320987715995008349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59029575094650287993344465 44272181320987715995008349)
    ·
      refine ⟨16602067995370393498128131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44272181320987715995008349 16602067995370393498128131)
      ·
        refine ⟨24903101993055590247192197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16602067995370393498128131 24903101993055590247192197)
        ·
          refine ⟨4669331623697923171348537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24903101993055590247192197 4669331623697923171348537)
          ·
            refine ⟨3501998717773442378511403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4669331623697923171348537 3501998717773442378511403)
            ·
              refine ⟨5252998076660163567767105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501998717773442378511403 5252998076660163567767105)
              ·
                refine ⟨3939748557495122675825329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5252998076660163567767105 3939748557495122675825329)
                ·
                  refine ⟨2954811418121342006868997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3939748557495122675825329 2954811418121342006868997)
                  ·
                    refine ⟨554027140897751626287937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2954811418121342006868997 554027140897751626287937)
                    ·
                      rfl

theorem cell23_3236892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_3236892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236892 prefixEnd_3236892 := by exact prefixLift 3236892
  have htrace : WordTrace (prefixWord ++ tailWord_3236892) baseStart_3236892 baseEnd_3236892 := by
    simpa [prefixWord, tailWord_3236892, baseEnd_3236892] using wordTrace_append hprefix tailTrace_3236892
  have hstable : (prefixWord ++ tailWord_3236892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236892).length < 2 ^ (prefixWord ++ tailWord_3236892).sum := by decide
  have hdescent : baseEnd_3236892 < baseStart_3236892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236950 : List Nat := [5, 2, 2, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_3236950 : Nat := 118140960795 + 3236950 * 2 ^ 59
def prefixEnd_3236950 : Nat := 4983230072969 + 3 ^ 40 * 3236950 * 2
def baseEnd_3236950 : Nat := 1662111204571215651938545

theorem tailTrace_3236950 : CollatzResearch.WordTrace tailWord_3236950 prefixEnd_3236950 1662111204571215651938545 := by
  unfold tailWord_3236950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7378829101443153243268769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78707510415393634594866869 7378829101443153243268769)
  ·
    refine ⟨5534121826082364932451577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7378829101443153243268769 5534121826082364932451577)
    ·
      refine ⟨4150591369561773699338683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5534121826082364932451577 4150591369561773699338683)
      ·
        refine ⟨6225887054342660549008025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4150591369561773699338683 6225887054342660549008025)
        ·
          refine ⟨4669415290756995411756019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6225887054342660549008025 4669415290756995411756019)
          ·
            refine ⟨7004122936135493117634029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4669415290756995411756019 7004122936135493117634029)
            ·
              refine ⟨2626546101050809919112761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7004122936135493117634029 2626546101050809919112761)
              ·
                refine ⟨1969909575788107439334571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2626546101050809919112761 1969909575788107439334571)
                ·
                  refine ⟨2954864363682161159001857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969909575788107439334571 2954864363682161159001857)
                  ·
                    refine ⟨2216148272761620869251393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2954864363682161159001857 2216148272761620869251393)
                    ·
                      refine ⟨1662111204571215651938545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2216148272761620869251393 1662111204571215651938545)
                      ·
                        rfl

theorem cell23_3236950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_3236950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236950 prefixEnd_3236950 := by exact prefixLift 3236950
  have htrace : WordTrace (prefixWord ++ tailWord_3236950) baseStart_3236950 baseEnd_3236950 := by
    simpa [prefixWord, tailWord_3236950, baseEnd_3236950] using wordTrace_append hprefix tailTrace_3236950
  have hstable : (prefixWord ++ tailWord_3236950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236950).length < 2 ^ (prefixWord ++ tailWord_3236950).sum := by decide
  have hdescent : baseEnd_3236950 < baseStart_3236950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3236972 : List Nat := [2, 2, 1, 1, 3, 2, 3, 3, 2, 2, 2]
def baseStart_3236972 : Nat := 118140960795 + 3236972 * 2 ^ 59
def prefixEnd_3236972 : Nat := 4983230072969 + 3 ^ 40 * 3236972 * 2
def baseEnd_3236972 : Nat := 1662122501145614565863443

theorem tailTrace_3236972 : CollatzResearch.WordTrace tailWord_3236972 prefixEnd_3236972 1662122501145614565863443 := by
  unfold tailWord_3236972
  simp only [CollatzResearch.WordTrace]
  refine ⟨59031034014505374824800585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78708045352673833099734113 59031034014505374824800585)
  ·
    refine ⟨44273275510879031118600439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59031034014505374824800585 44273275510879031118600439)
    ·
      refine ⟨66409913266318546677900659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44273275510879031118600439 66409913266318546677900659)
      ·
        refine ⟨99614869899477820016850989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66409913266318546677900659 99614869899477820016850989)
        ·
          refine ⟨37355576212304182506319121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99614869899477820016850989 37355576212304182506319121)
          ·
            refine ⟨28016682159228136879739341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37355576212304182506319121 28016682159228136879739341)
            ·
              refine ⟨10506255809710551329902253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28016682159228136879739341 10506255809710551329902253)
              ·
                refine ⟨3939845928641456748713345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10506255809710551329902253 3939845928641456748713345)
                ·
                  refine ⟨2954884446481092561535009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3939845928641456748713345 2954884446481092561535009)
                  ·
                    refine ⟨2216163334860819421151257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2954884446481092561535009 2216163334860819421151257)
                    ·
                      refine ⟨1662122501145614565863443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2216163334860819421151257 1662122501145614565863443)
                      ·
                        rfl

theorem cell23_3236972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 2, 2].length) (baseStart_3236972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3236972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3236972 prefixEnd_3236972 := by exact prefixLift 3236972
  have htrace : WordTrace (prefixWord ++ tailWord_3236972) baseStart_3236972 baseEnd_3236972 := by
    simpa [prefixWord, tailWord_3236972, baseEnd_3236972] using wordTrace_append hprefix tailTrace_3236972
  have hstable : (prefixWord ++ tailWord_3236972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3236972).length < 2 ^ (prefixWord ++ tailWord_3236972).sum := by decide
  have hdescent : baseEnd_3236972 < baseStart_3236972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3236972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237015 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 2, 5, 2]
def baseStart_3237015 : Nat := 118140960795 + 3237015 * 2 ^ 59
def prefixEnd_3237015 : Nat := 4983230072969 + 3 ^ 40 * 3237015 * 2
def baseEnd_3237015 : Nat := 1662144580813757897625745

theorem tailTrace_3237015 : CollatzResearch.WordTrace tailWord_3237015 prefixEnd_3237015 1662144580813757897625745 := by
  unfold tailWord_3237015
  simp only [CollatzResearch.WordTrace]
  refine ⟨118063636367854967993416499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78709090911903311995610999 118063636367854967993416499)
  ·
    refine ⟨177095454551782451990124749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118063636367854967993416499 177095454551782451990124749)
    ·
      refine ⟨66410795456918419496296781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177095454551782451990124749 66410795456918419496296781)
      ·
        refine ⟨24904048296344407311111293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66410795456918419496296781 24904048296344407311111293)
        ·
          refine ⟨9339018111129152741666735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24904048296344407311111293 9339018111129152741666735)
          ·
            refine ⟨14008527166693729112500103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9339018111129152741666735 14008527166693729112500103)
            ·
              refine ⟨21012790750040593668750155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14008527166693729112500103 21012790750040593668750155)
              ·
                refine ⟨31519186125060890503125233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21012790750040593668750155 31519186125060890503125233)
                ·
                  refine ⟨23639389593795667877343925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31519186125060890503125233 23639389593795667877343925)
                  ·
                    refine ⟨2216192774418343863500993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23639389593795667877343925 2216192774418343863500993)
                    ·
                      refine ⟨1662144580813757897625745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2216192774418343863500993 1662144580813757897625745)
                      ·
                        rfl

theorem cell23_3237015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_3237015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237015 prefixEnd_3237015 := by exact prefixLift 3237015
  have htrace : WordTrace (prefixWord ++ tailWord_3237015) baseStart_3237015 baseEnd_3237015 := by
    simpa [prefixWord, tailWord_3237015, baseEnd_3237015] using wordTrace_append hprefix tailTrace_3237015
  have hstable : (prefixWord ++ tailWord_3237015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237015).length < 2 ^ (prefixWord ++ tailWord_3237015).sum := by decide
  have hdescent : baseEnd_3237015 < baseStart_3237015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237022 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_3237022 : Nat := 118140960795 + 3237022 * 2 ^ 59
def prefixEnd_3237022 : Nat := 4983230072969 + 3 ^ 40 * 3237022 * 2
def baseEnd_3237022 : Nat := 1662148175178339370238213

theorem tailTrace_3237022 : CollatzResearch.WordTrace tailWord_3237022 prefixEnd_3237022 1662148175178339370238213 := by
  unfold tailWord_3237022
  simp only [CollatzResearch.WordTrace]
  refine ⟨14757986459853701023615165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78709261119219738792614213 14757986459853701023615165)
  ·
    refine ⟨5534244922445137883855687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14757986459853701023615165 5534244922445137883855687)
    ·
      refine ⟨8301367383667706825783531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5534244922445137883855687 8301367383667706825783531)
      ·
        refine ⟨12452051075501560238675297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8301367383667706825783531 12452051075501560238675297)
        ·
          refine ⟨9339038306626170179006473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12452051075501560238675297 9339038306626170179006473)
          ·
            refine ⟨7004278729969627634254855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9339038306626170179006473 7004278729969627634254855)
            ·
              refine ⟨10506418094954441451382283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7004278729969627634254855 10506418094954441451382283)
              ·
                refine ⟨15759627142431662177073425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10506418094954441451382283 15759627142431662177073425)
                ·
                  refine ⟨11819720356823746632805069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15759627142431662177073425 11819720356823746632805069)
                  ·
                    refine ⟨4432395133808904987301901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11819720356823746632805069 4432395133808904987301901)
                    ·
                      refine ⟨1662148175178339370238213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4432395133808904987301901 1662148175178339370238213)
                      ·
                        rfl

theorem cell23_3237022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_3237022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237022 prefixEnd_3237022 := by exact prefixLift 3237022
  have htrace : WordTrace (prefixWord ++ tailWord_3237022) baseStart_3237022 baseEnd_3237022 := by
    simpa [prefixWord, tailWord_3237022, baseEnd_3237022] using wordTrace_append hprefix tailTrace_3237022
  have hstable : (prefixWord ++ tailWord_3237022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237022).length < 2 ^ (prefixWord ++ tailWord_3237022).sum := by decide
  have hdescent : baseEnd_3237022 < baseStart_3237022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237046 : List Nat := [5, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_3237046 : Nat := 118140960795 + 3237046 * 2 ^ 59
def prefixEnd_3237046 : Nat := 4983230072969 + 3 ^ 40 * 3237046 * 2
def baseEnd_3237046 : Nat := 184684499857116364037567

theorem tailTrace_3237046 : CollatzResearch.WordTrace tailWord_3237046 prefixEnd_3237046 184684499857116364037567 := by
  unfold tailWord_3237046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7379047939421416267987187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78709844687161773525196661 7379047939421416267987187)
  ·
    refine ⟨11068571909132124401980781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7379047939421416267987187 11068571909132124401980781)
    ·
      refine ⟨4150714465924546650742793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11068571909132124401980781 4150714465924546650742793)
      ·
        refine ⟨3113035849443409988057095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4150714465924546650742793 3113035849443409988057095)
        ·
          refine ⟨4669553774165114982085643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113035849443409988057095 4669553774165114982085643)
          ·
            refine ⟨7004330661247672473128465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4669553774165114982085643 7004330661247672473128465)
            ·
              refine ⟨5253247995935754354846349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7004330661247672473128465 5253247995935754354846349)
              ·
                refine ⟨1969967998475907883067381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5253247995935754354846349 1969967998475907883067381)
                ·
                  refine ⟨184684499857116364037567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1969967998475907883067381 184684499857116364037567)
                  ·
                    rfl

theorem cell23_3237046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_3237046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237046 prefixEnd_3237046 := by exact prefixLift 3237046
  have htrace : WordTrace (prefixWord ++ tailWord_3237046) baseStart_3237046 baseEnd_3237046 := by
    simpa [prefixWord, tailWord_3237046, baseEnd_3237046] using wordTrace_append hprefix tailTrace_3237046
  have hstable : (prefixWord ++ tailWord_3237046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237046).length < 2 ^ (prefixWord ++ tailWord_3237046).sum := by decide
  have hdescent : baseEnd_3237046 < baseStart_3237046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237106 : List Nat := [3, 2, 1, 3, 3, 2, 1, 3, 1, 4]
def baseStart_3237106 : Nat := 118140960795 + 3237106 * 2 ^ 59
def prefixEnd_3237106 : Nat := 4983230072969 + 3 ^ 40 * 3237106 * 2
def baseEnd_3237106 : Nat := 554063769184439013862609

theorem tailTrace_3237106 : CollatzResearch.WordTrace tailWord_3237106 prefixEnd_3237106 554063769184439013862609 := by
  unfold tailWord_3237106
  simp only [CollatzResearch.WordTrace]
  refine ⟨29516738852631322633744793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78711303607016860356652781 29516738852631322633744793)
  ·
    refine ⟨22137554139473491975308595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29516738852631322633744793 22137554139473491975308595)
    ·
      refine ⟨33206331209210237962962893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22137554139473491975308595 33206331209210237962962893)
      ·
        refine ⟨12452374203453839236111085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33206331209210237962962893 12452374203453839236111085)
        ·
          refine ⟨4669640326295189713541657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12452374203453839236111085 4669640326295189713541657)
          ·
            refine ⟨3502230244721392285156243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4669640326295189713541657 3502230244721392285156243)
            ·
              refine ⟨5253345367082088427734365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3502230244721392285156243 5253345367082088427734365)
              ·
                refine ⟨1970004512655783160400387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5253345367082088427734365 1970004512655783160400387)
                ·
                  refine ⟨2955006768983674740600581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970004512655783160400387 2955006768983674740600581)
                  ·
                    refine ⟨554063769184439013862609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2955006768983674740600581 554063769184439013862609)
                    ·
                      rfl

theorem cell23_3237106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_3237106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237106 prefixEnd_3237106 := by exact prefixLift 3237106
  have htrace : WordTrace (prefixWord ++ tailWord_3237106) baseStart_3237106 baseEnd_3237106 := by
    simpa [prefixWord, tailWord_3237106, baseEnd_3237106] using wordTrace_append hprefix tailTrace_3237106
  have hstable : (prefixWord ++ tailWord_3237106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237106).length < 2 ^ (prefixWord ++ tailWord_3237106).sum := by decide
  have hdescent : baseEnd_3237106 < baseStart_3237106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237149 : List Nat := [1, 4, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_3237149 : Nat := 118140960795 + 3237149 * 2 ^ 59
def prefixEnd_3237149 : Nat := 4983230072969 + 3 ^ 40 * 3237149 * 2
def baseEnd_3237149 : Nat := 554071129073820124450043

theorem tailTrace_3237149 : CollatzResearch.WordTrace tailWord_3237149 prefixEnd_3237149 554071129073820124450043 := by
  unfold tailWord_3237149
  simp only [CollatzResearch.WordTrace]
  refine ⟨118068523749369508878794501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78712349166246339252529667 118068523749369508878794501)
  ·
    refine ⟨22137848203006782914773969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118068523749369508878794501 22137848203006782914773969)
    ·
      refine ⟨16603386152255087186080477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22137848203006782914773969 16603386152255087186080477)
      ·
        refine ⟨6226269807095657694780179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16603386152255087186080477 6226269807095657694780179)
        ·
          refine ⟨9339404710643486542170269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6226269807095657694780179 9339404710643486542170269)
          ·
            refine ⟨3502276766491307453313851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9339404710643486542170269 3502276766491307453313851)
            ·
              refine ⟨5253415149736961179970777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3502276766491307453313851 5253415149736961179970777)
              ·
                refine ⟨3940061362302720884978083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5253415149736961179970777 3940061362302720884978083)
                ·
                  refine ⟨5910092043454081327467125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3940061362302720884978083 5910092043454081327467125)
                  ·
                    refine ⟨554071129073820124450043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5910092043454081327467125 554071129073820124450043)
                    ·
                      rfl

theorem cell23_3237149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_3237149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237149 prefixEnd_3237149 := by exact prefixLift 3237149
  have htrace : WordTrace (prefixWord ++ tailWord_3237149) baseStart_3237149 baseEnd_3237149 := by
    simpa [prefixWord, tailWord_3237149, baseEnd_3237149] using wordTrace_append hprefix tailTrace_3237149
  have hstable : (prefixWord ++ tailWord_3237149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237149).length < 2 ^ (prefixWord ++ tailWord_3237149).sum := by decide
  have hdescent : baseEnd_3237149 < baseStart_3237149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237152 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3237152 : Nat := 118140960795 + 3237152 * 2 ^ 59
def prefixEnd_3237152 : Nat := 4983230072969 + 3 ^ 40 * 3237152 * 2
def baseEnd_3237152 : Nat := 1662214927663423861612615

theorem tailTrace_3237152 : CollatzResearch.WordTrace tailWord_3237152 prefixEnd_3237152 1662214927663423861612615 := by
  unfold tailWord_3237152
  simp only [CollatzResearch.WordTrace]
  refine ⟨59034316584179320195576855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78712422112239093594102473 59034316584179320195576855)
  ·
    refine ⟨88551474876268980293365283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59034316584179320195576855 88551474876268980293365283)
    ·
      refine ⟨132827212314403470440047925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88551474876268980293365283 132827212314403470440047925)
      ·
        refine ⟨12452551154475325353754493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132827212314403470440047925 12452551154475325353754493)
        ·
          refine ⟨4669706682928247007657935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12452551154475325353754493 4669706682928247007657935)
          ·
            refine ⟨7004560024392370511486903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4669706682928247007657935 7004560024392370511486903)
            ·
              refine ⟨10506840036588555767230355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7004560024392370511486903 10506840036588555767230355)
              ·
                refine ⟨15760260054882833650845533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10506840036588555767230355 15760260054882833650845533)
                ·
                  refine ⟨5910097520581062619067075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15760260054882833650845533 5910097520581062619067075)
                  ·
                    refine ⟨8865146280871593928600613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5910097520581062619067075 8865146280871593928600613)
                    ·
                      refine ⟨1662214927663423861612615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8865146280871593928600613 1662214927663423861612615)
                      ·
                        rfl

theorem cell23_3237152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3237152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237152 prefixEnd_3237152 := by exact prefixLift 3237152
  have htrace : WordTrace (prefixWord ++ tailWord_3237152) baseStart_3237152 baseEnd_3237152 := by
    simpa [prefixWord, tailWord_3237152, baseEnd_3237152] using wordTrace_append hprefix tailTrace_3237152
  have hstable : (prefixWord ++ tailWord_3237152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237152).length < 2 ^ (prefixWord ++ tailWord_3237152).sum := by decide
  have hdescent : baseEnd_3237152 < baseStart_3237152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237162 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 1, 6]
def baseStart_3237162 : Nat := 118140960795 + 3237162 * 2 ^ 59
def prefixEnd_3237162 : Nat := 4983230072969 + 3 ^ 40 * 3237162 * 2
def baseEnd_3237162 : Nat := 554073354156656274162523

theorem tailTrace_3237162 : CollatzResearch.WordTrace tailWord_3237162 prefixEnd_3237162 554073354156656274162523 := by
  unfold tailWord_3237162
  simp only [CollatzResearch.WordTrace]
  refine ⟨29517249474580603024754435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78712665265548274732678493 29517249474580603024754435)
  ·
    refine ⟨44275874211870904537131653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29517249474580603024754435 44275874211870904537131653)
    ·
      refine ⟨8301726414725794600712185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44275874211870904537131653 8301726414725794600712185)
      ·
        refine ⟨6226294811044345950534139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8301726414725794600712185 6226294811044345950534139)
        ·
          refine ⟨9339442216566518925801209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6226294811044345950534139 9339442216566518925801209)
          ·
            refine ⟨7004581662424889194350907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9339442216566518925801209 7004581662424889194350907)
            ·
              refine ⟨10506872493637333791526361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7004581662424889194350907 10506872493637333791526361)
              ·
                refine ⟨7880154370228000343644771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10506872493637333791526361 7880154370228000343644771)
                ·
                  refine ⟨11820231555342000515467157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7880154370228000343644771 11820231555342000515467157)
                  ·
                    refine ⟨554073354156656274162523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11820231555342000515467157 554073354156656274162523)
                    ·
                      rfl

theorem cell23_3237162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_3237162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237162 prefixEnd_3237162 := by exact prefixLift 3237162
  have htrace : WordTrace (prefixWord ++ tailWord_3237162) baseStart_3237162 baseEnd_3237162 := by
    simpa [prefixWord, tailWord_3237162, baseEnd_3237162] using wordTrace_append hprefix tailTrace_3237162
  have hstable : (prefixWord ++ tailWord_3237162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237162).length < 2 ^ (prefixWord ++ tailWord_3237162).sum := by decide
  have hdescent : baseEnd_3237162 < baseStart_3237162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237169 : List Nat := [1, 2, 2, 3, 3, 2, 3, 1, 1, 1, 4]
def baseStart_3237169 : Nat := 118140960795 + 3237169 * 2 ^ 59
def prefixEnd_3237169 : Nat := 4983230072969 + 3 ^ 40 * 3237169 * 2
def baseEnd_3237169 : Nat := 1662223656834550295100037

theorem tailTrace_3237169 : CollatzResearch.WordTrace tailWord_3237169 prefixEnd_3237169 1662223656834550295100037 := by
  unfold tailWord_3237169
  simp only [CollatzResearch.WordTrace]
  refine ⟨118069253209297052294522561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78712835472864701529681707 118069253209297052294522561)
  ·
    refine ⟨88551939906972789220891921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118069253209297052294522561 88551939906972789220891921)
    ·
      refine ⟨66413954930229591915668941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88551939906972789220891921 66413954930229591915668941)
      ·
        refine ⟨24905233098836096968375853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66413954930229591915668941 24905233098836096968375853)
        ·
          refine ⟨9339462412063536363140945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24905233098836096968375853 9339462412063536363140945)
          ·
            refine ⟨7004596809047652272355709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9339462412063536363140945 7004596809047652272355709)
            ·
              refine ⟨2626723803392869602133391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7004596809047652272355709 2626723803392869602133391)
              ·
                refine ⟨3940085705089304403200087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626723803392869602133391 3940085705089304403200087)
                ·
                  refine ⟨5910128557633956604800131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3940085705089304403200087 5910128557633956604800131)
                  ·
                    refine ⟨8865192836450934907200197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5910128557633956604800131 8865192836450934907200197)
                    ·
                      refine ⟨1662223656834550295100037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8865192836450934907200197 1662223656834550295100037)
                      ·
                        rfl

theorem cell23_3237169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_3237169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237169 prefixEnd_3237169 := by exact prefixLift 3237169
  have htrace : WordTrace (prefixWord ++ tailWord_3237169) baseStart_3237169 baseEnd_3237169 := by
    simpa [prefixWord, tailWord_3237169, baseEnd_3237169] using wordTrace_append hprefix tailTrace_3237169
  have hstable : (prefixWord ++ tailWord_3237169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237169).length < 2 ^ (prefixWord ++ tailWord_3237169).sum := by decide
  have hdescent : baseEnd_3237169 < baseStart_3237169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237202 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_3237202 : Nat := 118140960795 + 3237202 * 2 ^ 59
def prefixEnd_3237202 : Nat := 4983230072969 + 3 ^ 40 * 3237202 * 2
def baseEnd_3237202 : Nat := 1662240601696148665987385

theorem tailTrace_3237202 : CollatzResearch.WordTrace tailWord_3237202 prefixEnd_3237202 1662240601696148665987385 := by
  unfold tailWord_3237202
  simp only [CollatzResearch.WordTrace]
  refine ⟨29517614204544374732618465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78713637878784999286982573 29517614204544374732618465)
  ·
    refine ⟨22138210653408281049463849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29517614204544374732618465 22138210653408281049463849)
    ·
      refine ⟨16603657990056210787097887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22138210653408281049463849 16603657990056210787097887)
      ·
        refine ⟨24905486985084316180646831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16603657990056210787097887 24905486985084316180646831)
        ·
          refine ⟨37358230477626474270970247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24905486985084316180646831 37358230477626474270970247)
          ·
            refine ⟨56037345716439711406455371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37358230477626474270970247 56037345716439711406455371)
            ·
              refine ⟨84056018574659567109683057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56037345716439711406455371 84056018574659567109683057)
              ·
                refine ⟨63042013930994675332262293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84056018574659567109683057 63042013930994675332262293)
                ·
                  refine ⟨2955094403015375406199795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63042013930994675332262293 2955094403015375406199795)
                  ·
                    refine ⟨4432641604523063109299693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2955094403015375406199795 4432641604523063109299693)
                    ·
                      refine ⟨1662240601696148665987385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4432641604523063109299693 1662240601696148665987385)
                      ·
                        rfl

theorem cell23_3237202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_3237202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237202 prefixEnd_3237202 := by exact prefixLift 3237202
  have htrace : WordTrace (prefixWord ++ tailWord_3237202) baseStart_3237202 baseEnd_3237202 := by
    simpa [prefixWord, tailWord_3237202, baseEnd_3237202] using wordTrace_append hprefix tailTrace_3237202
  have hstable : (prefixWord ++ tailWord_3237202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237202).length < 2 ^ (prefixWord ++ tailWord_3237202).sum := by decide
  have hdescent : baseEnd_3237202 < baseStart_3237202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237223 : List Nat := [1, 1, 5, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_3237223 : Nat := 118140960795 + 3237223 * 2 ^ 59
def prefixEnd_3237223 : Nat := 4983230072969 + 3 ^ 40 * 3237223 * 2
def baseEnd_3237223 : Nat := 1662251384789893083824789

theorem tailTrace_3237223 : CollatzResearch.WordTrace tailWord_3237223 prefixEnd_3237223 1662251384789893083824789 := by
  unfold tailWord_3237223
  simp only [CollatzResearch.WordTrace]
  refine ⟨118071222751101419516988323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78714148500734279677992215 118071222751101419516988323)
  ·
    refine ⟨177106834126652129275482485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118071222751101419516988323 177106834126652129275482485)
    ·
      refine ⟨16603765699373637119576483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177106834126652129275482485 16603765699373637119576483)
      ·
        refine ⟨24905648549060455679364725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16603765699373637119576483 24905648549060455679364725)
        ·
          refine ⟨2334904551474417719940443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24905648549060455679364725 2334904551474417719940443)
          ·
            refine ⟨3502356827211626579910665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334904551474417719940443 3502356827211626579910665)
            ·
              refine ⟨2626767620408719934932999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3502356827211626579910665 2626767620408719934932999)
              ·
                refine ⟨3940151430613079902399499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626767620408719934932999 3940151430613079902399499)
                ·
                  refine ⟨5910227145919619853599249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3940151430613079902399499 5910227145919619853599249)
                  ·
                    refine ⟨4432670359439714890199437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5910227145919619853599249 4432670359439714890199437)
                    ·
                      refine ⟨1662251384789893083824789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4432670359439714890199437 1662251384789893083824789)
                      ·
                        rfl

theorem cell23_3237223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_3237223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237223 prefixEnd_3237223 := by exact prefixLift 3237223
  have htrace : WordTrace (prefixWord ++ tailWord_3237223) baseStart_3237223 baseEnd_3237223 := by
    simpa [prefixWord, tailWord_3237223, baseEnd_3237223] using wordTrace_append hprefix tailTrace_3237223
  have hstable : (prefixWord ++ tailWord_3237223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237223).length < 2 ^ (prefixWord ++ tailWord_3237223).sum := by decide
  have hdescent : baseEnd_3237223 < baseStart_3237223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237314 : List Nat := [3, 5, 2, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_3237314 : Nat := 118140960795 + 3237314 * 2 ^ 59
def prefixEnd_3237314 : Nat := 4983230072969 + 3 ^ 40 * 3237314 * 2
def baseEnd_3237314 : Nat := 1662298111529452227786871

theorem tailTrace_3237314 : CollatzResearch.WordTrace tailWord_3237314 prefixEnd_3237314 1662298111529452227786871 := by
  unfold tailWord_3237314
  simp only [CollatzResearch.WordTrace]
  refine ⟨29518635448442935514637749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78716361195847828039033997 29518635448442935514637749)
  ·
    refine ⟨2767372073291525204497289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29518635448442935514637749 2767372073291525204497289)
    ·
      refine ⟨2075529054968643903372967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2767372073291525204497289 2075529054968643903372967)
      ·
        refine ⟨3113293582452965855059451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2075529054968643903372967 3113293582452965855059451)
        ·
          refine ⟨4669940373679448782589177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113293582452965855059451 4669940373679448782589177)
          ·
            refine ⟨3502455280259586586941883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4669940373679448782589177 3502455280259586586941883)
            ·
              refine ⟨5253682920389379880412825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3502455280259586586941883 5253682920389379880412825)
              ·
                refine ⟨3940262190292034910309619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5253682920389379880412825 3940262190292034910309619)
                ·
                  refine ⟨5910393285438052365464429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3940262190292034910309619 5910393285438052365464429)
                  ·
                    refine ⟨2216397482039269637049161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5910393285438052365464429 2216397482039269637049161)
                    ·
                      refine ⟨1662298111529452227786871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2216397482039269637049161 1662298111529452227786871)
                      ·
                        rfl

theorem cell23_3237314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_3237314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237314 prefixEnd_3237314 := by exact prefixLift 3237314
  have htrace : WordTrace (prefixWord ++ tailWord_3237314) baseStart_3237314 baseEnd_3237314 := by
    simpa [prefixWord, tailWord_3237314, baseEnd_3237314] using wordTrace_append hprefix tailTrace_3237314
  have hstable : (prefixWord ++ tailWord_3237314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237314).length < 2 ^ (prefixWord ++ tailWord_3237314).sum := by decide
  have hdescent : baseEnd_3237314 < baseStart_3237314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237315 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 4]
def baseStart_3237315 : Nat := 118140960795 + 3237315 * 2 ^ 59
def prefixEnd_3237315 : Nat := 4983230072969 + 3 ^ 40 * 3237315 * 2
def baseEnd_3237315 : Nat := 1662298625010106723874365

theorem tailTrace_3237315 : CollatzResearch.WordTrace tailWord_3237315 prefixEnd_3237315 1662298625010106723874365 := by
  unfold tailWord_3237315
  simp only [CollatzResearch.WordTrace]
  refine ⟨118074578266768119229337399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78716385511178746152891599 118074578266768119229337399)
  ·
    refine ⟨177111867400152178844006099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118074578266768119229337399 177111867400152178844006099)
    ·
      refine ⟨265667801100228268266009149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177111867400152178844006099 265667801100228268266009149)
      ·
        refine ⟨99625425412585600599753431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265667801100228268266009149 99625425412585600599753431)
        ·
          refine ⟨149438138118878400899630147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99625425412585600599753431 149438138118878400899630147)
          ·
            refine ⟨224157207178317601349445221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149438138118878400899630147 224157207178317601349445221)
            ·
              refine ⟨42029476345934550253020979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224157207178317601349445221 42029476345934550253020979)
              ·
                refine ⟨63044214518901825379531469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42029476345934550253020979 63044214518901825379531469)
                ·
                  refine ⟨23641580444588184517324301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63044214518901825379531469 23641580444588184517324301)
                  ·
                    refine ⟨8865592666720569193996613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23641580444588184517324301 8865592666720569193996613)
                    ·
                      refine ⟨1662298625010106723874365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8865592666720569193996613 1662298625010106723874365)
                      ·
                        rfl

theorem cell23_3237315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_3237315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237315 prefixEnd_3237315 := by exact prefixLift 3237315
  have htrace : WordTrace (prefixWord ++ tailWord_3237315) baseStart_3237315 baseEnd_3237315 := by
    simpa [prefixWord, tailWord_3237315, baseEnd_3237315] using wordTrace_append hprefix tailTrace_3237315
  have hstable : (prefixWord ++ tailWord_3237315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237315).length < 2 ^ (prefixWord ++ tailWord_3237315).sum := by decide
  have hdescent : baseEnd_3237315 < baseStart_3237315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237349 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3237349 : Nat := 118140960795 + 3237349 * 2 ^ 59
def prefixEnd_3237349 : Nat := 4983230072969 + 3 ^ 40 * 3237349 * 2
def baseEnd_3237349 : Nat := 1662316083352359590849209

theorem tailTrace_3237349 : CollatzResearch.WordTrace tailWord_3237349 prefixEnd_3237349 1662316083352359590849209 := by
  unfold tailWord_3237349
  simp only [CollatzResearch.WordTrace]
  refine ⟨118075818348644943036075101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78717212232429962024050067 118075818348644943036075101)
  ·
    refine ⟨44278431880741853638528163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118075818348644943036075101 44278431880741853638528163)
    ·
      refine ⟨66417647821112780457792245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44278431880741853638528163 66417647821112780457792245)
      ·
        refine ⟨6226654483229323167918023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66417647821112780457792245 6226654483229323167918023)
        ·
          refine ⟨9339981724843984751877035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6226654483229323167918023 9339981724843984751877035)
          ·
            refine ⟨14009972587265977127815553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9339981724843984751877035 14009972587265977127815553)
            ·
              refine ⟨10507479440449482845861665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14009972587265977127815553 10507479440449482845861665)
              ·
                refine ⟨7880609580337112134396249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10507479440449482845861665 7880609580337112134396249)
                ·
                  refine ⟨5910457185252834100797187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7880609580337112134396249 5910457185252834100797187)
                  ·
                    refine ⟨8865685777879251151195781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5910457185252834100797187 8865685777879251151195781)
                    ·
                      refine ⟨1662316083352359590849209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8865685777879251151195781 1662316083352359590849209)
                      ·
                        rfl

theorem cell23_3237349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3237349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237349 prefixEnd_3237349 := by exact prefixLift 3237349
  have htrace : WordTrace (prefixWord ++ tailWord_3237349) baseStart_3237349 baseEnd_3237349 := by
    simpa [prefixWord, tailWord_3237349, baseEnd_3237349] using wordTrace_append hprefix tailTrace_3237349
  have hstable : (prefixWord ++ tailWord_3237349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237349).length < 2 ^ (prefixWord ++ tailWord_3237349).sum := by decide
  have hdescent : baseEnd_3237349 < baseStart_3237349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237366 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_3237366 : Nat := 118140960795 + 3237366 * 2 ^ 59
def prefixEnd_3237366 : Nat := 4983230072969 + 3 ^ 40 * 3237366 * 2
def baseEnd_3237366 : Nat := 1662324812523486024336631

theorem tailTrace_3237366 : CollatzResearch.WordTrace tailWord_3237366 prefixEnd_3237366 1662324812523486024336631 := by
  unfold tailWord_3237366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7379777399348959683715247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78717625593055569959629301 7379777399348959683715247)
  ·
    refine ⟨11069666099023439525572871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7379777399348959683715247 11069666099023439525572871)
    ·
      refine ⟨16604499148535159288359307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11069666099023439525572871 16604499148535159288359307)
      ·
        refine ⟨24906748722802738932538961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16604499148535159288359307 24906748722802738932538961)
        ·
          refine ⟨18680061542102054199404221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24906748722802738932538961 18680061542102054199404221)
          ·
            refine ⟨7005023078288270324776583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18680061542102054199404221 7005023078288270324776583)
            ·
              refine ⟨10507534617432405487164875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005023078288270324776583 10507534617432405487164875)
              ·
                refine ⟨15761301926148608230747313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10507534617432405487164875 15761301926148608230747313)
                ·
                  refine ⟨11820976444611456173060485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15761301926148608230747313 11820976444611456173060485)
                  ·
                    refine ⟨2216433083364648032448841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11820976444611456173060485 2216433083364648032448841)
                    ·
                      refine ⟨1662324812523486024336631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2216433083364648032448841 1662324812523486024336631)
                      ·
                        rfl

theorem cell23_3237366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_3237366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237366 prefixEnd_3237366 := by exact prefixLift 3237366
  have htrace : WordTrace (prefixWord ++ tailWord_3237366) baseStart_3237366 baseEnd_3237366 := by
    simpa [prefixWord, tailWord_3237366, baseEnd_3237366] using wordTrace_append hprefix tailTrace_3237366
  have hstable : (prefixWord ++ tailWord_3237366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237366).length < 2 ^ (prefixWord ++ tailWord_3237366).sum := by decide
  have hdescent : baseEnd_3237366 < baseStart_3237366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237372 : List Nat := [2, 2, 2, 1, 2, 1, 4, 3, 6]
def baseStart_3237372 : Nat := 118140960795 + 3237372 * 2 ^ 59
def prefixEnd_3237372 : Nat := 4983230072969 + 3 ^ 40 * 3237372 * 2
def baseEnd_3237372 : Nat := 184703099267490333429067

theorem tailTrace_3237372 : CollatzResearch.WordTrace tailWord_3237372 prefixEnd_3237372 184703099267490333429067 := by
  unfold tailWord_3237372
  simp only [CollatzResearch.WordTrace]
  refine ⟨59038328613780808982081185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78717771485041078642774913 59038328613780808982081185)
  ·
    refine ⟨44278746460335606736560889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59038328613780808982081185 44278746460335606736560889)
    ·
      refine ⟨33209059845251705052420667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44278746460335606736560889 33209059845251705052420667)
      ·
        refine ⟨49813589767877557578631001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33209059845251705052420667 49813589767877557578631001)
        ·
          refine ⟨37360192325908168183973251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49813589767877557578631001 37360192325908168183973251)
          ·
            refine ⟨56040288488862252275959877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37360192325908168183973251 56040288488862252275959877)
            ·
              refine ⟨10507554091661672301742477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56040288488862252275959877 10507554091661672301742477)
              ·
                refine ⟨3940332784373127113153429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10507554091661672301742477 3940332784373127113153429)
                ·
                  refine ⟨184703099267490333429067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3940332784373127113153429 184703099267490333429067)
                  ·
                    rfl

theorem cell23_3237372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 6].length) (baseStart_3237372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237372 prefixEnd_3237372 := by exact prefixLift 3237372
  have htrace : WordTrace (prefixWord ++ tailWord_3237372) baseStart_3237372 baseEnd_3237372 := by
    simpa [prefixWord, tailWord_3237372, baseEnd_3237372] using wordTrace_append hprefix tailTrace_3237372
  have hstable : (prefixWord ++ tailWord_3237372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237372).length < 2 ^ (prefixWord ++ tailWord_3237372).sum := by decide
  have hdescent : baseEnd_3237372 < baseStart_3237372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237375 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 6]
def baseStart_3237375 : Nat := 118140960795 + 3237375 * 2 ^ 59
def prefixEnd_3237375 : Nat := 4983230072969 + 3 ^ 40 * 3237375 * 2
def baseEnd_3237375 : Nat := 1662329433849376489124089

theorem tailTrace_3237375 : CollatzResearch.WordTrace tailWord_3237375 prefixEnd_3237375 1662329433849376489124089 := by
  unfold tailWord_3237375
  simp only [CollatzResearch.WordTrace]
  refine ⟨118076766646550749476521579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78717844431033832984347719 118076766646550749476521579)
  ·
    refine ⟨177115149969826124214782369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118076766646550749476521579 177115149969826124214782369)
    ·
      refine ⟨132836362477369593161086777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177115149969826124214782369 132836362477369593161086777)
      ·
        refine ⟨99627271858027194870815083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132836362477369593161086777 99627271858027194870815083)
        ·
          refine ⟨149440907787040792306222625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99627271858027194870815083 149440907787040792306222625)
          ·
            refine ⟨112080680840280594229666969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149440907787040792306222625 112080680840280594229666969)
            ·
              refine ⟨84060510630210445672250227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112080680840280594229666969 84060510630210445672250227)
              ·
                refine ⟨126090765945315668508375341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84060510630210445672250227 126090765945315668508375341)
                ·
                  refine ⟨47284037229493375690640753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126090765945315668508375341 47284037229493375690640753)
                  ·
                    refine ⟨35463027922120031767980565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47284037229493375690640753 35463027922120031767980565)
                    ·
                      refine ⟨1662329433849376489124089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35463027922120031767980565 1662329433849376489124089)
                      ·
                        rfl

theorem cell23_3237375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_3237375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237375 prefixEnd_3237375 := by exact prefixLift 3237375
  have htrace : WordTrace (prefixWord ++ tailWord_3237375) baseStart_3237375 baseEnd_3237375 := by
    simpa [prefixWord, tailWord_3237375, baseEnd_3237375] using wordTrace_append hprefix tailTrace_3237375
  have hstable : (prefixWord ++ tailWord_3237375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237375).length < 2 ^ (prefixWord ++ tailWord_3237375).sum := by decide
  have hdescent : baseEnd_3237375 < baseStart_3237375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237386 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 2, 2, 3]
def baseStart_3237386 : Nat := 118140960795 + 3237386 * 2 ^ 59
def prefixEnd_3237386 : Nat := 4983230072969 + 3 ^ 40 * 3237386 * 2
def baseEnd_3237386 : Nat := 1662335082136575946086539

theorem tailTrace_3237386 : CollatzResearch.WordTrace tailWord_3237386 prefixEnd_3237386 1662335082136575946086539 := by
  unfold tailWord_3237386
  simp only [CollatzResearch.WordTrace]
  refine ⟨29519291962377724588793003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78718111899673932236781341 29519291962377724588793003)
  ·
    refine ⟨44278937943566586883189505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29519291962377724588793003 44278937943566586883189505)
    ·
      refine ⟨33209203457674940162392129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44278937943566586883189505 33209203457674940162392129)
      ·
        refine ⟨24906902593256205121794097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33209203457674940162392129 24906902593256205121794097)
        ·
          refine ⟨18680176944942153841345573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24906902593256205121794097 18680176944942153841345573)
          ·
            refine ⟨3502533177176653845252295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18680176944942153841345573 3502533177176653845252295)
            ·
              refine ⟨5253799765764980767878443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3502533177176653845252295 5253799765764980767878443)
              ·
                refine ⟨7880699648647471151817665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5253799765764980767878443 7880699648647471151817665)
                ·
                  refine ⟨5910524736485603363863249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7880699648647471151817665 5910524736485603363863249)
                  ·
                    refine ⟨4432893552364202522897437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5910524736485603363863249 4432893552364202522897437)
                    ·
                      refine ⟨1662335082136575946086539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4432893552364202522897437 1662335082136575946086539)
                      ·
                        rfl

theorem cell23_3237386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_3237386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237386 prefixEnd_3237386 := by exact prefixLift 3237386
  have htrace : WordTrace (prefixWord ++ tailWord_3237386) baseStart_3237386 baseEnd_3237386 := by
    simpa [prefixWord, tailWord_3237386, baseEnd_3237386] using wordTrace_append hprefix tailTrace_3237386
  have hstable : (prefixWord ++ tailWord_3237386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237386).length < 2 ^ (prefixWord ++ tailWord_3237386).sum := by decide
  have hdescent : baseEnd_3237386 < baseStart_3237386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237436 : List Nat := [2, 2, 2, 2, 4, 1, 2, 2, 1, 5]
def baseStart_3237436 : Nat := 118140960795 + 3237436 * 2 ^ 59
def prefixEnd_3237436 : Nat := 4983230072969 + 3 ^ 40 * 3237436 * 2
def baseEnd_3237436 : Nat := 554120252056433583487103

theorem tailTrace_3237436 : CollatzResearch.WordTrace tailWord_3237436 prefixEnd_3237436 554120252056433583487103 := by
  unfold tailWord_3237436
  simp only [CollatzResearch.WordTrace]
  refine ⟨59039495749664878447246081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78719327666219837929661441 59039495749664878447246081)
  ·
    refine ⟨44279621812248658835434561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59039495749664878447246081 44279621812248658835434561)
    ·
      refine ⟨33209716359186494126575921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44279621812248658835434561 33209716359186494126575921)
      ·
        refine ⟨24907287269389870594931941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33209716359186494126575921 24907287269389870594931941)
        ·
          refine ⟨4670116363010600736549739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24907287269389870594931941 4670116363010600736549739)
          ·
            refine ⟨7005174544515901104824609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670116363010600736549739 7005174544515901104824609)
            ·
              refine ⟨5253880908386925828618457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7005174544515901104824609 5253880908386925828618457)
              ·
                refine ⟨3940410681290194371463843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5253880908386925828618457 3940410681290194371463843)
                ·
                  refine ⟨5910616021935291557195765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3940410681290194371463843 5910616021935291557195765)
                  ·
                    refine ⟨554120252056433583487103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5910616021935291557195765 554120252056433583487103)
                    ·
                      rfl

theorem cell23_3237436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_3237436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237436 prefixEnd_3237436 := by exact prefixLift 3237436
  have htrace : WordTrace (prefixWord ++ tailWord_3237436) baseStart_3237436 baseEnd_3237436 := by
    simpa [prefixWord, tailWord_3237436, baseEnd_3237436] using wordTrace_append hprefix tailTrace_3237436
  have hstable : (prefixWord ++ tailWord_3237436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237436).length < 2 ^ (prefixWord ++ tailWord_3237436).sum := by decide
  have hdescent : baseEnd_3237436 < baseStart_3237436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237439 : List Nat := [1, 1, 2, 2, 3, 3, 1, 4, 1, 1, 4]
def baseStart_3237439 : Nat := 118140960795 + 3237439 * 2 ^ 59
def prefixEnd_3237439 : Nat := 4983230072969 + 3 ^ 40 * 3237439 * 2
def baseEnd_3237439 : Nat := 1662362296611264238723795

theorem tailTrace_3237439 : CollatzResearch.WordTrace tailWord_3237439 prefixEnd_3237439 1662362296611264238723795 := by
  unfold tailWord_3237439
  simp only [CollatzResearch.WordTrace]
  refine ⟨118079100918318888406851371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78719400612212592271234247 118079100918318888406851371)
  ·
    refine ⟨177118651377478332610277057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118079100918318888406851371 177118651377478332610277057)
    ·
      refine ⟨132838988533108749457707793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177118651377478332610277057 132838988533108749457707793)
      ·
        refine ⟨99629241399831562093280845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132838988533108749457707793 99629241399831562093280845)
        ·
          refine ⟨37360965524936835784980317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99629241399831562093280845 37360965524936835784980317)
          ·
            refine ⟨14010362071851313419367619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37360965524936835784980317 14010362071851313419367619)
            ·
              refine ⟨21015543107776970129051429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14010362071851313419367619 21015543107776970129051429)
              ·
                refine ⟨3940414332708181899197143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21015543107776970129051429 3940414332708181899197143)
                ·
                  refine ⟨5910621499062272848795715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3940414332708181899197143 5910621499062272848795715)
                  ·
                    refine ⟨8865932248593409273193573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5910621499062272848795715 8865932248593409273193573)
                    ·
                      refine ⟨1662362296611264238723795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8865932248593409273193573 1662362296611264238723795)
                      ·
                        rfl

theorem cell23_3237439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_3237439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237439 prefixEnd_3237439 := by exact prefixLift 3237439
  have htrace : WordTrace (prefixWord ++ tailWord_3237439) baseStart_3237439 baseEnd_3237439 := by
    simpa [prefixWord, tailWord_3237439, baseEnd_3237439] using wordTrace_append hprefix tailTrace_3237439
  have hstable : (prefixWord ++ tailWord_3237439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237439).length < 2 ^ (prefixWord ++ tailWord_3237439).sum := by decide
  have hdescent : baseEnd_3237439 < baseStart_3237439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237493 : List Nat := [1, 3, 4, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3237493 : Nat := 118140960795 + 3237493 * 2 ^ 59
def prefixEnd_3237493 : Nat := 4983230072969 + 3 ^ 40 * 3237493 * 2
def baseEnd_3237493 : Nat := 1662390024566607027448547

theorem tailTrace_3237493 : CollatzResearch.WordTrace tailWord_3237493 prefixEnd_3237493 1662390024566607027448547 := by
  unfold tailWord_3237493
  simp only [CollatzResearch.WordTrace]
  refine ⟨118081070460123255629317133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78720713640082170419544755 118081070460123255629317133)
  ·
    refine ⟨44280401422546220860993925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118081070460123255629317133 44280401422546220860993925)
    ·
      refine ⟨8302575266727416411436361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44280401422546220860993925 8302575266727416411436361)
      ·
        refine ⟨6226931450045562308577271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8302575266727416411436361 6226931450045562308577271)
        ·
          refine ⟨9340397175068343462865907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6226931450045562308577271 9340397175068343462865907)
          ·
            refine ⟨14010595762602515194298861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9340397175068343462865907 14010595762602515194298861)
            ·
              refine ⟨5253973410975943197862073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14010595762602515194298861 5253973410975943197862073)
              ·
                refine ⟨3940480058231957398396555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5253973410975943197862073 3940480058231957398396555)
                ·
                  refine ⟨5910720087347936097594833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3940480058231957398396555 5910720087347936097594833)
                  ·
                    refine ⟨4433040065510952073196125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5910720087347936097594833 4433040065510952073196125)
                    ·
                      refine ⟨1662390024566607027448547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4433040065510952073196125 1662390024566607027448547)
                      ·
                        rfl

theorem cell23_3237493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3237493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237493 prefixEnd_3237493 := by exact prefixLift 3237493
  have htrace : WordTrace (prefixWord ++ tailWord_3237493) baseStart_3237493 baseEnd_3237493 := by
    simpa [prefixWord, tailWord_3237493, baseEnd_3237493] using wordTrace_append hprefix tailTrace_3237493
  have hstable : (prefixWord ++ tailWord_3237493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237493).length < 2 ^ (prefixWord ++ tailWord_3237493).sum := by decide
  have hdescent : baseEnd_3237493 < baseStart_3237493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237552 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 9]
def baseStart_3237552 : Nat := 118140960795 + 3237552 * 2 ^ 59
def prefixEnd_3237552 : Nat := 4983230072969 + 3 ^ 40 * 3237552 * 2
def baseEnd_3237552 : Nat := 184713368880580255178975

theorem tailTrace_3237552 : CollatzResearch.WordTrace tailWord_3237552 prefixEnd_3237552 184713368880580255178975 := by
  unfold tailWord_3237552
  simp only [CollatzResearch.WordTrace]
  refine ⟨59041611183454754352857455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78722148244606339137143273 59041611183454754352857455)
  ·
    refine ⟨88562416775182131529286183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59041611183454754352857455 88562416775182131529286183)
    ·
      refine ⟨132843625162773197293929275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88562416775182131529286183 132843625162773197293929275)
      ·
        refine ⟨199265437744159795940893913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132843625162773197293929275 199265437744159795940893913)
        ·
          refine ⟨149449078308119846955670435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199265437744159795940893913 149449078308119846955670435)
          ·
            refine ⟨224173617462179770433505653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149449078308119846955670435 224173617462179770433505653)
            ·
              refine ⟨21016276637079353478141155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224173617462179770433505653 21016276637079353478141155)
              ·
                refine ⟨31524414955619030217211733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21016276637079353478141155 31524414955619030217211733)
                ·
                  refine ⟨184713368880580255178975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31524414955619030217211733 184713368880580255178975)
                  ·
                    rfl

theorem cell23_3237552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 9].length) (baseStart_3237552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237552 prefixEnd_3237552 := by exact prefixLift 3237552
  have htrace : WordTrace (prefixWord ++ tailWord_3237552) baseStart_3237552 baseEnd_3237552 := by
    simpa [prefixWord, tailWord_3237552, baseEnd_3237552] using wordTrace_append hprefix tailTrace_3237552
  have hstable : (prefixWord ++ tailWord_3237552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237552).length < 2 ^ (prefixWord ++ tailWord_3237552).sum := by decide
  have hdescent : baseEnd_3237552 < baseStart_3237552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237574 : List Nat := [6, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3237574 : Nat := 118140960795 + 3237574 * 2 ^ 59
def prefixEnd_3237574 : Nat := 4983230072969 + 3 ^ 40 * 3237574 * 2
def baseEnd_3237574 : Nat := 1662431616499621210535675

theorem tailTrace_3237574 : CollatzResearch.WordTrace tailWord_3237574 prefixEnd_3237574 1662431616499621210535675 := by
  unfold tailWord_3237574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3690125774150931451969243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78722683181886537642010517 3690125774150931451969243)
  ·
    refine ⟨5535188661226397177953865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3690125774150931451969243 5535188661226397177953865)
    ·
      refine ⟨4151391495919797883465399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5535188661226397177953865 4151391495919797883465399)
      ·
        refine ⟨6227087243879696825198099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4151391495919797883465399 6227087243879696825198099)
        ·
          refine ⟨9340630865819545237797149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6227087243879696825198099 9340630865819545237797149)
          ·
            refine ⟨3502736574682329464173931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9340630865819545237797149 3502736574682329464173931)
            ·
              refine ⟨5254104862023494196260897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3502736574682329464173931 5254104862023494196260897)
              ·
                refine ⟨3940578646517620647195673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5254104862023494196260897 3940578646517620647195673)
                ·
                  refine ⟨2955433984888215485396755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3940578646517620647195673 2955433984888215485396755)
                  ·
                    refine ⟨4433150977332323228095133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2955433984888215485396755 4433150977332323228095133)
                    ·
                      refine ⟨1662431616499621210535675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4433150977332323228095133 1662431616499621210535675)
                      ·
                        rfl

theorem cell23_3237574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3237574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237574 prefixEnd_3237574 := by exact prefixLift 3237574
  have htrace : WordTrace (prefixWord ++ tailWord_3237574) baseStart_3237574 baseEnd_3237574 := by
    simpa [prefixWord, tailWord_3237574, baseEnd_3237574] using wordTrace_append hprefix tailTrace_3237574
  have hstable : (prefixWord ++ tailWord_3237574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237574).length < 2 ^ (prefixWord ++ tailWord_3237574).sum := by decide
  have hdescent : baseEnd_3237574 < baseStart_3237574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237580 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 4, 2, 2]
def baseStart_3237580 : Nat := 118140960795 + 3237580 * 2 ^ 59
def prefixEnd_3237580 : Nat := 4983230072969 + 3 ^ 40 * 3237580 * 2
def baseEnd_3237580 : Nat := 1662434697383548187060647

theorem tailTrace_3237580 : CollatzResearch.WordTrace tailWord_3237580 prefixEnd_3237580 1662434697383548187060647 := by
  unfold tailWord_3237580
  simp only [CollatzResearch.WordTrace]
  refine ⟨59042121805404034743867097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78722829073872046325156129 59042121805404034743867097)
  ·
    refine ⟨44281591354053026057900323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59042121805404034743867097 44281591354053026057900323)
    ·
      refine ⟨66422387031079539086850485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44281591354053026057900323 66422387031079539086850485)
      ·
        refine ⟨6227098784163706789392233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66422387031079539086850485 6227098784163706789392233)
        ·
          refine ⟨4670324088122780092044175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6227098784163706789392233 4670324088122780092044175)
          ·
            refine ⟨7005486132184170138066263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670324088122780092044175 7005486132184170138066263)
            ·
              refine ⟨10508229198276255207099395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005486132184170138066263 10508229198276255207099395)
              ·
                refine ⟨15762343797414382810649093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10508229198276255207099395 15762343797414382810649093)
                ·
                  refine ⟨2955439462015196776996705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15762343797414382810649093 2955439462015196776996705)
                  ·
                    refine ⟨2216579596511397582747529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2955439462015196776996705 2216579596511397582747529)
                    ·
                      refine ⟨1662434697383548187060647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2216579596511397582747529 1662434697383548187060647)
                      ·
                        rfl

theorem cell23_3237580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_3237580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237580 prefixEnd_3237580 := by exact prefixLift 3237580
  have htrace : WordTrace (prefixWord ++ tailWord_3237580) baseStart_3237580 baseEnd_3237580 := by
    simpa [prefixWord, tailWord_3237580, baseEnd_3237580] using wordTrace_append hprefix tailTrace_3237580
  have hstable : (prefixWord ++ tailWord_3237580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237580).length < 2 ^ (prefixWord ++ tailWord_3237580).sum := by decide
  have hdescent : baseEnd_3237580 < baseStart_3237580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237586 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 7]
def baseStart_3237586 : Nat := 118140960795 + 3237586 * 2 ^ 59
def prefixEnd_3237586 : Nat := 4983230072969 + 3 ^ 40 * 3237586 * 2
def baseEnd_3237586 : Nat := 184715308696386129287291

theorem tailTrace_3237586 : CollatzResearch.WordTrace tailWord_3237586 prefixEnd_3237586 184715308696386129287291 := by
  unfold tailWord_3237586
  simp only [CollatzResearch.WordTrace]
  refine ⟨29521115612196583128113153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78722974965857555008301741 29521115612196583128113153)
  ·
    refine ⟨22140836709147437346084865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29521115612196583128113153 22140836709147437346084865)
    ·
      refine ⟨16605627531860578009563649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22140836709147437346084865 16605627531860578009563649)
      ·
        refine ⟨12454220648895433507172737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16605627531860578009563649 12454220648895433507172737)
        ·
          refine ⟨9340665486671575130379553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12454220648895433507172737 9340665486671575130379553)
          ·
            refine ⟨7005499115003681347784665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9340665486671575130379553 7005499115003681347784665)
            ·
              refine ⟨5254124336252761010838499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7005499115003681347784665 5254124336252761010838499)
              ·
                refine ⟨7881186504379141516257749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5254124336252761010838499 7881186504379141516257749)
                ·
                  refine ⟨184715308696386129287291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7881186504379141516257749 184715308696386129287291)
                  ·
                    rfl

theorem cell23_3237586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_3237586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237586 prefixEnd_3237586 := by exact prefixLift 3237586
  have htrace : WordTrace (prefixWord ++ tailWord_3237586) baseStart_3237586 baseEnd_3237586 := by
    simpa [prefixWord, tailWord_3237586, baseEnd_3237586] using wordTrace_append hprefix tailTrace_3237586
  have hstable : (prefixWord ++ tailWord_3237586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237586).length < 2 ^ (prefixWord ++ tailWord_3237586).sum := by decide
  have hdescent : baseEnd_3237586 < baseStart_3237586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237597 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_3237597 : Nat := 118140960795 + 3237597 * 2 ^ 59
def prefixEnd_3237597 : Nat := 4983230072969 + 3 ^ 40 * 3237597 * 2
def baseEnd_3237597 : Nat := 1662443426554674620548069

theorem tailTrace_3237597 : CollatzResearch.WordTrace tailWord_3237597 prefixEnd_3237597 1662443426554674620548069 := by
  unfold tailWord_3237597
  simp only [CollatzResearch.WordTrace]
  refine ⟨118084863651746481391103045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78723242434497654260735363 118084863651746481391103045)
  ·
    refine ⟨22140911934702465260831821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118084863651746481391103045 22140911934702465260831821)
    ·
      refine ⟨8302841975513424472811933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22140911934702465260831821 8302841975513424472811933)
      ·
        refine ⟨3113565740817534177304475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8302841975513424472811933 3113565740817534177304475)
        ·
          refine ⟨4670348611226301265956713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113565740817534177304475 4670348611226301265956713)
          ·
            refine ⟨3502761458419725949467535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4670348611226301265956713 3502761458419725949467535)
            ·
              refine ⟨5254142187629588924201303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3502761458419725949467535 5254142187629588924201303)
              ·
                refine ⟨7881213281444383386301955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5254142187629588924201303 7881213281444383386301955)
                ·
                  refine ⟨11821819922166575079452933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7881213281444383386301955 11821819922166575079452933)
                  ·
                    refine ⟨2216591235406232827397425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11821819922166575079452933 2216591235406232827397425)
                    ·
                      refine ⟨1662443426554674620548069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2216591235406232827397425 1662443426554674620548069)
                      ·
                        rfl

theorem cell23_3237597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_3237597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237597 prefixEnd_3237597 := by exact prefixLift 3237597
  have htrace : WordTrace (prefixWord ++ tailWord_3237597) baseStart_3237597 baseEnd_3237597 := by
    simpa [prefixWord, tailWord_3237597, baseEnd_3237597] using wordTrace_append hprefix tailTrace_3237597
  have hstable : (prefixWord ++ tailWord_3237597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237597).length < 2 ^ (prefixWord ++ tailWord_3237597).sum := by decide
  have hdescent : baseEnd_3237597 < baseStart_3237597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237619 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 4]
def baseStart_3237619 : Nat := 118140960795 + 3237619 * 2 ^ 59
def prefixEnd_3237619 : Nat := 4983230072969 + 3 ^ 40 * 3237619 * 2
def baseEnd_3237619 : Nat := 1662454723129073534472967

theorem tailTrace_3237619 : CollatzResearch.WordTrace tailWord_3237619 prefixEnd_3237619 1662454723129073534472967 := by
  unfold tailWord_3237619
  simp only [CollatzResearch.WordTrace]
  refine ⟨118085666057666779148403911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78723777371777852765602607 118085666057666779148403911)
  ·
    refine ⟨177128499086500168722605867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118085666057666779148403911 177128499086500168722605867)
    ·
      refine ⟨265692748629750253083908801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177128499086500168722605867 265692748629750253083908801)
      ·
        refine ⟨199269561472312689812931601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265692748629750253083908801 199269561472312689812931601)
        ·
          refine ⟨149452171104234517359698701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199269561472312689812931601 149452171104234517359698701)
          ·
            refine ⟨56044564164087944009887013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149452171104234517359698701 56044564164087944009887013)
            ·
              refine ⟨10508355780766489501853815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56044564164087944009887013 10508355780766489501853815)
              ·
                refine ⟨15762533671149734252780723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10508355780766489501853815 15762533671149734252780723)
                ·
                  refine ⟨23643800506724601379171085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15762533671149734252780723 23643800506724601379171085)
                  ·
                    refine ⟨8866425190021725517189157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23643800506724601379171085 8866425190021725517189157)
                    ·
                      refine ⟨1662454723129073534472967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8866425190021725517189157 1662454723129073534472967)
                      ·
                        rfl

theorem cell23_3237619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_3237619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237619 prefixEnd_3237619 := by exact prefixLift 3237619
  have htrace : WordTrace (prefixWord ++ tailWord_3237619) baseStart_3237619 baseEnd_3237619 := by
    simpa [prefixWord, tailWord_3237619, baseEnd_3237619] using wordTrace_append hprefix tailTrace_3237619
  have hstable : (prefixWord ++ tailWord_3237619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237619).length < 2 ^ (prefixWord ++ tailWord_3237619).sum := by decide
  have hdescent : baseEnd_3237619 < baseStart_3237619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237636 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3237636 : Nat := 118140960795 + 3237636 * 2 ^ 59
def prefixEnd_3237636 : Nat := 4983230072969 + 3 ^ 40 * 3237636 * 2
def baseEnd_3237636 : Nat := 1662463452300199967960389

theorem tailTrace_3237636 : CollatzResearch.WordTrace tailWord_3237636 prefixEnd_3237636 1662463452300199967960389 := by
  unfold tailWord_3237636
  simp only [CollatzResearch.WordTrace]
  refine ⟨59043143049302595525886381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78724190732403460701181841 59043143049302595525886381)
  ·
    refine ⟨22141178643488473322207393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59043143049302595525886381 22141178643488473322207393)
    ·
      refine ⟨16605883982616354991655545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22141178643488473322207393 16605883982616354991655545)
      ·
        refine ⟨12454412986962266243741659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16605883982616354991655545 12454412986962266243741659)
        ·
          refine ⟨18681619480443399365612489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12454412986962266243741659 18681619480443399365612489)
          ·
            refine ⟨14011214610332549524209367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18681619480443399365612489 14011214610332549524209367)
            ·
              refine ⟨21016821915498824286314051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14011214610332549524209367 21016821915498824286314051)
              ·
                refine ⟨31525232873248236429471077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21016821915498824286314051 31525232873248236429471077)
                ·
                  refine ⟨5910981163734044330525827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31525232873248236429471077 5910981163734044330525827)
                  ·
                    refine ⟨8866471745601066495788741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5910981163734044330525827 8866471745601066495788741)
                    ·
                      refine ⟨1662463452300199967960389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8866471745601066495788741 1662463452300199967960389)
                      ·
                        rfl

theorem cell23_3237636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3237636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237636 prefixEnd_3237636 := by exact prefixLift 3237636
  have htrace : WordTrace (prefixWord ++ tailWord_3237636) baseStart_3237636 baseEnd_3237636 := by
    simpa [prefixWord, tailWord_3237636, baseEnd_3237636] using wordTrace_append hprefix tailTrace_3237636
  have hstable : (prefixWord ++ tailWord_3237636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237636).length < 2 ^ (prefixWord ++ tailWord_3237636).sum := by decide
  have hdescent : baseEnd_3237636 < baseStart_3237636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237659 : List Nat := [1, 1, 1, 1, 1, 1, 4, 7, 6]
def baseStart_3237659 : Nat := 118140960795 + 3237659 * 2 ^ 59
def prefixEnd_3237659 : Nat := 4983230072969 + 3 ^ 40 * 3237659 * 2
def baseEnd_3237659 : Nat := 184719473595028153108087

theorem tailTrace_3237659 : CollatzResearch.WordTrace tailWord_3237659 prefixEnd_3237659 184719473595028153108087 := by
  unfold tailWord_3237659
  simp only [CollatzResearch.WordTrace]
  refine ⟨118087124977521865979860031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78724749985014577319906687 118087124977521865979860031)
  ·
    refine ⟨177130687466282798969790047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118087124977521865979860031 177130687466282798969790047)
    ·
      refine ⟨265696031199424198454685071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177130687466282798969790047 265696031199424198454685071)
      ·
        refine ⟨398544046799136297682027607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265696031199424198454685071 398544046799136297682027607)
        ·
          refine ⟨597816070198704446523041411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398544046799136297682027607 597816070198704446523041411)
          ·
            refine ⟨896724105298056669784562117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597816070198704446523041411 896724105298056669784562117)
            ·
              refine ⟨168135769743385625584605397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 896724105298056669784562117 168135769743385625584605397)
              ·
                refine ⟨3940682103360600599639189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 168135769743385625584605397 3940682103360600599639189)
                ·
                  refine ⟨184719473595028153108087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3940682103360600599639189 184719473595028153108087)
                  ·
                    rfl

theorem cell23_3237659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 6].length) (baseStart_3237659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237659 prefixEnd_3237659 := by exact prefixLift 3237659
  have htrace : WordTrace (prefixWord ++ tailWord_3237659) baseStart_3237659 baseEnd_3237659 := by
    simpa [prefixWord, tailWord_3237659, baseEnd_3237659] using wordTrace_append hprefix tailTrace_3237659
  have hstable : (prefixWord ++ tailWord_3237659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237659).length < 2 ^ (prefixWord ++ tailWord_3237659).sum := by decide
  have hdescent : baseEnd_3237659 < baseStart_3237659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237693 : List Nat := [1, 4, 1, 4, 1, 2, 2, 2, 6]
def baseStart_3237693 : Nat := 118140960795 + 3237693 * 2 ^ 59
def prefixEnd_3237693 : Nat := 4983230072969 + 3 ^ 40 * 3237693 * 2
def baseEnd_3237693 : Nat := 184721413410834027216403

theorem tailTrace_3237693 : CollatzResearch.WordTrace tailWord_3237693 prefixEnd_3237693 184721413410834027216403 := by
  unfold tailWord_3237693
  simp only [CollatzResearch.WordTrace]
  refine ⟨118088365059398689786597733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78725576706265793191065155 118088365059398689786597733)
  ·
    refine ⟨22141568448637254334987075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118088365059398689786597733 22141568448637254334987075)
    ·
      refine ⟨33212352672955881502480613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22141568448637254334987075 33212352672955881502480613)
      ·
        refine ⟨6227316126179227781715115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33212352672955881502480613 6227316126179227781715115)
        ·
          refine ⟨9340974189268841672572673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6227316126179227781715115 9340974189268841672572673)
          ·
            refine ⟨7005730641951631254429505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9340974189268841672572673 7005730641951631254429505)
            ·
              refine ⟨5254297981463723440822129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7005730641951631254429505 5254297981463723440822129)
              ·
                refine ⟨3940723486097792580616597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5254297981463723440822129 3940723486097792580616597)
                ·
                  refine ⟨184721413410834027216403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3940723486097792580616597 184721413410834027216403)
                  ·
                    rfl

theorem cell23_3237693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_3237693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237693 prefixEnd_3237693 := by exact prefixLift 3237693
  have htrace : WordTrace (prefixWord ++ tailWord_3237693) baseStart_3237693 baseEnd_3237693 := by
    simpa [prefixWord, tailWord_3237693, baseEnd_3237693] using wordTrace_append hprefix tailTrace_3237693
  have hstable : (prefixWord ++ tailWord_3237693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237693).length < 2 ^ (prefixWord ++ tailWord_3237693).sum := by decide
  have hdescent : baseEnd_3237693 < baseStart_3237693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237696 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 5, 5, 2]
def baseStart_3237696 : Nat := 118140960795 + 3237696 * 2 ^ 59
def prefixEnd_3237696 : Nat := 4983230072969 + 3 ^ 40 * 3237696 * 2
def baseEnd_3237696 : Nat := 1662494261139469733210113

theorem tailTrace_3237696 : CollatzResearch.WordTrace tailWord_3237696 prefixEnd_3237696 1662494261139469733210113 := by
  unfold tailWord_3237696
  simp only [CollatzResearch.WordTrace]
  refine ⟨59044237239193910649478471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78725649652258547532637961 59044237239193910649478471)
  ·
    refine ⟨88566355858790865974217707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59044237239193910649478471 88566355858790865974217707)
    ·
      refine ⟨132849533788186298961326561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88566355858790865974217707 132849533788186298961326561)
      ·
        refine ⟨99637150341139724220994921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132849533788186298961326561 99637150341139724220994921)
        ·
          refine ⟨74727862755854793165746191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99637150341139724220994921 74727862755854793165746191)
          ·
            refine ⟨112091794133782189748619287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74727862755854793165746191 112091794133782189748619287)
            ·
              refine ⟨168137691200673284622928931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112091794133782189748619287 168137691200673284622928931)
              ·
                refine ⟨252206536801009926934393397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168137691200673284622928931 252206536801009926934393397)
                ·
                  refine ⟨23644362825094680650099381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252206536801009926934393397 23644362825094680650099381)
                  ·
                    refine ⟨2216659014852626310946817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23644362825094680650099381 2216659014852626310946817)
                    ·
                      refine ⟨1662494261139469733210113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2216659014852626310946817 1662494261139469733210113)
                      ·
                        rfl

theorem cell23_3237696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 5, 2].length) (baseStart_3237696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237696 prefixEnd_3237696 := by exact prefixLift 3237696
  have htrace : WordTrace (prefixWord ++ tailWord_3237696) baseStart_3237696 baseEnd_3237696 := by
    simpa [prefixWord, tailWord_3237696, baseEnd_3237696] using wordTrace_append hprefix tailTrace_3237696
  have hstable : (prefixWord ++ tailWord_3237696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237696).length < 2 ^ (prefixWord ++ tailWord_3237696).sum := by decide
  have hdescent : baseEnd_3237696 < baseStart_3237696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237730 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_3237730 : Nat := 118140960795 + 3237730 * 2 ^ 59
def prefixEnd_3237730 : Nat := 4983230072969 + 3 ^ 40 * 3237730 * 2
def baseEnd_3237730 : Nat := 1662511719481722600184957

theorem tailTrace_3237730 : CollatzResearch.WordTrace tailWord_3237730 prefixEnd_3237730 1662511719481722600184957 := by
  unfold tailWord_3237730
  simp only [CollatzResearch.WordTrace]
  refine ⟨29522428640066161276423661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78726476373509763403796429 29522428640066161276423661)
  ·
    refine ⟨11070910740024810478658873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29522428640066161276423661 11070910740024810478658873)
    ·
      refine ⟨8303183055018607858994155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11070910740024810478658873 8303183055018607858994155)
      ·
        refine ⟨12454774582527911788491233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8303183055018607858994155 12454774582527911788491233)
        ·
          refine ⟨9341080936895933841368425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12454774582527911788491233 9341080936895933841368425)
          ·
            refine ⟨7005810702671950381026319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9341080936895933841368425 7005810702671950381026319)
            ·
              refine ⟨10508716054007925571539479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005810702671950381026319 10508716054007925571539479)
              ·
                refine ⟨15763074081011888357309219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10508716054007925571539479 15763074081011888357309219)
                ·
                  refine ⟨23644611121517832535963829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15763074081011888357309219 23644611121517832535963829)
                  ·
                    refine ⟨2216682292642296800246609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23644611121517832535963829 2216682292642296800246609)
                    ·
                      refine ⟨1662511719481722600184957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2216682292642296800246609 1662511719481722600184957)
                      ·
                        rfl

theorem cell23_3237730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_3237730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237730 prefixEnd_3237730 := by exact prefixLift 3237730
  have htrace : WordTrace (prefixWord ++ tailWord_3237730) baseStart_3237730 baseEnd_3237730 := by
    simpa [prefixWord, tailWord_3237730, baseEnd_3237730] using wordTrace_append hprefix tailTrace_3237730
  have hstable : (prefixWord ++ tailWord_3237730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237730).length < 2 ^ (prefixWord ++ tailWord_3237730).sum := by decide
  have hdescent : baseEnd_3237730 < baseStart_3237730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237736 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 1, 6]
def baseStart_3237736 : Nat := 118140960795 + 3237736 * 2 ^ 59
def prefixEnd_3237736 : Nat := 4983230072969 + 3 ^ 40 * 3237736 * 2
def baseEnd_3237736 : Nat := 554171600121883192236643

theorem tailTrace_3237736 : CollatzResearch.WordTrace tailWord_3237736 prefixEnd_3237736 554171600121883192236643 := by
  unfold tailWord_3237736
  simp only [CollatzResearch.WordTrace]
  refine ⟨59044966699121454065206531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78726622265495272086942041 59044966699121454065206531)
  ·
    refine ⟨88567450048682181097809797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59044966699121454065206531 88567450048682181097809797)
    ·
      refine ⟨16606396884127908955839337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88567450048682181097809797 16606396884127908955839337)
      ·
        refine ⟨12454797663095931716879503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16606396884127908955839337 12454797663095931716879503)
        ·
          refine ⟨18682196494643897575319255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12454797663095931716879503 18682196494643897575319255)
          ·
            refine ⟨28023294741965846362978883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18682196494643897575319255 28023294741965846362978883)
            ·
              refine ⟨42034942112948769544468325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28023294741965846362978883 42034942112948769544468325)
              ·
                refine ⟨7881551646177894289587811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42034942112948769544468325 7881551646177894289587811)
                ·
                  refine ⟨11822327469266841434381717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7881551646177894289587811 11822327469266841434381717)
                  ·
                    refine ⟨554171600121883192236643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11822327469266841434381717 554171600121883192236643)
                    ·
                      rfl

theorem cell23_3237736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_3237736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237736 prefixEnd_3237736 := by exact prefixLift 3237736
  have htrace : WordTrace (prefixWord ++ tailWord_3237736) baseStart_3237736 baseEnd_3237736 := by
    simpa [prefixWord, tailWord_3237736, baseEnd_3237736] using wordTrace_append hprefix tailTrace_3237736
  have hstable : (prefixWord ++ tailWord_3237736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237736).length < 2 ^ (prefixWord ++ tailWord_3237736).sum := by decide
  have hdescent : baseEnd_3237736 < baseStart_3237736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237739 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 6]
def baseStart_3237739 : Nat := 118140960795 + 3237739 * 2 ^ 59
def prefixEnd_3237739 : Nat := 4983230072969 + 3 ^ 40 * 3237739 * 2
def baseEnd_3237739 : Nat := 1662516340807613064972415

theorem tailTrace_3237739 : CollatzResearch.WordTrace tailWord_3237739 prefixEnd_3237739 1662516340807613064972415 := by
  unfold tailWord_3237739
  simp only [CollatzResearch.WordTrace]
  refine ⟨118090042817232039642772271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78726695211488026428514847 118090042817232039642772271)
  ·
    refine ⟨177135064225848059464158407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118090042817232039642772271 177135064225848059464158407)
    ·
      refine ⟨265702596338772089196237611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177135064225848059464158407 265702596338772089196237611)
      ·
        refine ⟨398553894508158133794356417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265702596338772089196237611 398553894508158133794356417)
        ·
          refine ⟨298915420881118600345767313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398553894508158133794356417 298915420881118600345767313)
          ·
            refine ⟨224186565660838950259325485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298915420881118600345767313 224186565660838950259325485)
            ·
              refine ⟨84069962122814606347247057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224186565660838950259325485 84069962122814606347247057)
              ·
                refine ⟨63052471592110954760435293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84069962122814606347247057 63052471592110954760435293)
                ·
                  refine ⟨23644676847041608035163235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63052471592110954760435293 23644676847041608035163235)
                  ·
                    refine ⟨35467015270562412052744853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23644676847041608035163235 35467015270562412052744853)
                    ·
                      refine ⟨1662516340807613064972415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35467015270562412052744853 1662516340807613064972415)
                      ·
                        rfl

theorem cell23_3237739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 6].length) (baseStart_3237739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237739 prefixEnd_3237739 := by exact prefixLift 3237739
  have htrace : WordTrace (prefixWord ++ tailWord_3237739) baseStart_3237739 baseEnd_3237739 := by
    simpa [prefixWord, tailWord_3237739, baseEnd_3237739] using wordTrace_append hprefix tailTrace_3237739
  have hstable : (prefixWord ++ tailWord_3237739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237739).length < 2 ^ (prefixWord ++ tailWord_3237739).sum := by decide
  have hdescent : baseEnd_3237739 < baseStart_3237739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237740 : List Nat := [2, 2, 1, 1, 4, 4, 2, 1, 1, 5]
def baseStart_3237740 : Nat := 118140960795 + 3237740 * 2 ^ 59
def prefixEnd_3237740 : Nat := 4983230072969 + 3 ^ 40 * 3237740 * 2
def baseEnd_3237740 : Nat := 554172284762755853686637

theorem tailTrace_3237740 : CollatzResearch.WordTrace tailWord_3237740 prefixEnd_3237740 554172284762755853686637 := by
  unfold tailWord_3237740
  simp only [CollatzResearch.WordTrace]
  refine ⟨59045039645114208406779337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78726719526818944542372449 59045039645114208406779337)
  ·
    refine ⟨44283779733835656305084503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59045039645114208406779337 44283779733835656305084503)
    ·
      refine ⟨66425669600753484457626755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44283779733835656305084503 66425669600753484457626755)
      ·
        refine ⟨99638504401130226686440133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66425669600753484457626755 99638504401130226686440133)
        ·
          refine ⟨18682219575211917503707525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99638504401130226686440133 18682219575211917503707525)
          ·
            refine ⟨3502916170352234531945161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18682219575211917503707525 3502916170352234531945161)
            ·
              refine ⟨2627187127764175898958871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3502916170352234531945161 2627187127764175898958871)
              ·
                refine ⟨3940780691646263848438307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627187127764175898958871 3940780691646263848438307)
                ·
                  refine ⟨5911171037469395772657461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3940780691646263848438307 5911171037469395772657461)
                  ·
                    refine ⟨554172284762755853686637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5911171037469395772657461 554172284762755853686637)
                    ·
                      rfl

theorem cell23_3237740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_3237740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237740 prefixEnd_3237740 := by exact prefixLift 3237740
  have htrace : WordTrace (prefixWord ++ tailWord_3237740) baseStart_3237740 baseEnd_3237740 := by
    simpa [prefixWord, tailWord_3237740, baseEnd_3237740] using wordTrace_append hprefix tailTrace_3237740
  have hstable : (prefixWord ++ tailWord_3237740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237740).length < 2 ^ (prefixWord ++ tailWord_3237740).sum := by decide
  have hdescent : baseEnd_3237740 < baseStart_3237740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237746 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_3237746 : Nat := 118140960795 + 3237746 * 2 ^ 59
def prefixEnd_3237746 : Nat := 4983230072969 + 3 ^ 40 * 3237746 * 2
def baseEnd_3237746 : Nat := 1662519935172194537584883

theorem tailTrace_3237746 : CollatzResearch.WordTrace tailWord_3237746 prefixEnd_3237746 1662519935172194537584883 := by
  unfold tailWord_3237746
  simp only [CollatzResearch.WordTrace]
  refine ⟨29522574532051669959569273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78726865418804453225518061 29522574532051669959569273)
  ·
    refine ⟨22141930899038752469676955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29522574532051669959569273 22141930899038752469676955)
    ·
      refine ⟨33212896348558128704515433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22141930899038752469676955 33212896348558128704515433)
      ·
        refine ⟨24909672261418596528386575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33212896348558128704515433 24909672261418596528386575)
        ·
          refine ⟨37364508392127894792579863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24909672261418596528386575 37364508392127894792579863)
          ·
            refine ⟨56046762588191842188869795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37364508392127894792579863 56046762588191842188869795)
            ·
              refine ⟨84070143882287763283304693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56046762588191842188869795 84070143882287763283304693)
              ·
                refine ⟨7881575988964477807809815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84070143882287763283304693 7881575988964477807809815)
                ·
                  refine ⟨11822363983446716711714723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7881575988964477807809815 11822363983446716711714723)
                  ·
                    refine ⟨17733545975170075067572085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11822363983446716711714723 17733545975170075067572085)
                    ·
                      refine ⟨1662519935172194537584883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17733545975170075067572085 1662519935172194537584883)
                      ·
                        rfl

theorem cell23_3237746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_3237746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237746 prefixEnd_3237746 := by exact prefixLift 3237746
  have htrace : WordTrace (prefixWord ++ tailWord_3237746) baseStart_3237746 baseEnd_3237746 := by
    simpa [prefixWord, tailWord_3237746, baseEnd_3237746] using wordTrace_append hprefix tailTrace_3237746
  have hstable : (prefixWord ++ tailWord_3237746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237746).length < 2 ^ (prefixWord ++ tailWord_3237746).sum := by decide
  have hdescent : baseEnd_3237746 < baseStart_3237746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237759 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 7]
def baseStart_3237759 : Nat := 118140960795 + 3237759 * 2 ^ 59
def prefixEnd_3237759 : Nat := 4983230072969 + 3 ^ 40 * 3237759 * 2
def baseEnd_3237759 : Nat := 1662526610420702986722323

theorem tailTrace_3237759 : CollatzResearch.WordTrace tailWord_3237759 prefixEnd_3237759 1662526610420702986722323 := by
  unfold tailWord_3237759
  simp only [CollatzResearch.WordTrace]
  refine ⟨118090772277159583058500331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78727181518106388705666887 118090772277159583058500331)
  ·
    refine ⟨177136158415739374587750497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118090772277159583058500331 177136158415739374587750497)
    ·
      refine ⟨132852118811804530940812873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177136158415739374587750497 132852118811804530940812873)
      ·
        refine ⟨99639089108853398205609655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132852118811804530940812873 99639089108853398205609655)
        ·
          refine ⟨149458633663280097308414483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99639089108853398205609655 149458633663280097308414483)
          ·
            refine ⟨224187950494920145962621725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149458633663280097308414483 224187950494920145962621725)
            ·
              refine ⟨84070481435595054735983147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224187950494920145962621725 84070481435595054735983147)
              ·
                refine ⟨126105722153392582103974721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84070481435595054735983147 126105722153392582103974721)
                ·
                  refine ⟨94579291615044436577981041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126105722153392582103974721 94579291615044436577981041)
                  ·
                    refine ⟨70934468711283327433485781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94579291615044436577981041 70934468711283327433485781)
                    ·
                      refine ⟨1662526610420702986722323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70934468711283327433485781 1662526610420702986722323)
                      ·
                        rfl

theorem cell23_3237759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_3237759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237759 prefixEnd_3237759 := by exact prefixLift 3237759
  have htrace : WordTrace (prefixWord ++ tailWord_3237759) baseStart_3237759 baseEnd_3237759 := by
    simpa [prefixWord, tailWord_3237759, baseEnd_3237759] using wordTrace_append hprefix tailTrace_3237759
  have hstable : (prefixWord ++ tailWord_3237759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237759).length < 2 ^ (prefixWord ++ tailWord_3237759).sum := by decide
  have hdescent : baseEnd_3237759 < baseStart_3237759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237760 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 3, 2, 2]
def baseStart_3237760 : Nat := 118140960795 + 3237760 * 2 ^ 59
def prefixEnd_3237760 : Nat := 4983230072969 + 3 ^ 40 * 3237760 * 2
def baseEnd_3237760 : Nat := 1662527123901357482809819

theorem tailTrace_3237760 : CollatzResearch.WordTrace tailWord_3237760 prefixEnd_3237760 1662527123901357482809819 := by
  unfold tailWord_3237760
  simp only [CollatzResearch.WordTrace]
  refine ⟨59045404375077980114643367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78727205833437306819524489 59045404375077980114643367)
  ·
    refine ⟨88568106562616970171965051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59045404375077980114643367 88568106562616970171965051)
    ·
      refine ⟨132852159843925455257947577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88568106562616970171965051 132852159843925455257947577)
      ·
        refine ⟨99639119882944091443460683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132852159843925455257947577 99639119882944091443460683)
        ·
          refine ⟨149458679824416137165191025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99639119882944091443460683 149458679824416137165191025)
          ·
            refine ⟨112094009868312102873893269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149458679824416137165191025 112094009868312102873893269)
            ·
              refine ⟨5254406712577129822213747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112094009868312102873893269 5254406712577129822213747)
              ·
                refine ⟨7881610068865694733320621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5254406712577129822213747 7881610068865694733320621)
                ·
                  refine ⟨2955603775824635524995233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7881610068865694733320621 2955603775824635524995233)
                  ·
                    refine ⟨2216702831868476643746425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2955603775824635524995233 2216702831868476643746425)
                    ·
                      refine ⟨1662527123901357482809819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2216702831868476643746425 1662527123901357482809819)
                      ·
                        rfl

theorem cell23_3237760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 3, 2, 2].length) (baseStart_3237760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237760 prefixEnd_3237760 := by exact prefixLift 3237760
  have htrace : WordTrace (prefixWord ++ tailWord_3237760) baseStart_3237760 baseEnd_3237760 := by
    simpa [prefixWord, tailWord_3237760, baseEnd_3237760] using wordTrace_append hprefix tailTrace_3237760
  have hstable : (prefixWord ++ tailWord_3237760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237760).length < 2 ^ (prefixWord ++ tailWord_3237760).sum := by decide
  have hdescent : baseEnd_3237760 < baseStart_3237760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237770 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 1, 6]
def baseStart_3237770 : Nat := 118140960795 + 3237770 * 2 ^ 59
def prefixEnd_3237770 : Nat := 4983230072969 + 3 ^ 40 * 3237770 * 2
def baseEnd_3237770 : Nat := 554177419569300814561591

theorem tailTrace_3237770 : CollatzResearch.WordTrace tailWord_3237770 prefixEnd_3237770 554177419569300814561591 := by
  unfold tailWord_3237770
  simp only [CollatzResearch.WordTrace]
  refine ⟨29522793370029932984287691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78727448986746487958100509 29522793370029932984287691)
  ·
    refine ⟨44284190055044899476431537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29522793370029932984287691 44284190055044899476431537)
    ·
      refine ⟨33213142541283674607323653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44284190055044899476431537 33213142541283674607323653)
      ·
        refine ⟨6227464226490688988873185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33213142541283674607323653 6227464226490688988873185)
        ·
          refine ⟨4670598169868016741654889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6227464226490688988873185 4670598169868016741654889)
          ·
            refine ⟨3502948627401012556241167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4670598169868016741654889 3502948627401012556241167)
            ·
              refine ⟨5254422941101518834361751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3502948627401012556241167 5254422941101518834361751)
              ·
                refine ⟨7881634411652278251542627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5254422941101518834361751 7881634411652278251542627)
                ·
                  refine ⟨11822451617478417377313941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7881634411652278251542627 11822451617478417377313941)
                  ·
                    refine ⟨554177419569300814561591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11822451617478417377313941 554177419569300814561591)
                    ·
                      rfl

theorem cell23_3237770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_3237770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237770 prefixEnd_3237770 := by exact prefixLift 3237770
  have htrace : WordTrace (prefixWord ++ tailWord_3237770) baseStart_3237770 baseEnd_3237770 := by
    simpa [prefixWord, tailWord_3237770, baseEnd_3237770] using wordTrace_append hprefix tailTrace_3237770
  have hstable : (prefixWord ++ tailWord_3237770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237770).length < 2 ^ (prefixWord ++ tailWord_3237770).sum := by decide
  have hdescent : baseEnd_3237770 < baseStart_3237770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237779 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 3, 9]
def baseStart_3237779 : Nat := 118140960795 + 3237779 * 2 ^ 59
def prefixEnd_3237779 : Nat := 4983230072969 + 3 ^ 40 * 3237779 * 2
def baseEnd_3237779 : Nat := 554178960011264302824077

theorem tailTrace_3237779 : CollatzResearch.WordTrace tailWord_3237779 prefixEnd_3237779 554178960011264302824077 := by
  unfold tailWord_3237779
  simp only [CollatzResearch.WordTrace]
  refine ⟨118091501737087126474228391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78727667824724750982818927 118091501737087126474228391)
  ·
    refine ⟨177137252605630689711342587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118091501737087126474228391 177137252605630689711342587)
    ·
      refine ⟨265705878908446034567013881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177137252605630689711342587 265705878908446034567013881)
      ·
        refine ⟨199279409181334525925260411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265705878908446034567013881 199279409181334525925260411)
        ·
          refine ⟨298919113772001788887890617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199279409181334525925260411 298919113772001788887890617)
          ·
            refine ⟨224189335329001341665917963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298919113772001788887890617 224189335329001341665917963)
            ·
              refine ⟨336284002993502012498876945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224189335329001341665917963 336284002993502012498876945)
              ·
                refine ⟨252213002245126509374157709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336284002993502012498876945 252213002245126509374157709)
                ·
                  refine ⟨94579875841922441015309141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252213002245126509374157709 94579875841922441015309141)
                  ·
                    refine ⟨554178960011264302824077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 94579875841922441015309141 554178960011264302824077)
                    ·
                      rfl

theorem cell23_3237779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 9].length) (baseStart_3237779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237779 prefixEnd_3237779 := by exact prefixLift 3237779
  have htrace : WordTrace (prefixWord ++ tailWord_3237779) baseStart_3237779 baseEnd_3237779 := by
    simpa [prefixWord, tailWord_3237779, baseEnd_3237779] using wordTrace_append hprefix tailTrace_3237779
  have hstable : (prefixWord ++ tailWord_3237779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237779).length < 2 ^ (prefixWord ++ tailWord_3237779).sum := by decide
  have hdescent : baseEnd_3237779 < baseStart_3237779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237780 : List Nat := [2, 4, 2, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_3237780 : Nat := 118140960795 + 3237780 * 2 ^ 59
def prefixEnd_3237780 : Nat := 4983230072969 + 3 ^ 40 * 3237780 * 2
def baseEnd_3237780 : Nat := 1662537393514447404559727

theorem tailTrace_3237780 : CollatzResearch.WordTrace tailWord_3237780 prefixEnd_3237780 1662537393514447404559727 := by
  unfold tailWord_3237780
  simp only [CollatzResearch.WordTrace]
  refine ⟨59045769105041751822507397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78727692140055669096676529 59045769105041751822507397)
  ·
    refine ⟨11071081707195328466720137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59045769105041751822507397 11071081707195328466720137)
    ·
      refine ⟨8303311280396496350040103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11071081707195328466720137 8303311280396496350040103)
      ·
        refine ⟨12454966920594744525060155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8303311280396496350040103 12454966920594744525060155)
        ·
          refine ⟨18682450380892116787590233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12454966920594744525060155 18682450380892116787590233)
          ·
            refine ⟨14011837785669087590692675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18682450380892116787590233 14011837785669087590692675)
            ·
              refine ⟨21017756678503631386039013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14011837785669087590692675 21017756678503631386039013)
              ·
                refine ⟨3940829377219430884882315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21017756678503631386039013 3940829377219430884882315)
                ·
                  refine ⟨5911244065829146327323473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3940829377219430884882315 5911244065829146327323473)
                  ·
                    refine ⟨4433433049371859745492605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5911244065829146327323473 4433433049371859745492605)
                    ·
                      refine ⟨1662537393514447404559727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4433433049371859745492605 1662537393514447404559727)
                      ·
                        rfl

theorem cell23_3237780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_3237780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237780 prefixEnd_3237780 := by exact prefixLift 3237780
  have htrace : WordTrace (prefixWord ++ tailWord_3237780) baseStart_3237780 baseEnd_3237780 := by
    simpa [prefixWord, tailWord_3237780, baseEnd_3237780] using wordTrace_append hprefix tailTrace_3237780
  have hstable : (prefixWord ++ tailWord_3237780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237780).length < 2 ^ (prefixWord ++ tailWord_3237780).sum := by decide
  have hdescent : baseEnd_3237780 < baseStart_3237780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237783 : List Nat := [1, 1, 3, 3, 1, 5, 2, 7]
def baseStart_3237783 : Nat := 118140960795 + 3237783 * 2 ^ 59
def prefixEnd_3237783 : Nat := 4983230072969 + 3 ^ 40 * 3237783 * 2
def baseEnd_3237783 : Nat := 61575516072459662697119

theorem tailTrace_3237783 : CollatzResearch.WordTrace tailWord_3237783 prefixEnd_3237783 61575516072459662697119 := by
  unfold tailWord_3237783
  simp only [CollatzResearch.WordTrace]
  refine ⟨118091647629072635157374003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78727765086048423438249335 118091647629072635157374003)
  ·
    refine ⟨177137471443608952736061005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118091647629072635157374003 177137471443608952736061005)
    ·
      refine ⟨66426551791353357276022877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177137471443608952736061005 66426551791353357276022877)
      ·
        refine ⟨24909956921757508978508579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66426551791353357276022877 24909956921757508978508579)
        ·
          refine ⟨37364935382636263467762869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24909956921757508978508579 37364935382636263467762869)
          ·
            refine ⟨3502962692122149700102769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37364935382636263467762869 3502962692122149700102769)
            ·
              refine ⟨2627222019091612275077077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3502962692122149700102769 2627222019091612275077077)
              ·
                refine ⟨61575516072459662697119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2627222019091612275077077 61575516072459662697119)
                ·
                  rfl

theorem cell23_3237783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 7].length) (baseStart_3237783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237783 prefixEnd_3237783 := by exact prefixLift 3237783
  have htrace : WordTrace (prefixWord ++ tailWord_3237783) baseStart_3237783 baseEnd_3237783 := by
    simpa [prefixWord, tailWord_3237783, baseEnd_3237783] using wordTrace_append hprefix tailTrace_3237783
  have hstable : (prefixWord ++ tailWord_3237783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237783).length < 2 ^ (prefixWord ++ tailWord_3237783).sum := by decide
  have hdescent : baseEnd_3237783 < baseStart_3237783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237800 : List Nat := [2, 1, 6, 2, 1, 2, 9]
def baseStart_3237800 : Nat := 118140960795 + 3237800 * 2 ^ 59
def prefixEnd_3237800 : Nat := 4983230072969 + 3 ^ 40 * 3237800 * 2
def baseEnd_3237800 : Nat := 20525279791697991682835

theorem tailTrace_3237800 : CollatzResearch.WordTrace tailWord_3237800 prefixEnd_3237800 20525279791697991682835 := by
  unfold tailWord_3237800
  simp only [CollatzResearch.WordTrace]
  refine ⟨59046133835005523530371427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78728178446674031373828569 59046133835005523530371427)
  ·
    refine ⟨88569200752508285295557141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59046133835005523530371427 88569200752508285295557141)
    ·
      refine ⟨4151681285273825873229241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88569200752508285295557141 4151681285273825873229241)
      ·
        refine ⟨3113760963955369404921931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4151681285273825873229241 3113760963955369404921931)
        ·
          refine ⟨4670641445933054107382897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113760963955369404921931 4670641445933054107382897)
          ·
            refine ⟨3502981084449790580537173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4670641445933054107382897 3502981084449790580537173)
            ·
              refine ⟨20525279791697991682835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3502981084449790580537173 20525279791697991682835)
              ·
                rfl

theorem cell23_3237800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 9].length) (baseStart_3237800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237800 prefixEnd_3237800 := by exact prefixLift 3237800
  have htrace : WordTrace (prefixWord ++ tailWord_3237800) baseStart_3237800 baseEnd_3237800 := by
    simpa [prefixWord, tailWord_3237800, baseEnd_3237800] using wordTrace_append hprefix tailTrace_3237800
  have hstable : (prefixWord ++ tailWord_3237800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237800).length < 2 ^ (prefixWord ++ tailWord_3237800).sum := by decide
  have hdescent : baseEnd_3237800 < baseStart_3237800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237816 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_3237816 : Nat := 118140960795 + 3237816 * 2 ^ 59
def prefixEnd_3237816 : Nat := 4983230072969 + 3 ^ 40 * 3237816 * 2
def baseEnd_3237816 : Nat := 1662555878818009263709561

theorem tailTrace_3237816 : CollatzResearch.WordTrace tailWord_3237816 prefixEnd_3237816 1662555878818009263709561 := by
  unfold tailWord_3237816
  simp only [CollatzResearch.WordTrace]
  refine ⟨59046425618976540896662651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78728567491968721195550201 59046425618976540896662651)
  ·
    refine ⟨88569638428464811344993977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59046425618976540896662651 88569638428464811344993977)
    ·
      refine ⟨66427228821348608508745483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88569638428464811344993977 66427228821348608508745483)
      ·
        refine ⟨99640843232022912763118225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66427228821348608508745483 99640843232022912763118225)
        ·
          refine ⟨74730632424017184572338669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99640843232022912763118225 74730632424017184572338669)
          ·
            refine ⟨28023987159006444214627001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74730632424017184572338669 28023987159006444214627001)
            ·
              refine ⟨21017990369254833160970251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28023987159006444214627001 21017990369254833160970251)
              ·
                refine ⟨31526985553882249741455377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21017990369254833160970251 31526985553882249741455377)
                ·
                  refine ⟨23645239165411687306091533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31526985553882249741455377 23645239165411687306091533)
                  ·
                    refine ⟨8866964687029382739784325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23645239165411687306091533 8866964687029382739784325)
                    ·
                      refine ⟨1662555878818009263709561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8866964687029382739784325 1662555878818009263709561)
                      ·
                        rfl

theorem cell23_3237816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_3237816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237816 prefixEnd_3237816 := by exact prefixLift 3237816
  have htrace : WordTrace (prefixWord ++ tailWord_3237816) baseStart_3237816 baseEnd_3237816 := by
    simpa [prefixWord, tailWord_3237816, baseEnd_3237816] using wordTrace_append hprefix tailTrace_3237816
  have hstable : (prefixWord ++ tailWord_3237816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237816).length < 2 ^ (prefixWord ++ tailWord_3237816).sum := by decide
  have hdescent : baseEnd_3237816 < baseStart_3237816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237923 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 4]
def baseStart_3237923 : Nat := 118140960795 + 3237923 * 2 ^ 59
def prefixEnd_3237923 : Nat := 4983230072969 + 3 ^ 40 * 3237923 * 2
def baseEnd_3237923 : Nat := 1662610821248040345071569

theorem tailTrace_3237923 : CollatzResearch.WordTrace tailWord_3237923 prefixEnd_3237923 1662610821248040345071569 := by
  unfold tailWord_3237923
  simp only [CollatzResearch.WordTrace]
  refine ⟨118096753848565439067470423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78731169232376959378313615 118096753848565439067470423)
  ·
    refine ⟨177145130772848158601205635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118096753848565439067470423 177145130772848158601205635)
    ·
      refine ⟨265717696159272237901808453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177145130772848158601205635 265717696159272237901808453)
      ·
        refine ⟨49822068029863544606589085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265717696159272237901808453 49822068029863544606589085)
        ·
          refine ⟨18683275511198829227470907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49822068029863544606589085 18683275511198829227470907)
          ·
            refine ⟨28024913266798243841206361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18683275511198829227470907 28024913266798243841206361)
            ·
              refine ⟨21018684950098682880904771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28024913266798243841206361 21018684950098682880904771)
              ·
                refine ⟨31528027425148024321357157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21018684950098682880904771 31528027425148024321357157)
                ·
                  refine ⟨5911505142215254560254467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31528027425148024321357157 5911505142215254560254467)
                  ·
                    refine ⟨8867257713322881840381701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5911505142215254560254467 8867257713322881840381701)
                    ·
                      refine ⟨1662610821248040345071569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8867257713322881840381701 1662610821248040345071569)
                      ·
                        rfl

theorem cell23_3237923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_3237923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237923 prefixEnd_3237923 := by exact prefixLift 3237923
  have htrace : WordTrace (prefixWord ++ tailWord_3237923) baseStart_3237923 baseEnd_3237923 := by
    simpa [prefixWord, tailWord_3237923, baseEnd_3237923] using wordTrace_append hprefix tailTrace_3237923
  have hstable : (prefixWord ++ tailWord_3237923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237923).length < 2 ^ (prefixWord ++ tailWord_3237923).sum := by decide
  have hdescent : baseEnd_3237923 < baseStart_3237923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237943 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 3]
def baseStart_3237943 : Nat := 118140960795 + 3237943 * 2 ^ 59
def prefixEnd_3237943 : Nat := 4983230072969 + 3 ^ 40 * 3237943 * 2
def baseEnd_3237943 : Nat := 1662621090861130266821477

theorem tailTrace_3237943 : CollatzResearch.WordTrace tailWord_3237943 prefixEnd_3237943 1662621090861130266821477 := by
  unfold tailWord_3237943
  simp only [CollatzResearch.WordTrace]
  refine ⟨118097483308492982483198483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78731655538995321655465655 118097483308492982483198483)
  ·
    refine ⟨177146224962739473724797725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118097483308492982483198483 177146224962739473724797725)
    ·
      refine ⟨66429834361027302646799147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177146224962739473724797725 66429834361027302646799147)
      ·
        refine ⟨99644751541540953970198721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66429834361027302646799147 99644751541540953970198721)
        ·
          refine ⟨74733563656155715477649041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99644751541540953970198721 74733563656155715477649041)
          ·
            refine ⟨56050172742116786608236781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74733563656155715477649041 56050172742116786608236781)
            ·
              refine ⟨21018814778293794978088793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56050172742116786608236781 21018814778293794978088793)
              ·
                refine ⟨15764111083720346233566595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21018814778293794978088793 15764111083720346233566595)
                ·
                  refine ⟨23646166625580519350349893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15764111083720346233566595 23646166625580519350349893)
                  ·
                    refine ⟨4433656242296347378190605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23646166625580519350349893 4433656242296347378190605)
                    ·
                      refine ⟨1662621090861130266821477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4433656242296347378190605 1662621090861130266821477)
                      ·
                        rfl

theorem cell23_3237943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_3237943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237943 prefixEnd_3237943 := by exact prefixLift 3237943
  have htrace : WordTrace (prefixWord ++ tailWord_3237943) baseStart_3237943 baseEnd_3237943 := by
    simpa [prefixWord, tailWord_3237943, baseEnd_3237943] using wordTrace_append hprefix tailTrace_3237943
  have hstable : (prefixWord ++ tailWord_3237943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237943).length < 2 ^ (prefixWord ++ tailWord_3237943).sum := by decide
  have hdescent : baseEnd_3237943 < baseStart_3237943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237974 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3237974 : Nat := 118140960795 + 3237974 * 2 ^ 59
def prefixEnd_3237974 : Nat := 4983230072969 + 3 ^ 40 * 3237974 * 2
def baseEnd_3237974 : Nat := 1662637008761419645533835

theorem tailTrace_3237974 : CollatzResearch.WordTrace tailWord_3237974 prefixEnd_3237974 1662637008761419645533835 := by
  unfold tailWord_3237974
  simp only [CollatzResearch.WordTrace]
  refine ⟨7381163373211292173598561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78732409314253783185051317 7381163373211292173598561)
  ·
    refine ⟨5535872529908469130198921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7381163373211292173598561 5535872529908469130198921)
    ·
      refine ⟨4151904397431351847649191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5535872529908469130198921 4151904397431351847649191)
      ·
        refine ⟨6227856596147027771473787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4151904397431351847649191 6227856596147027771473787)
        ·
          refine ⟨9341784894220541657210681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6227856596147027771473787 9341784894220541657210681)
          ·
            refine ⟨7006338670665406242908011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9341784894220541657210681 7006338670665406242908011)
            ·
              refine ⟨10509508005998109364362017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7006338670665406242908011 10509508005998109364362017)
              ·
                refine ⟨7882131004498582023271513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10509508005998109364362017 7882131004498582023271513)
                ·
                  refine ⟨5911598253373936517453635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7882131004498582023271513 5911598253373936517453635)
                  ·
                    refine ⟨8867397380060904776180453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5911598253373936517453635 8867397380060904776180453)
                    ·
                      refine ⟨1662637008761419645533835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8867397380060904776180453 1662637008761419645533835)
                      ·
                        rfl

theorem cell23_3237974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3237974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237974 prefixEnd_3237974 := by exact prefixLift 3237974
  have htrace : WordTrace (prefixWord ++ tailWord_3237974) baseStart_3237974 baseEnd_3237974 := by
    simpa [prefixWord, tailWord_3237974, baseEnd_3237974] using wordTrace_append hprefix tailTrace_3237974
  have hstable : (prefixWord ++ tailWord_3237974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237974).length < 2 ^ (prefixWord ++ tailWord_3237974).sum := by decide
  have hdescent : baseEnd_3237974 < baseStart_3237974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237984 : List Nat := [2, 1, 1, 3, 2, 4, 3, 2, 1, 4]
def baseStart_3237984 : Nat := 118140960795 + 3237984 * 2 ^ 59
def prefixEnd_3237984 : Nat := 4983230072969 + 3 ^ 40 * 3237984 * 2
def baseEnd_3237984 : Nat := 554214047855988202136263

theorem tailTrace_3237984 : CollatzResearch.WordTrace tailWord_3237984 prefixEnd_3237984 554214047855988202136263 := by
  unfold tailWord_3237984
  simp only [CollatzResearch.WordTrace]
  refine ⟨59049489350672223242720503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78732652467562964323627337 59049489350672223242720503)
  ·
    refine ⟨88574234026008334864080755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59049489350672223242720503 88574234026008334864080755)
    ·
      refine ⟨132861351039012502296121133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88574234026008334864080755 132861351039012502296121133)
      ·
        refine ⟨49823006639629688361045425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132861351039012502296121133 49823006639629688361045425)
        ·
          refine ⟨37367254979722266270784069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49823006639629688361045425 37367254979722266270784069)
          ·
            refine ⟨7006360308697924925772013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37367254979722266270784069 7006360308697924925772013)
            ·
              refine ⟨2627385115761721847164505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7006360308697924925772013 2627385115761721847164505)
              ·
                refine ⟨1970538836821291385373379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2627385115761721847164505 1970538836821291385373379)
                ·
                  refine ⟨2955808255231937078060069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970538836821291385373379 2955808255231937078060069)
                  ·
                    refine ⟨554214047855988202136263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2955808255231937078060069 554214047855988202136263)
                    ·
                      rfl

theorem cell23_3237984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 1, 4].length) (baseStart_3237984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237984 prefixEnd_3237984 := by exact prefixLift 3237984
  have htrace : WordTrace (prefixWord ++ tailWord_3237984) baseStart_3237984 baseEnd_3237984 := by
    simpa [prefixWord, tailWord_3237984, baseEnd_3237984] using wordTrace_append hprefix tailTrace_3237984
  have hstable : (prefixWord ++ tailWord_3237984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237984).length < 2 ^ (prefixWord ++ tailWord_3237984).sum := by decide
  have hdescent : baseEnd_3237984 < baseStart_3237984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237993 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 3, 5]
def baseStart_3237993 : Nat := 118140960795 + 3237993 * 2 ^ 59
def prefixEnd_3237993 : Nat := 4983230072969 + 3 ^ 40 * 3237993 * 2
def baseEnd_3237993 : Nat := 554215588297951690398749

theorem tailTrace_3237993 : CollatzResearch.WordTrace tailWord_3237993 prefixEnd_3237993 554215588297951690398749 := by
  unfold tailWord_3237993
  simp only [CollatzResearch.WordTrace]
  refine ⟨118099306958311841022518633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78732871305541227348345755 118099306958311841022518633)
  ·
    refine ⟨88574480218733880766888975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118099306958311841022518633 88574480218733880766888975)
    ·
      refine ⟨132861720328100821150333463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88574480218733880766888975 132861720328100821150333463)
      ·
        refine ⟨199292580492151231725500195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132861720328100821150333463 199292580492151231725500195)
        ·
          refine ⟨298938870738226847588250293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199292580492151231725500195 298938870738226847588250293)
          ·
            refine ⟨28025519131708766961398465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 298938870738226847588250293 28025519131708766961398465)
            ·
              refine ⟨21019139348781575221048849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28025519131708766961398465 21019139348781575221048849)
              ·
                refine ⟨15764354511586181415786637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21019139348781575221048849 15764354511586181415786637)
                ·
                  refine ⟨5911632941844818030919989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15764354511586181415786637 5911632941844818030919989)
                  ·
                    refine ⟨554215588297951690398749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5911632941844818030919989 554215588297951690398749)
                    ·
                      rfl

theorem cell23_3237993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 3, 5].length) (baseStart_3237993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3237993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3237993 prefixEnd_3237993 := by exact prefixLift 3237993
  have htrace : WordTrace (prefixWord ++ tailWord_3237993) baseStart_3237993 baseEnd_3237993 := by
    simpa [prefixWord, tailWord_3237993, baseEnd_3237993] using wordTrace_append hprefix tailTrace_3237993
  have hstable : (prefixWord ++ tailWord_3237993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237993).length < 2 ^ (prefixWord ++ tailWord_3237993).sum := by decide
  have hdescent : baseEnd_3237993 < baseStart_3237993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238023 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 3, 6]
def baseStart_3238023 : Nat := 118140960795 + 3238023 * 2 ^ 59
def prefixEnd_3238023 : Nat := 4983230072969 + 3 ^ 40 * 3238023 * 2
def baseEnd_3238023 : Nat := 554220723104496651273703

theorem tailTrace_3238023 : CollatzResearch.WordTrace tailWord_3238023 prefixEnd_3238023 554220723104496651273703 := by
  unfold tailWord_3238023
  simp only [CollatzResearch.WordTrace]
  refine ⟨118100401148203156146110723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78733600765468770764073815 118100401148203156146110723)
  ·
    refine ⟨177150601722304734219166085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118100401148203156146110723 177150601722304734219166085)
    ·
      refine ⟨33215737822932137666093641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177150601722304734219166085 33215737822932137666093641)
      ·
        refine ⟨24911803367199103249570231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33215737822932137666093641 24911803367199103249570231)
        ·
          refine ⟨37367705050798654874355347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24911803367199103249570231 37367705050798654874355347)
          ·
            refine ⟨56051557576197982311533021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37367705050798654874355347 56051557576197982311533021)
            ·
              refine ⟨21019334091074243366824883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56051557576197982311533021 21019334091074243366824883)
              ·
                refine ⟨31529001136611365050237325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21019334091074243366824883 31529001136611365050237325)
                ·
                  refine ⟨11823375426229261893838997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31529001136611365050237325 11823375426229261893838997)
                  ·
                    refine ⟨554220723104496651273703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11823375426229261893838997 554220723104496651273703)
                    ·
                      rfl

theorem cell23_3238023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_3238023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238023 prefixEnd_3238023 := by exact prefixLift 3238023
  have htrace : WordTrace (prefixWord ++ tailWord_3238023) baseStart_3238023 baseEnd_3238023 := by
    simpa [prefixWord, tailWord_3238023, baseEnd_3238023] using wordTrace_append hprefix tailTrace_3238023
  have hstable : (prefixWord ++ tailWord_3238023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238023).length < 2 ^ (prefixWord ++ tailWord_3238023).sum := by decide
  have hdescent : baseEnd_3238023 < baseStart_3238023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238043 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 4]
def baseStart_3238043 : Nat := 118140960795 + 3238043 * 2 ^ 59
def prefixEnd_3238043 : Nat := 4983230072969 + 3 ^ 40 * 3238043 * 2
def baseEnd_3238043 : Nat := 1662672438926579875571017

theorem tailTrace_3238043 : CollatzResearch.WordTrace tailWord_3238043 prefixEnd_3238043 1662672438926579875571017 := by
  unfold tailWord_3238043
  simp only [CollatzResearch.WordTrace]
  refine ⟨118101130608130699561838783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78734087072087133041225855 118101130608130699561838783)
  ·
    refine ⟨177151695912196049342758175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118101130608130699561838783 177151695912196049342758175)
    ·
      refine ⟨265727543868294074014137263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177151695912196049342758175 265727543868294074014137263)
      ·
        refine ⟨398591315802441111021205895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265727543868294074014137263 398591315802441111021205895)
        ·
          refine ⟨597886973703661666531808843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398591315802441111021205895 597886973703661666531808843)
          ·
            refine ⟨896830460555492499797713265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597886973703661666531808843 896830460555492499797713265)
            ·
              refine ⟨672622845416619374848284949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896830460555492499797713265 672622845416619374848284949)
              ·
                refine ⟨31529195878904033196013357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 672622845416619374848284949 31529195878904033196013357)
                ·
                  refine ⟨11823448454589012448505009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31529195878904033196013357 11823448454589012448505009)
                  ·
                    refine ⟨8867586340941759336378757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11823448454589012448505009 8867586340941759336378757)
                    ·
                      refine ⟨1662672438926579875571017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8867586340941759336378757 1662672438926579875571017)
                      ·
                        rfl

theorem cell23_3238043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 4].length) (baseStart_3238043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238043 prefixEnd_3238043 := by exact prefixLift 3238043
  have htrace : WordTrace (prefixWord ++ tailWord_3238043) baseStart_3238043 baseEnd_3238043 := by
    simpa [prefixWord, tailWord_3238043, baseEnd_3238043] using wordTrace_append hprefix tailTrace_3238043
  have hstable : (prefixWord ++ tailWord_3238043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238043).length < 2 ^ (prefixWord ++ tailWord_3238043).sum := by decide
  have hdescent : baseEnd_3238043 < baseStart_3238043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238068 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_3238068 : Nat := 118140960795 + 3238068 * 2 ^ 59
def prefixEnd_3238068 : Nat := 4983230072969 + 3 ^ 40 * 3238068 * 2
def baseEnd_3238068 : Nat := 1662685275942942277758403

theorem tailTrace_3238068 : CollatzResearch.WordTrace tailWord_3238068 prefixEnd_3238068 1662685275942942277758403 := by
  unfold tailWord_3238068
  simp only [CollatzResearch.WordTrace]
  refine ⟨59051021216520064415749429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78734694955360085887665905 59051021216520064415749429)
  ·
    refine ⟨5536033239048756038976509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59051021216520064415749429 5536033239048756038976509)
    ·
      refine ⟨2076012464643283514616191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5536033239048756038976509 2076012464643283514616191)
      ·
        refine ⟨3114018696964925271924287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2076012464643283514616191 3114018696964925271924287)
        ·
          refine ⟨4671028045447387907886431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3114018696964925271924287 4671028045447387907886431)
          ·
            refine ⟨7006542068171081861829647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4671028045447387907886431 7006542068171081861829647)
            ·
              refine ⟨10509813102256622792744471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7006542068171081861829647 10509813102256622792744471)
              ·
                refine ⟨15764719653384934189116707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10509813102256622792744471 15764719653384934189116707)
                ·
                  refine ⟨23647079480077401283675061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15764719653384934189116707 23647079480077401283675061)
                  ·
                    refine ⟨2216913701257256370344537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23647079480077401283675061 2216913701257256370344537)
                    ·
                      refine ⟨1662685275942942277758403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2216913701257256370344537 1662685275942942277758403)
                      ·
                        rfl

theorem cell23_3238068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_3238068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238068 prefixEnd_3238068 := by exact prefixLift 3238068
  have htrace : WordTrace (prefixWord ++ tailWord_3238068) baseStart_3238068 baseEnd_3238068 := by
    simpa [prefixWord, tailWord_3238068, baseEnd_3238068] using wordTrace_append hprefix tailTrace_3238068
  have hstable : (prefixWord ++ tailWord_3238068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238068).length < 2 ^ (prefixWord ++ tailWord_3238068).sum := by decide
  have hdescent : baseEnd_3238068 < baseStart_3238068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238084 : List Nat := [2, 3, 3, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_3238084 : Nat := 118140960795 + 3238084 * 2 ^ 59
def prefixEnd_3238084 : Nat := 4983230072969 + 3 ^ 40 * 3238084 * 2
def baseEnd_3238084 : Nat := 1662693491633414215158329

theorem tailTrace_3238084 : CollatzResearch.WordTrace tailWord_3238084 prefixEnd_3238084 1662693491633414215158329 := by
  unfold tailWord_3238084
  simp only [CollatzResearch.WordTrace]
  refine ⟨59051313000491081782040653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78735084000654775709387537 59051313000491081782040653)
  ·
    refine ⟨22144242375184155668265245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59051313000491081782040653 22144242375184155668265245)
    ·
      refine ⟨8304090890694058375599467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22144242375184155668265245 8304090890694058375599467)
      ·
        refine ⟨12456136336041087563399201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8304090890694058375599467 12456136336041087563399201)
        ·
          refine ⟨9342102252030815672549401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12456136336041087563399201 9342102252030815672549401)
          ·
            refine ⟨7006576689023111754412051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9342102252030815672549401 7006576689023111754412051)
            ·
              refine ⟨10509865033534667631618077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7006576689023111754412051 10509865033534667631618077)
              ·
                refine ⟨3941199387575500361856779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10509865033534667631618077 3941199387575500361856779)
                ·
                  refine ⟨5911799081363250542785169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941199387575500361856779 5911799081363250542785169)
                  ·
                    refine ⟨4433849311022437907088877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5911799081363250542785169 4433849311022437907088877)
                    ·
                      refine ⟨1662693491633414215158329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4433849311022437907088877 1662693491633414215158329)
                      ·
                        rfl

theorem cell23_3238084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_3238084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238084 prefixEnd_3238084 := by exact prefixLift 3238084
  have htrace : WordTrace (prefixWord ++ tailWord_3238084) baseStart_3238084 baseEnd_3238084 := by
    simpa [prefixWord, tailWord_3238084, baseEnd_3238084] using wordTrace_append hprefix tailTrace_3238084
  have hstable : (prefixWord ++ tailWord_3238084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238084).length < 2 ^ (prefixWord ++ tailWord_3238084).sum := by decide
  have hdescent : baseEnd_3238084 < baseStart_3238084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238108 : List Nat := [2, 2, 5, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3238108 : Nat := 118140960795 + 3238108 * 2 ^ 59
def prefixEnd_3238108 : Nat := 4983230072969 + 3 ^ 40 * 3238108 * 2
def baseEnd_3238108 : Nat := 554235271723040707086073

theorem tailTrace_3238108 : CollatzResearch.WordTrace tailWord_3238108 prefixEnd_3238108 554235271723040707086073 := by
  unfold tailWord_3238108
  simp only [CollatzResearch.WordTrace]
  refine ⟨59051750676447607831477489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78735667568596810441969985 59051750676447607831477489)
  ·
    refine ⟨44288813007335705873608117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59051750676447607831477489 44288813007335705873608117)
    ·
      refine ⟨4152076219437722425650761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44288813007335705873608117 4152076219437722425650761)
      ·
        refine ⟨3114057164578291819238071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4152076219437722425650761 3114057164578291819238071)
        ·
          refine ⟨4671085746867437728857107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3114057164578291819238071 4671085746867437728857107)
          ·
            refine ⟨7006628620301156593285661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4671085746867437728857107 7006628620301156593285661)
            ·
              refine ⟨2627485732612933722482123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7006628620301156593285661 2627485732612933722482123)
              ·
                refine ⟨3941228598919400583723185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627485732612933722482123 3941228598919400583723185)
                ·
                  refine ⟨2955921449189550437792389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3941228598919400583723185 2955921449189550437792389)
                  ·
                    refine ⟨554235271723040707086073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2955921449189550437792389 554235271723040707086073)
                    ·
                      rfl

theorem cell23_3238108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3238108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238108 prefixEnd_3238108 := by exact prefixLift 3238108
  have htrace : WordTrace (prefixWord ++ tailWord_3238108) baseStart_3238108 baseEnd_3238108 := by
    simpa [prefixWord, tailWord_3238108, baseEnd_3238108] using wordTrace_append hprefix tailTrace_3238108
  have hstable : (prefixWord ++ tailWord_3238108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238108).length < 2 ^ (prefixWord ++ tailWord_3238108).sum := by decide
  have hdescent : baseEnd_3238108 < baseStart_3238108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238124 : List Nat := [2, 2, 1, 1, 2, 3, 4, 2, 1, 3, 2]
def baseStart_3238124 : Nat := 118140960795 + 3238124 * 2 ^ 59
def prefixEnd_3238124 : Nat := 4983230072969 + 3 ^ 40 * 3238124 * 2
def baseEnd_3238124 : Nat := 1662714030859594058658145

theorem tailTrace_3238124 : CollatzResearch.WordTrace tailWord_3238124 prefixEnd_3238124 1662714030859594058658145 := by
  unfold tailWord_3238124
  simp only [CollatzResearch.WordTrace]
  refine ⟨59052042460418625197768713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78736056613891500263691617 59052042460418625197768713)
  ·
    refine ⟨44289031845313968898326535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59052042460418625197768713 44289031845313968898326535)
    ·
      refine ⟨66433547767970953347489803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44289031845313968898326535 66433547767970953347489803)
      ·
        refine ⟨99650321651956430021234705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66433547767970953347489803 99650321651956430021234705)
        ·
          refine ⟨74737741238967322515926029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99650321651956430021234705 74737741238967322515926029)
          ·
            refine ⟨28026652964612745943472261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74737741238967322515926029 28026652964612745943472261)
            ·
              refine ⟨5254997430864889864401049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28026652964612745943472261 5254997430864889864401049)
              ·
                refine ⟨3941248073148667398300787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5254997430864889864401049 3941248073148667398300787)
                ·
                  refine ⟨5911872109723001097451181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941248073148667398300787 5911872109723001097451181)
                  ·
                    refine ⟨2216952041146125411544193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5911872109723001097451181 2216952041146125411544193)
                    ·
                      refine ⟨1662714030859594058658145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2216952041146125411544193 1662714030859594058658145)
                      ·
                        rfl

theorem cell23_3238124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 3, 2].length) (baseStart_3238124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238124 prefixEnd_3238124 := by exact prefixLift 3238124
  have htrace : WordTrace (prefixWord ++ tailWord_3238124) baseStart_3238124 baseEnd_3238124 := by
    simpa [prefixWord, tailWord_3238124, baseEnd_3238124] using wordTrace_append hprefix tailTrace_3238124
  have hstable : (prefixWord ++ tailWord_3238124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238124).length < 2 ^ (prefixWord ++ tailWord_3238124).sum := by decide
  have hdescent : baseEnd_3238124 < baseStart_3238124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238140 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_3238140 : Nat := 118140960795 + 3238140 * 2 ^ 59
def prefixEnd_3238140 : Nat := 4983230072969 + 3 ^ 40 * 3238140 * 2
def baseEnd_3238140 : Nat := 1662722246550065996058071

theorem tailTrace_3238140 : CollatzResearch.WordTrace tailWord_3238140 prefixEnd_3238140 1662722246550065996058071 := by
  unfold tailWord_3238140
  simp only [CollatzResearch.WordTrace]
  refine ⟨59052334244389642564059937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78736445659186190085413249 59052334244389642564059937)
  ·
    refine ⟨44289250683292231923044953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59052334244389642564059937 44289250683292231923044953)
    ·
      refine ⟨33216938012469173942283715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44289250683292231923044953 33216938012469173942283715)
      ·
        refine ⟨49825407018703760913425573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33216938012469173942283715 49825407018703760913425573)
        ·
          refine ⟨9342263816006955171267295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49825407018703760913425573 9342263816006955171267295)
          ·
            refine ⟨14013395724010432756900943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9342263816006955171267295 14013395724010432756900943)
            ·
              refine ⟨21020093586015649135351415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14013395724010432756900943 21020093586015649135351415)
              ·
                refine ⟨31530140379023473703027123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21020093586015649135351415 31530140379023473703027123)
                ·
                  refine ⟨47295210568535210554540685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31530140379023473703027123 47295210568535210554540685)
                  ·
                    refine ⟨17735703963200703957952757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47295210568535210554540685 17735703963200703957952757)
                    ·
                      refine ⟨1662722246550065996058071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17735703963200703957952757 1662722246550065996058071)
                      ·
                        rfl

theorem cell23_3238140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_3238140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238140 prefixEnd_3238140 := by exact prefixLift 3238140
  have htrace : WordTrace (prefixWord ++ tailWord_3238140) baseStart_3238140 baseEnd_3238140 := by
    simpa [prefixWord, tailWord_3238140, baseEnd_3238140] using wordTrace_append hprefix tailTrace_3238140
  have hstable : (prefixWord ++ tailWord_3238140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238140).length < 2 ^ (prefixWord ++ tailWord_3238140).sum := by decide
  have hdescent : baseEnd_3238140 < baseStart_3238140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238154 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2]
def baseStart_3238154 : Nat := 118140960795 + 3238154 * 2 ^ 59
def prefixEnd_3238154 : Nat := 4983230072969 + 3 ^ 40 * 3238154 * 2
def baseEnd_3238154 : Nat := 1662729435279228941283007

theorem tailTrace_3238154 : CollatzResearch.WordTrace tailWord_3238154 prefixEnd_3238154 1662729435279228941283007 := by
  unfold tailWord_3238154
  simp only [CollatzResearch.WordTrace]
  refine ⟨29526294777682141379782379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78736786073819043679419677 29526294777682141379782379)
  ·
    refine ⟨44289442166523212069673569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29526294777682141379782379 44289442166523212069673569)
    ·
      refine ⟨33217081624892409052255177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44289442166523212069673569 33217081624892409052255177)
      ·
        refine ⟨24912811218669306789191383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33217081624892409052255177 24912811218669306789191383)
        ·
          refine ⟨37369216828003960183787075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24912811218669306789191383 37369216828003960183787075)
          ·
            refine ⟨56053825242005940275680613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37369216828003960183787075 56053825242005940275680613)
            ·
              refine ⟨10510092232876113801690115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56053825242005940275680613 10510092232876113801690115)
              ·
                refine ⟨15765138349314170702535173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10510092232876113801690115 15765138349314170702535173)
                ·
                  refine ⟨2955963440496407006725345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15765138349314170702535173 2955963440496407006725345)
                  ·
                    refine ⟨2216972580372305255044009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2955963440496407006725345 2216972580372305255044009)
                    ·
                      refine ⟨1662729435279228941283007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2216972580372305255044009 1662729435279228941283007)
                      ·
                        rfl

theorem cell23_3238154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_3238154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238154 prefixEnd_3238154 := by exact prefixLift 3238154
  have htrace : WordTrace (prefixWord ++ tailWord_3238154) baseStart_3238154 baseEnd_3238154 := by
    simpa [prefixWord, tailWord_3238154, baseEnd_3238154] using wordTrace_append hprefix tailTrace_3238154
  have hstable : (prefixWord ++ tailWord_3238154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238154).length < 2 ^ (prefixWord ++ tailWord_3238154).sum := by decide
  have hdescent : baseEnd_3238154 < baseStart_3238154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238171 : List Nat := [1, 1, 1, 1, 1, 1, 10, 1, 2, 2, 2]
def baseStart_3238171 : Nat := 118140960795 + 3238171 * 2 ^ 59
def prefixEnd_3238171 : Nat := 4983230072969 + 3 ^ 40 * 3238171 * 2
def baseEnd_3238171 : Nat := 1662738164450355374770429

theorem tailTrace_3238171 : CollatzResearch.WordTrace tailWord_3238171 prefixEnd_3238171 1662738164450355374770429 := by
  unfold tailWord_3238171
  simp only [CollatzResearch.WordTrace]
  refine ⟨118105799151666977422498367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78737199434444651614998911 118105799151666977422498367)
  ·
    refine ⟨177158698727500466133747551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118105799151666977422498367 177158698727500466133747551)
    ·
      refine ⟨265738048091250699200621327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177158698727500466133747551 265738048091250699200621327)
      ·
        refine ⟨398607072136876048800931991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265738048091250699200621327 398607072136876048800931991)
        ·
          refine ⟨597910608205314073201397987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398607072136876048800931991 597910608205314073201397987)
          ·
            refine ⟨896865912307971109802096981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597910608205314073201397987 896865912307971109802096981)
            ·
              refine ⟨2627536852464759110748331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 896865912307971109802096981 2627536852464759110748331)
              ·
                refine ⟨3941305278697138666122497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627536852464759110748331 3941305278697138666122497)
                ·
                  refine ⟨2955978959022853999591873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3941305278697138666122497 2955978959022853999591873)
                  ·
                    refine ⟨2216984219267140499693905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2955978959022853999591873 2216984219267140499693905)
                    ·
                      refine ⟨1662738164450355374770429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2216984219267140499693905 1662738164450355374770429)
                      ·
                        rfl

theorem cell23_3238171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 2, 2, 2].length) (baseStart_3238171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238171 prefixEnd_3238171 := by exact prefixLift 3238171
  have htrace : WordTrace (prefixWord ++ tailWord_3238171) baseStart_3238171 baseEnd_3238171 := by
    simpa [prefixWord, tailWord_3238171, baseEnd_3238171] using wordTrace_append hprefix tailTrace_3238171
  have hstable : (prefixWord ++ tailWord_3238171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238171).length < 2 ^ (prefixWord ++ tailWord_3238171).sum := by decide
  have hdescent : baseEnd_3238171 < baseStart_3238171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238174 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3238174 : Nat := 118140960795 + 3238174 * 2 ^ 59
def prefixEnd_3238174 : Nat := 4983230072969 + 3 ^ 40 * 3238174 * 2
def baseEnd_3238174 : Nat := 1662739704892318863032915

theorem tailTrace_3238174 : CollatzResearch.WordTrace tailWord_3238174 prefixEnd_3238174 1662739704892318863032915 := by
  unfold tailWord_3238174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14763238571332013616857197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78737272380437405956571717 14763238571332013616857197)
  ·
    refine ⟨5536214464249505106321449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14763238571332013616857197 5536214464249505106321449)
    ·
      refine ⟨4152160848187128829741087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5536214464249505106321449 4152160848187128829741087)
      ·
        refine ⟨6228241272280693244611631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4152160848187128829741087 6228241272280693244611631)
        ·
          refine ⟨9342361908421039866917447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6228241272280693244611631 9342361908421039866917447)
          ·
            refine ⟨14013542862631559800376171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9342361908421039866917447 14013542862631559800376171)
            ·
              refine ⟨21020314293947339700564257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14013542862631559800376171 21020314293947339700564257)
              ·
                refine ⟨15765235720460504775423193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21020314293947339700564257 15765235720460504775423193)
                ·
                  refine ⟨11823926790345378581567395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15765235720460504775423193 11823926790345378581567395)
                  ·
                    refine ⟨17735890185518067872351093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11823926790345378581567395 17735890185518067872351093)
                    ·
                      refine ⟨1662739704892318863032915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17735890185518067872351093 1662739704892318863032915)
                      ·
                        rfl

theorem cell23_3238174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3238174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238174 prefixEnd_3238174 := by exact prefixLift 3238174
  have htrace : WordTrace (prefixWord ++ tailWord_3238174) baseStart_3238174 baseEnd_3238174 := by
    simpa [prefixWord, tailWord_3238174, baseEnd_3238174] using wordTrace_append hprefix tailTrace_3238174
  have hstable : (prefixWord ++ tailWord_3238174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238174).length < 2 ^ (prefixWord ++ tailWord_3238174).sum := by decide
  have hdescent : baseEnd_3238174 < baseStart_3238174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238200 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_3238200 : Nat := 118140960795 + 3238200 * 2 ^ 59
def prefixEnd_3238200 : Nat := 4983230072969 + 3 ^ 40 * 3238200 * 2
def baseEnd_3238200 : Nat := 1662753055389335761307795

theorem tailTrace_3238200 : CollatzResearch.WordTrace tailWord_3238200 prefixEnd_3238200 1662753055389335761307795 := by
  unfold tailWord_3238200
  simp only [CollatzResearch.WordTrace]
  refine ⟨59053428434280957687652027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78737904579041276916869369 59053428434280957687652027)
  ·
    refine ⟨88580142651421436531478041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59053428434280957687652027 88580142651421436531478041)
    ·
      refine ⟨66435106988566077398608531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88580142651421436531478041 66435106988566077398608531)
      ·
        refine ⟨99652660482849116097912797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66435106988566077398608531 99652660482849116097912797)
        ·
          refine ⟨37369747681068418536717299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99652660482849116097912797 37369747681068418536717299)
          ·
            refine ⟨56054621521602627805075949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37369747681068418536717299 56054621521602627805075949)
            ·
              refine ⟨21020483070600985426903481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56054621521602627805075949 21020483070600985426903481)
              ·
                refine ⟨15765362302950739070177611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21020483070600985426903481 15765362302950739070177611)
                ·
                  refine ⟨23648043454426108605266417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15765362302950739070177611 23648043454426108605266417)
                  ·
                    refine ⟨17736032590819581453949813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23648043454426108605266417 17736032590819581453949813)
                    ·
                      refine ⟨1662753055389335761307795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17736032590819581453949813 1662753055389335761307795)
                      ·
                        rfl

theorem cell23_3238200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_3238200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238200 prefixEnd_3238200 := by exact prefixLift 3238200
  have htrace : WordTrace (prefixWord ++ tailWord_3238200) baseStart_3238200 baseEnd_3238200 := by
    simpa [prefixWord, tailWord_3238200, baseEnd_3238200] using wordTrace_append hprefix tailTrace_3238200
  have hstable : (prefixWord ++ tailWord_3238200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238200).length < 2 ^ (prefixWord ++ tailWord_3238200).sum := by decide
  have hdescent : baseEnd_3238200 < baseStart_3238200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238267 : List Nat := [1, 1, 1, 1, 1, 7, 3, 2, 6]
def baseStart_3238267 : Nat := 118140960795 + 3238267 * 2 ^ 59
def prefixEnd_3238267 : Nat := 4983230072969 + 3 ^ 40 * 3238267 * 2
def baseEnd_3238267 : Nat := 184754162065909666574443

theorem tailTrace_3238267 : CollatzResearch.WordTrace tailWord_3238267 prefixEnd_3238267 184754162065909666574443 := by
  unfold tailWord_3238267
  simp only [CollatzResearch.WordTrace]
  refine ⟨118109300559319185817993055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78739533706212790545328703 118109300559319185817993055)
  ·
    refine ⟨177163950838978778726989583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118109300559319185817993055 177163950838978778726989583)
    ·
      refine ⟨265745926258468168090484375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177163950838978778726989583 265745926258468168090484375)
      ·
        refine ⟨398618889387702252135726563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265745926258468168090484375 398618889387702252135726563)
        ·
          refine ⟨597928334081553378203589845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398618889387702252135726563 597928334081553378203589845)
          ·
            refine ⟨14013945330036407301646637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 597928334081553378203589845 14013945330036407301646637)
            ·
              refine ⟨5255229498763652738117489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14013945330036407301646637 5255229498763652738117489)
              ·
                refine ⟨3941422124072739553588117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5255229498763652738117489 3941422124072739553588117)
                ·
                  refine ⟨184754162065909666574443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3941422124072739553588117 184754162065909666574443)
                  ·
                    rfl

theorem cell23_3238267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 6].length) (baseStart_3238267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238267 prefixEnd_3238267 := by exact prefixLift 3238267
  have htrace : WordTrace (prefixWord ++ tailWord_3238267) baseStart_3238267 baseEnd_3238267 := by
    simpa [prefixWord, tailWord_3238267, baseEnd_3238267] using wordTrace_append hprefix tailTrace_3238267
  have hstable : (prefixWord ++ tailWord_3238267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238267).length < 2 ^ (prefixWord ++ tailWord_3238267).sum := by decide
  have hdescent : baseEnd_3238267 < baseStart_3238267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238284 : List Nat := [2, 2, 1, 2, 1, 5, 3, 1, 6]
def baseStart_3238284 : Nat := 118140960795 + 3238284 * 2 ^ 59
def prefixEnd_3238284 : Nat := 4983230072969 + 3 ^ 40 * 3238284 * 2
def baseEnd_3238284 : Nat := 184755131973812603628601

theorem tailTrace_3238284 : CollatzResearch.WordTrace tailWord_3238284 prefixEnd_3238284 184755131973812603628601 := by
  unfold tailWord_3238284
  simp only [CollatzResearch.WordTrace]
  refine ⟨59054960300128798860680953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78739947066838398480907937 59054960300128798860680953)
  ·
    refine ⟨44291220225096599145510715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59054960300128798860680953 44291220225096599145510715)
    ·
      refine ⟨66436830337644898718266073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44291220225096599145510715 66436830337644898718266073)
      ·
        refine ⟨49827622753233674038699555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66436830337644898718266073 49827622753233674038699555)
        ·
          refine ⟨74741434129850511058049333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49827622753233674038699555 74741434129850511058049333)
          ·
            refine ⟨7007009449673485411692125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74741434129850511058049333 7007009449673485411692125)
            ·
              refine ⟨2627628543627557029384547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7007009449673485411692125 2627628543627557029384547)
              ·
                refine ⟨3941442815441335544076821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627628543627557029384547 3941442815441335544076821)
                ·
                  refine ⟨184755131973812603628601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3941442815441335544076821 184755131973812603628601)
                  ·
                    rfl

theorem cell23_3238284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 6].length) (baseStart_3238284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238284 prefixEnd_3238284 := by exact prefixLift 3238284
  have htrace : WordTrace (prefixWord ++ tailWord_3238284) baseStart_3238284 baseEnd_3238284 := by
    simpa [prefixWord, tailWord_3238284, baseEnd_3238284] using wordTrace_append hprefix tailTrace_3238284
  have hstable : (prefixWord ++ tailWord_3238284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238284).length < 2 ^ (prefixWord ++ tailWord_3238284).sum := by decide
  have hdescent : baseEnd_3238284 < baseStart_3238284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238304 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 1, 5, 2]
def baseStart_3238304 : Nat := 118140960795 + 3238304 * 2 ^ 59
def prefixEnd_3238304 : Nat := 4983230072969 + 3 ^ 40 * 3238304 * 2
def baseEnd_3238304 : Nat := 1662806457377403354407317

theorem tailTrace_3238304 : CollatzResearch.WordTrace tailWord_3238304 prefixEnd_3238304 1662806457377403354407317 := by
  unfold tailWord_3238304
  simp only [CollatzResearch.WordTrace]
  refine ⟨59055325030092570568544983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78740433373456760758059977 59055325030092570568544983)
  ·
    refine ⟨88582987545138855852817475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59055325030092570568544983 88582987545138855852817475)
    ·
      refine ⟨132874481317708283779226213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88582987545138855852817475 132874481317708283779226213)
      ·
        refine ⟨24913965247070303208604915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132874481317708283779226213 24913965247070303208604915)
        ·
          refine ⟨37370947870605454812907373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24913965247070303208604915 37370947870605454812907373)
          ·
            refine ⟨14014105451477045554840265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37370947870605454812907373 14014105451477045554840265)
            ·
              refine ⟨10510579088607784166130199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14014105451477045554840265 10510579088607784166130199)
              ·
                refine ⟨15765868632911676249195299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10510579088607784166130199 15765868632911676249195299)
                ·
                  refine ⟨23648802949367514373792949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15765868632911676249195299 23648802949367514373792949)
                  ·
                    refine ⟨2217075276503204472543089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23648802949367514373792949 2217075276503204472543089)
                    ·
                      refine ⟨1662806457377403354407317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217075276503204472543089 1662806457377403354407317)
                      ·
                        rfl

theorem cell23_3238304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_3238304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238304 prefixEnd_3238304 := by exact prefixLift 3238304
  have htrace : WordTrace (prefixWord ++ tailWord_3238304) baseStart_3238304 baseEnd_3238304 := by
    simpa [prefixWord, tailWord_3238304, baseEnd_3238304] using wordTrace_append hprefix tailTrace_3238304
  have hstable : (prefixWord ++ tailWord_3238304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238304).length < 2 ^ (prefixWord ++ tailWord_3238304).sum := by decide
  have hdescent : baseEnd_3238304 < baseStart_3238304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238305 : List Nat := [1, 2, 3, 5, 1, 2, 1, 3, 1, 4]
def baseStart_3238305 : Nat := 118140960795 + 3238305 * 2 ^ 59
def prefixEnd_3238305 : Nat := 4983230072969 + 3 ^ 40 * 3238305 * 2
def baseEnd_3238305 : Nat := 554268990286019283498271

theorem tailTrace_3238305 : CollatzResearch.WordTrace tailWord_3238305 prefixEnd_3238305 554268990286019283498271 := by
  unfold tailWord_3238305
  simp only [CollatzResearch.WordTrace]
  refine ⟨118110686533181518307876369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78740457688787678871917579 118110686533181518307876369)
  ·
    refine ⟨88583014899886138730907277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118110686533181518307876369 88583014899886138730907277)
    ·
      refine ⟨33218630587457302024090229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88583014899886138730907277 33218630587457302024090229)
      ·
        refine ⟨3114246617574122064758459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33218630587457302024090229 3114246617574122064758459)
        ·
          refine ⟨4671369926361183097137689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3114246617574122064758459 4671369926361183097137689)
          ·
            refine ⟨3503527444770887322853267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4671369926361183097137689 3503527444770887322853267)
            ·
              refine ⟨5255291167156330984279901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503527444770887322853267 5255291167156330984279901)
              ·
                refine ⟨1970734187683624119104963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5255291167156330984279901 1970734187683624119104963)
                ·
                  refine ⟨2956101281525436178657445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970734187683624119104963 2956101281525436178657445)
                  ·
                    refine ⟨554268990286019283498271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2956101281525436178657445 554268990286019283498271)
                    ·
                      rfl

theorem cell23_3238305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_3238305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238305 prefixEnd_3238305 := by exact prefixLift 3238305
  have htrace : WordTrace (prefixWord ++ tailWord_3238305) baseStart_3238305 baseEnd_3238305 := by
    simpa [prefixWord, tailWord_3238305, baseEnd_3238305] using wordTrace_append hprefix tailTrace_3238305
  have hstable : (prefixWord ++ tailWord_3238305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238305).length < 2 ^ (prefixWord ++ tailWord_3238305).sum := by decide
  have hdescent : baseEnd_3238305 < baseStart_3238305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238321 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 2, 3, 2]
def baseStart_3238321 : Nat := 118140960795 + 3238321 * 2 ^ 59
def prefixEnd_3238321 : Nat := 4983230072969 + 3 ^ 40 * 3238321 * 2
def baseEnd_3238321 : Nat := 1662815186548529787894739

theorem tailTrace_3238321 : CollatzResearch.WordTrace tailWord_3238321 prefixEnd_3238321 1662815186548529787894739 := by
  unfold tailWord_3238321
  simp only [CollatzResearch.WordTrace]
  refine ⟨118111270101123553040458817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78740846734082368693639211 118111270101123553040458817)
  ·
    refine ⟨88583452575842664780344113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118111270101123553040458817 88583452575842664780344113)
    ·
      refine ⟨66437589431881998585258085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88583452575842664780344113 66437589431881998585258085)
      ·
        refine ⟨12457048018477874734735891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66437589431881998585258085 12457048018477874734735891)
        ·
          refine ⟨18685572027716812102103837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12457048018477874734735891 18685572027716812102103837)
          ·
            refine ⟨7007089510393804538288939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18685572027716812102103837 7007089510393804538288939)
            ·
              refine ⟨10510634265590706807433409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7007089510393804538288939 10510634265590706807433409)
              ·
                refine ⟨7882975699193030105575057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10510634265590706807433409 7882975699193030105575057)
                ·
                  refine ⟨5912231774394772579181293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7882975699193030105575057 5912231774394772579181293)
                  ·
                    refine ⟨2217086915398039717192985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5912231774394772579181293 2217086915398039717192985)
                    ·
                      refine ⟨1662815186548529787894739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217086915398039717192985 1662815186548529787894739)
                      ·
                        rfl

theorem cell23_3238321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_3238321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238321 prefixEnd_3238321 := by exact prefixLift 3238321
  have htrace : WordTrace (prefixWord ++ tailWord_3238321) baseStart_3238321 baseEnd_3238321 := by
    simpa [prefixWord, tailWord_3238321, baseEnd_3238321] using wordTrace_append hprefix tailTrace_3238321
  have hstable : (prefixWord ++ tailWord_3238321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238321).length < 2 ^ (prefixWord ++ tailWord_3238321).sum := by decide
  have hdescent : baseEnd_3238321 < baseStart_3238321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238347 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 4]
def baseStart_3238347 : Nat := 118140960795 + 3238347 * 2 ^ 59
def prefixEnd_3238347 : Nat := 4983230072969 + 3 ^ 40 * 3238347 * 2
def baseEnd_3238347 : Nat := 1662828537045546686169619

theorem tailTrace_3238347 : CollatzResearch.WordTrace tailWord_3238347 prefixEnd_3238347 1662828537045546686169619 := by
  unfold tailWord_3238347
  simp only [CollatzResearch.WordTrace]
  refine ⟨118112218399029359480905295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78741478932686239653936863 118112218399029359480905295)
  ·
    refine ⟨177168327598544039221357943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118112218399029359480905295 177168327598544039221357943)
    ·
      refine ⟨265752491397816058832036915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177168327598544039221357943 265752491397816058832036915)
      ·
        refine ⟨398628737096724088248055373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265752491397816058832036915 398628737096724088248055373)
        ·
          refine ⟨149485776411271533093020765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398628737096724088248055373 149485776411271533093020765)
          ·
            refine ⟨56057166154226824909882787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149485776411271533093020765 56057166154226824909882787)
            ·
              refine ⟨84085749231340237364824181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56057166154226824909882787 84085749231340237364824181)
              ·
                refine ⟨7883038990438147252952267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84085749231340237364824181 7883038990438147252952267)
                ·
                  refine ⟨11824558485657220879428401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7883038990438147252952267 11824558485657220879428401)
                  ·
                    refine ⟨8868418864242915659571301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11824558485657220879428401 8868418864242915659571301)
                    ·
                      refine ⟨1662828537045546686169619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8868418864242915659571301 1662828537045546686169619)
                      ·
                        rfl

theorem cell23_3238347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 4].length) (baseStart_3238347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238347 prefixEnd_3238347 := by exact prefixLift 3238347
  have htrace : WordTrace (prefixWord ++ tailWord_3238347) baseStart_3238347 baseEnd_3238347 := by
    simpa [prefixWord, tailWord_3238347, baseEnd_3238347] using wordTrace_append hprefix tailTrace_3238347
  have hstable : (prefixWord ++ tailWord_3238347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238347).length < 2 ^ (prefixWord ++ tailWord_3238347).sum := by decide
  have hdescent : baseEnd_3238347 < baseStart_3238347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238348 : List Nat := [2, 2, 1, 4, 4, 1, 1, 2, 1, 5]
def baseStart_3238348 : Nat := 118140960795 + 3238348 * 2 ^ 59
def prefixEnd_3238348 : Nat := 4983230072969 + 3 ^ 40 * 3238348 * 2
def baseEnd_3238348 : Nat := 554276350175400394085705

theorem tailTrace_3238348 : CollatzResearch.WordTrace tailWord_3238348 prefixEnd_3238348 554276350175400394085705 := by
  unfold tailWord_3238348
  simp only [CollatzResearch.WordTrace]
  refine ⟨59056127436012868325845849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78741503248017157767794465 59056127436012868325845849)
  ·
    refine ⟨44292095577009651244384387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59056127436012868325845849 44292095577009651244384387)
    ·
      refine ⟨66438143365514476866576581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44292095577009651244384387 66438143365514476866576581)
      ·
        refine ⟨12457151881033964412483109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66438143365514476866576581 12457151881033964412483109)
        ·
          refine ⟨2335715977693868327340583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12457151881033964412483109 2335715977693868327340583)
          ·
            refine ⟨3503573966540802491010875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2335715977693868327340583 3503573966540802491010875)
            ·
              refine ⟨5255360949811203736516313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503573966540802491010875 5255360949811203736516313)
              ·
                refine ⟨3941520712358402802387235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5255360949811203736516313 3941520712358402802387235)
                ·
                  refine ⟨5912281068537604203580853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941520712358402802387235 5912281068537604203580853)
                  ·
                    refine ⟨554276350175400394085705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5912281068537604203580853 554276350175400394085705)
                    ·
                      rfl

theorem cell23_3238348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_3238348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238348 prefixEnd_3238348 := by exact prefixLift 3238348
  have htrace : WordTrace (prefixWord ++ tailWord_3238348) baseStart_3238348 baseEnd_3238348 := by
    simpa [prefixWord, tailWord_3238348, baseEnd_3238348] using wordTrace_append hprefix tailTrace_3238348
  have hstable : (prefixWord ++ tailWord_3238348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238348).length < 2 ^ (prefixWord ++ tailWord_3238348).sum := by decide
  have hdescent : baseEnd_3238348 < baseStart_3238348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238357 : List Nat := [1, 3, 2, 3, 1, 2, 2, 9]
def baseStart_3238357 : Nat := 118140960795 + 3238357 * 2 ^ 59
def prefixEnd_3238357 : Nat := 4983230072969 + 3 ^ 40 * 3238357 * 2
def baseEnd_3238357 : Nat := 61586432290818209149799

theorem tailTrace_3238357 : CollatzResearch.WordTrace tailWord_3238357 prefixEnd_3238357 61586432290818209149799 := by
  unfold tailWord_3238357
  simp only [CollatzResearch.WordTrace]
  refine ⟨118112583128993131188769325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78741722085995420792512883 118112583128993131188769325)
  ·
    refine ⟨44292218673372424195788497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118112583128993131188769325 44292218673372424195788497)
    ·
      refine ⟨33219164005029318146841373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44292218673372424195788497 33219164005029318146841373)
      ·
        refine ⟨12457186501885994305065515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33219164005029318146841373 12457186501885994305065515)
        ·
          refine ⟨18685779752828991457598273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12457186501885994305065515 18685779752828991457598273)
          ·
            refine ⟨14014334814621743593198705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18685779752828991457598273 14014334814621743593198705)
            ·
              refine ⟨10510751110966307694899029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14014334814621743593198705 10510751110966307694899029)
              ·
                refine ⟨61586432290818209149799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10510751110966307694899029 61586432290818209149799)
                ·
                  rfl

theorem cell23_3238357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 9].length) (baseStart_3238357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238357 prefixEnd_3238357 := by exact prefixLift 3238357
  have htrace : WordTrace (prefixWord ++ tailWord_3238357) baseStart_3238357 baseEnd_3238357 := by
    simpa [prefixWord, tailWord_3238357, baseEnd_3238357] using wordTrace_append hprefix tailTrace_3238357
  have hstable : (prefixWord ++ tailWord_3238357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238357).length < 2 ^ (prefixWord ++ tailWord_3238357).sum := by decide
  have hdescent : baseEnd_3238357 < baseStart_3238357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238368 : List Nat := [2, 1, 1, 3, 1, 1, 4, 5, 1, 2, 2]
def baseStart_3238368 : Nat := 118140960795 + 3238368 * 2 ^ 59
def prefixEnd_3238368 : Nat := 4983230072969 + 3 ^ 40 * 3238368 * 2
def baseEnd_3238368 : Nat := 1662839320139291104007023

theorem tailTrace_3238368 : CollatzResearch.WordTrace tailWord_3238368 prefixEnd_3238368 1662839320139291104007023 := by
  unfold tailWord_3238368
  simp only [CollatzResearch.WordTrace]
  refine ⟨59056492165976640033709879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78741989554635520044946505 59056492165976640033709879)
  ·
    refine ⟨88584738248964960050564819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59056492165976640033709879 88584738248964960050564819)
    ·
      refine ⟨132877107373447440075847229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88584738248964960050564819 132877107373447440075847229)
      ·
        refine ⟨49828915265042790028442711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132877107373447440075847229 49828915265042790028442711)
        ·
          refine ⟨74743372897564185042664067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49828915265042790028442711 74743372897564185042664067)
          ·
            refine ⟨112115059346346277563996101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74743372897564185042664067 112115059346346277563996101)
            ·
              refine ⟨21021573627439927043249269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112115059346346277563996101 21021573627439927043249269)
              ·
                refine ⟨1970772527572493160304619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21021573627439927043249269 1970772527572493160304619)
                ·
                  refine ⟨2956158791358739740456929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970772527572493160304619 2956158791358739740456929)
                  ·
                    refine ⟨2217119093519054805342697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2956158791358739740456929 2217119093519054805342697)
                    ·
                      refine ⟨1662839320139291104007023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217119093519054805342697 1662839320139291104007023)
                      ·
                        rfl

theorem cell23_3238368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_3238368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238368 prefixEnd_3238368 := by exact prefixLift 3238368
  have htrace : WordTrace (prefixWord ++ tailWord_3238368) baseStart_3238368 baseEnd_3238368 := by
    simpa [prefixWord, tailWord_3238368, baseEnd_3238368] using wordTrace_append hprefix tailTrace_3238368
  have hstable : (prefixWord ++ tailWord_3238368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238368).length < 2 ^ (prefixWord ++ tailWord_3238368).sum := by decide
  have hdescent : baseEnd_3238368 < baseStart_3238368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238371 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 1, 1, 5]
def baseStart_3238371 : Nat := 118140960795 + 3238371 * 2 ^ 59
def prefixEnd_3238371 : Nat := 4983230072969 + 3 ^ 40 * 3238371 * 2
def baseEnd_3238371 : Nat := 1662840860581254592269509

theorem tailTrace_3238371 : CollatzResearch.WordTrace tailWord_3238371 prefixEnd_3238371 1662840860581254592269509 := by
  unfold tailWord_3238371
  simp only [CollatzResearch.WordTrace]
  refine ⟨118113093750942411579778967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78742062500628274386519311 118113093750942411579778967)
  ·
    refine ⟨177169640626413617369668451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118113093750942411579778967 177169640626413617369668451)
    ·
      refine ⟨265754460939620426054502677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177169640626413617369668451 265754460939620426054502677)
      ·
        refine ⟨12457240356544707471304813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 265754460939620426054502677 12457240356544707471304813)
        ·
          refine ⟨4671465133704265301739305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12457240356544707471304813 4671465133704265301739305)
          ·
            refine ⟨3503598850278198976304479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4671465133704265301739305 3503598850278198976304479)
            ·
              refine ⟨5255398275417298464456719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503598850278198976304479 5255398275417298464456719)
              ·
                refine ⟨7883097413125947696685079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5255398275417298464456719 7883097413125947696685079)
                ·
                  refine ⟨11824646119688921545027619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7883097413125947696685079 11824646119688921545027619)
                  ·
                    refine ⟨17736969179533382317541429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11824646119688921545027619 17736969179533382317541429)
                    ·
                      refine ⟨1662840860581254592269509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17736969179533382317541429 1662840860581254592269509)
                      ·
                        rfl

theorem cell23_3238371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_3238371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238371 prefixEnd_3238371 := by exact prefixLift 3238371
  have htrace : WordTrace (prefixWord ++ tailWord_3238371) baseStart_3238371 baseEnd_3238371 := by
    simpa [prefixWord, tailWord_3238371, baseEnd_3238371] using wordTrace_append hprefix tailTrace_3238371
  have hstable : (prefixWord ++ tailWord_3238371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238371).length < 2 ^ (prefixWord ++ tailWord_3238371).sum := by decide
  have hdescent : baseEnd_3238371 < baseStart_3238371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238401 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_3238401 : Nat := 118140960795 + 3238401 * 2 ^ 59
def prefixEnd_3238401 : Nat := 4983230072969 + 3 ^ 40 * 3238401 * 2
def baseEnd_3238401 : Nat := 1662856265000889474894371

theorem tailTrace_3238401 : CollatzResearch.WordTrace tailWord_3238401 prefixEnd_3238401 1662856265000889474894371 := by
  unfold tailWord_3238401
  simp only [CollatzResearch.WordTrace]
  refine ⟨118114187940833726703371057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78742791960555817802247371 118114187940833726703371057)
  ·
    refine ⟨88585640955625295027528293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118114187940833726703371057 88585640955625295027528293)
    ·
      refine ⟨16609807679179742817661555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88585640955625295027528293 16609807679179742817661555)
      ·
        refine ⟨24914711518769614226492333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16609807679179742817661555 24914711518769614226492333)
        ·
          refine ⟨9343016819538605334934625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24914711518769614226492333 9343016819538605334934625)
          ·
            refine ⟨7007262614653954001200969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9343016819538605334934625 7007262614653954001200969)
            ·
              refine ⟨5255446960990465500900727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7007262614653954001200969 5255446960990465500900727)
              ·
                refine ⟨7883170441485698251351091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5255446960990465500900727 7883170441485698251351091)
                ·
                  refine ⟨11824755662228547377026637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7883170441485698251351091 11824755662228547377026637)
                  ·
                    refine ⟨4434283373335705266384989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11824755662228547377026637 4434283373335705266384989)
                    ·
                      refine ⟨1662856265000889474894371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4434283373335705266384989 1662856265000889474894371)
                      ·
                        rfl

theorem cell23_3238401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_3238401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238401 prefixEnd_3238401 := by exact prefixLift 3238401
  have htrace : WordTrace (prefixWord ++ tailWord_3238401) baseStart_3238401 baseEnd_3238401 := by
    simpa [prefixWord, tailWord_3238401, baseEnd_3238401] using wordTrace_append hprefix tailTrace_3238401
  have hstable : (prefixWord ++ tailWord_3238401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238401).length < 2 ^ (prefixWord ++ tailWord_3238401).sum := by decide
  have hdescent : baseEnd_3238401 < baseStart_3238401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238411 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 3, 3, 2]
def baseStart_3238411 : Nat := 118140960795 + 3238411 * 2 ^ 59
def prefixEnd_3238411 : Nat := 4983230072969 + 3 ^ 40 * 3238411 * 2
def baseEnd_3238411 : Nat := 1662861399807434435769325

theorem tailTrace_3238411 : CollatzResearch.WordTrace tailWord_3238411 prefixEnd_3238411 1662861399807434435769325 := by
  unfold tailWord_3238411
  simp only [CollatzResearch.WordTrace]
  refine ⟨118114552670797498411235087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78743035113864998940823391 118114552670797498411235087)
  ·
    refine ⟨177171829006196247616852631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118114552670797498411235087 177171829006196247616852631)
    ·
      refine ⟨265757743509294371425278947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177171829006196247616852631 265757743509294371425278947)
      ·
        refine ⟨398636615263941557137918421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265757743509294371425278947 398636615263941557137918421)
        ·
          refine ⟨9343045670248630245419963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 398636615263941557137918421 9343045670248630245419963)
          ·
            refine ⟨14014568505372945368129945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9343045670248630245419963 14014568505372945368129945)
            ·
              refine ⟨10510926379029709026097459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14014568505372945368129945 10510926379029709026097459)
              ·
                refine ⟨15766389568544563539146189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10510926379029709026097459 15766389568544563539146189)
                ·
                  refine ⟨5912396088204211327179821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15766389568544563539146189 5912396088204211327179821)
                  ·
                    refine ⟨2217148533076579247692433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5912396088204211327179821 2217148533076579247692433)
                    ·
                      refine ⟨1662861399807434435769325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217148533076579247692433 1662861399807434435769325)
                      ·
                        rfl

theorem cell23_3238411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 3, 2].length) (baseStart_3238411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238411 prefixEnd_3238411 := by exact prefixLift 3238411
  have htrace : WordTrace (prefixWord ++ tailWord_3238411) baseStart_3238411 baseEnd_3238411 := by
    simpa [prefixWord, tailWord_3238411, baseEnd_3238411] using wordTrace_append hprefix tailTrace_3238411
  have hstable : (prefixWord ++ tailWord_3238411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238411).length < 2 ^ (prefixWord ++ tailWord_3238411).sum := by decide
  have hdescent : baseEnd_3238411 < baseStart_3238411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238428 : List Nat := [2, 2, 3, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_3238428 : Nat := 118140960795 + 3238428 * 2 ^ 59
def prefixEnd_3238428 : Nat := 4983230072969 + 3 ^ 40 * 3238428 * 2
def baseEnd_3238428 : Nat := 1662870128978560869256747

theorem tailTrace_3238428 : CollatzResearch.WordTrace tailWord_3238428 prefixEnd_3238428 1662870128978560869256747 := by
  unfold tailWord_3238428
  simp only [CollatzResearch.WordTrace]
  refine ⟨59057586355867955157301969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78743448474490606876402625 59057586355867955157301969)
  ·
    refine ⟨44293189766900966367976477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59057586355867955157301969 44293189766900966367976477)
    ·
      refine ⟨16609946162587862387991179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44293189766900966367976477 16609946162587862387991179)
      ·
        refine ⟨24914919243881793581986769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16609946162587862387991179 24914919243881793581986769)
        ·
          refine ⟨18686189432911345186490077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24914919243881793581986769 18686189432911345186490077)
          ·
            refine ⟨7007321037341754444933779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18686189432911345186490077 7007321037341754444933779)
            ·
              refine ⟨10510981556012631667400669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7007321037341754444933779 10510981556012631667400669)
              ·
                refine ⟨3941618083504736875275251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10510981556012631667400669 3941618083504736875275251)
                ·
                  refine ⟨5912427125257105312912877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941618083504736875275251 5912427125257105312912877)
                  ·
                    refine ⟨2217160171971414492342329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5912427125257105312912877 2217160171971414492342329)
                    ·
                      refine ⟨1662870128978560869256747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217160171971414492342329 1662870128978560869256747)
                      ·
                        rfl

theorem cell23_3238428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_3238428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238428 prefixEnd_3238428 := by exact prefixLift 3238428
  have htrace : WordTrace (prefixWord ++ tailWord_3238428) baseStart_3238428 baseEnd_3238428 := by
    simpa [prefixWord, tailWord_3238428, baseEnd_3238428] using wordTrace_append hprefix tailTrace_3238428
  have hstable : (prefixWord ++ tailWord_3238428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238428).length < 2 ^ (prefixWord ++ tailWord_3238428).sum := by decide
  have hdescent : baseEnd_3238428 < baseStart_3238428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238452 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_3238452 : Nat := 118140960795 + 3238452 * 2 ^ 59
def prefixEnd_3238452 : Nat := 4983230072969 + 3 ^ 40 * 3238452 * 2
def baseEnd_3238452 : Nat := 1662882452514268775356637

theorem tailTrace_3238452 : CollatzResearch.WordTrace tailWord_3238452 prefixEnd_3238452 1662882452514268775356637 := by
  unfold tailWord_3238452
  simp only [CollatzResearch.WordTrace]
  refine ⟨59058024031824481206738805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78744032042432641608985073 59058024031824481206738805)
  ·
    refine ⟨5536689752983545113131763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59058024031824481206738805 5536689752983545113131763)
    ·
      refine ⟨8305034629475317669697645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5536689752983545113131763 8305034629475317669697645)
      ·
        refine ⟨3114387986053244126136617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8305034629475317669697645 3114387986053244126136617)
        ·
          refine ⟨2335790989539933094602463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3114387986053244126136617 2335790989539933094602463)
          ·
            refine ⟨3503686484309899641903695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2335790989539933094602463 3503686484309899641903695)
            ·
              refine ⟨5255529726464849462855543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503686484309899641903695 5255529726464849462855543)
              ·
                refine ⟨7883294589697274194283315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5255529726464849462855543 7883294589697274194283315)
                ·
                  refine ⟨11824941884545911291424973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7883294589697274194283315 11824941884545911291424973)
                  ·
                    refine ⟨4434353206704716734284365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11824941884545911291424973 4434353206704716734284365)
                    ·
                      refine ⟨1662882452514268775356637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4434353206704716734284365 1662882452514268775356637)
                      ·
                        rfl

theorem cell23_3238452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_3238452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238452 prefixEnd_3238452 := by exact prefixLift 3238452
  have htrace : WordTrace (prefixWord ++ tailWord_3238452) baseStart_3238452 baseEnd_3238452 := by
    simpa [prefixWord, tailWord_3238452, baseEnd_3238452] using wordTrace_append hprefix tailTrace_3238452
  have hstable : (prefixWord ++ tailWord_3238452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238452).length < 2 ^ (prefixWord ++ tailWord_3238452).sum := by decide
  have hdescent : baseEnd_3238452 < baseStart_3238452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238458 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2]
def baseStart_3238458 : Nat := 118140960795 + 3238458 * 2 ^ 59
def prefixEnd_3238458 : Nat := 4983230072969 + 3 ^ 40 * 3238458 * 2
def baseEnd_3238458 : Nat := 1662885533398195751881609

theorem tailTrace_3238458 : CollatzResearch.WordTrace tailWord_3238458 prefixEnd_3238458 1662885533398195751881609 := by
  unfold tailWord_3238458
  simp only [CollatzResearch.WordTrace]
  refine ⟨29529066725406806359549007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78744177934418150292130685 29529066725406806359549007)
  ·
    refine ⟨44293600088110209539323511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29529066725406806359549007 44293600088110209539323511)
    ·
      refine ⟨66440400132165314308985267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44293600088110209539323511 66440400132165314308985267)
      ·
        refine ⟨99660600198247971463477901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66440400132165314308985267 99660600198247971463477901)
        ·
          refine ⟨37372725074342989298804213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99660600198247971463477901 37372725074342989298804213)
          ·
            refine ⟨3503692975719655246762895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37372725074342989298804213 3503692975719655246762895)
            ·
              refine ⟨5255539463579482870144343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503692975719655246762895 5255539463579482870144343)
              ·
                refine ⟨7883309195369224305216515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5255539463579482870144343 7883309195369224305216515)
                ·
                  refine ⟨11824963793053836457824773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7883309195369224305216515 11824963793053836457824773)
                  ·
                    refine ⟨2217180711197594335842145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11824963793053836457824773 2217180711197594335842145)
                    ·
                      refine ⟨1662885533398195751881609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217180711197594335842145 1662885533398195751881609)
                      ·
                        rfl

theorem cell23_3238458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2].length) (baseStart_3238458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238458 prefixEnd_3238458 := by exact prefixLift 3238458
  have htrace : WordTrace (prefixWord ++ tailWord_3238458) baseStart_3238458 baseEnd_3238458 := by
    simpa [prefixWord, tailWord_3238458, baseEnd_3238458] using wordTrace_append hprefix tailTrace_3238458
  have hstable : (prefixWord ++ tailWord_3238458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238458).length < 2 ^ (prefixWord ++ tailWord_3238458).sum := by decide
  have hdescent : baseEnd_3238458 < baseStart_3238458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238462 : List Nat := [4, 2, 1, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_3238462 : Nat := 118140960795 + 3238462 * 2 ^ 59
def prefixEnd_3238462 : Nat := 4983230072969 + 3 ^ 40 * 3238462 * 2
def baseEnd_3238462 : Nat := 1662887587320813736231591

theorem tailTrace_3238462 : CollatzResearch.WordTrace tailWord_3238462 prefixEnd_3238462 1662887587320813736231591 := by
  unfold tailWord_3238462
  simp only [CollatzResearch.WordTrace]
  refine ⟨14764551599201591765167705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78744275195741822747561093 14764551599201591765167705)
  ·
    refine ⟨11073413699401193823875779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14764551599201591765167705 11073413699401193823875779)
    ·
      refine ⟨16610120549101790735813669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11073413699401193823875779 16610120549101790735813669)
      ·
        refine ⟨3114397602956585762965063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16610120549101790735813669 3114397602956585762965063)
        ·
          refine ⟨4671596404434878644447595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3114397602956585762965063 4671596404434878644447595)
          ·
            refine ⟨7007394606652317966671393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4671596404434878644447595 7007394606652317966671393)
            ·
              refine ⟨5255545954989238475003545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7007394606652317966671393 5255545954989238475003545)
              ·
                refine ⟨3941659466241928856252659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5255545954989238475003545 3941659466241928856252659)
                ·
                  refine ⟨5912489199362893284378989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941659466241928856252659 5912489199362893284378989)
                  ·
                    refine ⟨2217183449761084981642121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5912489199362893284378989 2217183449761084981642121)
                    ·
                      refine ⟨1662887587320813736231591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217183449761084981642121 1662887587320813736231591)
                      ·
                        rfl

theorem cell23_3238462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_3238462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238462 prefixEnd_3238462 := by exact prefixLift 3238462
  have htrace : WordTrace (prefixWord ++ tailWord_3238462) baseStart_3238462 baseEnd_3238462 := by
    simpa [prefixWord, tailWord_3238462, baseEnd_3238462] using wordTrace_append hprefix tailTrace_3238462
  have hstable : (prefixWord ++ tailWord_3238462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238462).length < 2 ^ (prefixWord ++ tailWord_3238462).sum := by decide
  have hdescent : baseEnd_3238462 < baseStart_3238462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238481 : List Nat := [1, 2, 2, 1, 3, 3, 3, 3, 5]
def baseStart_3238481 : Nat := 118140960795 + 3238481 * 2 ^ 59
def prefixEnd_3238481 : Nat := 4983230072969 + 3 ^ 40 * 3238481 * 2
def baseEnd_3238481 : Nat := 184766371494805462432667

theorem tailTrace_3238481 : CollatzResearch.WordTrace tailWord_3238481 prefixEnd_3238481 184766371494805462432667 := by
  unfold tailWord_3238481
  simp only [CollatzResearch.WordTrace]
  refine ⟨118117105780543900366283297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78744737187029266910855531 118117105780543900366283297)
  ·
    refine ⟨88587829335407925274712473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118117105780543900366283297 88587829335407925274712473)
    ·
      refine ⟨66440872001555943956034355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88587829335407925274712473 66440872001555943956034355)
      ·
        refine ⟨99661308002333915934051533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66440872001555943956034355 99661308002333915934051533)
        ·
          refine ⟨37372990500875218475269325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99661308002333915934051533 37372990500875218475269325)
          ·
            refine ⟨14014871437828206928225997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37372990500875218475269325 14014871437828206928225997)
            ·
              refine ⟨5255576789185577598084749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14014871437828206928225997 5255576789185577598084749)
              ·
                refine ⟨1970841295944591599281781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5255576789185577598084749 1970841295944591599281781)
                ·
                  refine ⟨184766371494805462432667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1970841295944591599281781 184766371494805462432667)
                  ·
                    rfl

theorem cell23_3238481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 5].length) (baseStart_3238481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238481 prefixEnd_3238481 := by exact prefixLift 3238481
  have htrace : WordTrace (prefixWord ++ tailWord_3238481) baseStart_3238481 baseEnd_3238481 := by
    simpa [prefixWord, tailWord_3238481, baseEnd_3238481] using wordTrace_append hprefix tailTrace_3238481
  have hstable : (prefixWord ++ tailWord_3238481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238481).length < 2 ^ (prefixWord ++ tailWord_3238481).sum := by decide
  have hdescent : baseEnd_3238481 < baseStart_3238481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238507 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 2, 8]
def baseStart_3238507 : Nat := 118140960795 + 3238507 * 2 ^ 59
def prefixEnd_3238507 : Nat := 4983230072969 + 3 ^ 40 * 3238507 * 2
def baseEnd_3238507 : Nat := 554303564650088686722961

theorem tailTrace_3238507 : CollatzResearch.WordTrace tailWord_3238507 prefixEnd_3238507 554303564650088686722961 := by
  unfold tailWord_3238507
  simp only [CollatzResearch.WordTrace]
  refine ⟨118118054078449706806729775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78745369385633137871153183 118118054078449706806729775)
  ·
    refine ⟨177177081117674560210094663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118118054078449706806729775 177177081117674560210094663)
    ·
      refine ⟨265765621676511840315141995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177177081117674560210094663 265765621676511840315141995)
      ·
        refine ⟨398648432514767760472712993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265765621676511840315141995 398648432514767760472712993)
        ·
          refine ⟨298986324386075820354534745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398648432514767760472712993 298986324386075820354534745)
          ·
            refine ⟨224239743289556865265901059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298986324386075820354534745 224239743289556865265901059)
            ·
              refine ⟨336359614934335297898851589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224239743289556865265901059 336359614934335297898851589)
              ·
                refine ⟨63067427800187868356034673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336359614934335297898851589 63067427800187868356034673)
                ·
                  refine ⟨47300570850140901267026005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63067427800187868356034673 47300570850140901267026005)
                  ·
                    refine ⟨554303564650088686722961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47300570850140901267026005 554303564650088686722961)
                    ·
                      rfl

theorem cell23_3238507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 8].length) (baseStart_3238507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238507 prefixEnd_3238507 := by exact prefixLift 3238507
  have htrace : WordTrace (prefixWord ++ tailWord_3238507) baseStart_3238507 baseEnd_3238507 := by
    simpa [prefixWord, tailWord_3238507, baseEnd_3238507] using wordTrace_append hprefix tailTrace_3238507
  have hstable : (prefixWord ++ tailWord_3238507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238507).length < 2 ^ (prefixWord ++ tailWord_3238507).sum := by decide
  have hdescent : baseEnd_3238507 < baseStart_3238507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238548 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3238548 : Nat := 118140960795 + 3238548 * 2 ^ 59
def prefixEnd_3238548 : Nat := 4983230072969 + 3 ^ 40 * 3238548 * 2
def baseEnd_3238548 : Nat := 1662931746657100399756195

theorem tailTrace_3238548 : CollatzResearch.WordTrace tailWord_3238548 prefixEnd_3238548 1662931746657100399756195 := by
  unfold tailWord_3238548
  simp only [CollatzResearch.WordTrace]
  refine ⟨59059774735650585404486149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78746366314200780539314865 59059774735650585404486149)
  ·
    refine ⟨11073707762934484763341153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59059774735650585404486149 11073707762934484763341153)
    ·
      refine ⟨8305280822200863572505865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11073707762934484763341153 8305280822200863572505865)
      ·
        refine ⟨6228960616650647679379399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8305280822200863572505865 6228960616650647679379399)
        ·
          refine ⟨9343440924975971519069099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6228960616650647679379399 9343440924975971519069099)
          ·
            refine ⟨14015161387463957278603649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9343440924975971519069099 14015161387463957278603649)
            ·
              refine ⟨10511371040597967958952737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14015161387463957278603649 10511371040597967958952737)
              ·
                refine ⟨7883528280448475969214553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10511371040597967958952737 7883528280448475969214553)
                ·
                  refine ⟨5912646210336356976910915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7883528280448475969214553 5912646210336356976910915)
                  ·
                    refine ⟨8868969315504535465366373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5912646210336356976910915 8868969315504535465366373)
                    ·
                      refine ⟨1662931746657100399756195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8868969315504535465366373 1662931746657100399756195)
                      ·
                        rfl

theorem cell23_3238548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3238548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238548 prefixEnd_3238548 := by exact prefixLift 3238548
  have htrace : WordTrace (prefixWord ++ tailWord_3238548) baseStart_3238548 baseEnd_3238548 := by
    simpa [prefixWord, tailWord_3238548, baseEnd_3238548] using wordTrace_append hprefix tailTrace_3238548
  have hstable : (prefixWord ++ tailWord_3238548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238548).length < 2 ^ (prefixWord ++ tailWord_3238548).sum := by decide
  have hdescent : baseEnd_3238548 < baseStart_3238548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238551 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 3]
def baseStart_3238551 : Nat := 118140960795 + 3238551 * 2 ^ 59
def prefixEnd_3238551 : Nat := 4983230072969 + 3 ^ 40 * 3238551 * 2
def baseEnd_3238551 : Nat := 1662933287099063888018681

theorem tailTrace_3238551 : CollatzResearch.WordTrace tailWord_3238551 prefixEnd_3238551 1662933287099063888018681 := by
  unfold tailWord_3238551
  simp only [CollatzResearch.WordTrace]
  refine ⟨118119658890290302321331507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78746439260193534880887671 118119658890290302321331507)
  ·
    refine ⟨177179488335435453481997261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118119658890290302321331507 177179488335435453481997261)
    ·
      refine ⟨66442308125788295055748973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177179488335435453481997261 66442308125788295055748973)
      ·
        refine ⟨24915865547170610645905865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66442308125788295055748973 24915865547170610645905865)
        ·
          refine ⟨18686899160377957984429399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24915865547170610645905865 18686899160377957984429399)
          ·
            refine ⟨28030348740566936976644099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18686899160377957984429399 28030348740566936976644099)
            ·
              refine ⟨42045523110850405464966149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28030348740566936976644099 42045523110850405464966149)
              ·
                refine ⟨7883535583284451024681153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42045523110850405464966149 7883535583284451024681153)
                ·
                  refine ⟨5912651687463338268510865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7883535583284451024681153 5912651687463338268510865)
                  ·
                    refine ⟨4434488765597503701383149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5912651687463338268510865 4434488765597503701383149)
                    ·
                      refine ⟨1662933287099063888018681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4434488765597503701383149 1662933287099063888018681)
                      ·
                        rfl

theorem cell23_3238551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_3238551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238551 prefixEnd_3238551 := by exact prefixLift 3238551
  have htrace : WordTrace (prefixWord ++ tailWord_3238551) baseStart_3238551 baseEnd_3238551 := by
    simpa [prefixWord, tailWord_3238551, baseEnd_3238551] using wordTrace_append hprefix tailTrace_3238551
  have hstable : (prefixWord ++ tailWord_3238551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238551).length < 2 ^ (prefixWord ++ tailWord_3238551).sum := by decide
  have hdescent : baseEnd_3238551 < baseStart_3238551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238558 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_3238558 : Nat := 118140960795 + 3238558 * 2 ^ 59
def prefixEnd_3238558 : Nat := 4983230072969 + 3 ^ 40 * 3238558 * 2
def baseEnd_3238558 : Nat := 554312293821215120210383

theorem tailTrace_3238558 : CollatzResearch.WordTrace tailWord_3238558 prefixEnd_3238558 554312293821215120210383 := by
  unfold tailWord_3238558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14764989275158117814604541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78746609467509961677890885 14764989275158117814604541)
  ·
    refine ⟨5536870978184294180476703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14764989275158117814604541 5536870978184294180476703)
    ·
      refine ⟨8305306467276441270715055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5536870978184294180476703 8305306467276441270715055)
      ·
        refine ⟨12457959700914661906072583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8305306467276441270715055 12457959700914661906072583)
        ·
          refine ⟨18686939551371992859108875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12457959700914661906072583 18686939551371992859108875)
          ·
            refine ⟨28030409327057989288663313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18686939551371992859108875 28030409327057989288663313)
            ·
              refine ⟨21022806995293491966497485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28030409327057989288663313 21022806995293491966497485)
              ·
                refine ⟨7883552623235059487436557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21022806995293491966497485 7883552623235059487436557)
                ·
                  refine ⟨2956332233713147307788709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7883552623235059487436557 2956332233713147307788709)
                  ·
                    refine ⟨554312293821215120210383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2956332233713147307788709 554312293821215120210383)
                    ·
                      rfl

theorem cell23_3238558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_3238558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238558 prefixEnd_3238558 := by exact prefixLift 3238558
  have htrace : WordTrace (prefixWord ++ tailWord_3238558) baseStart_3238558 baseEnd_3238558 := by
    simpa [prefixWord, tailWord_3238558, baseEnd_3238558] using wordTrace_append hprefix tailTrace_3238558
  have hstable : (prefixWord ++ tailWord_3238558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238558).length < 2 ^ (prefixWord ++ tailWord_3238558).sum := by decide
  have hdescent : baseEnd_3238558 < baseStart_3238558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238582 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3238582 : Nat := 118140960795 + 3238582 * 2 ^ 59
def prefixEnd_3238582 : Nat := 4983230072969 + 3 ^ 40 * 3238582 * 2
def baseEnd_3238582 : Nat := 1662949204999353266731039

theorem tailTrace_3238582 : CollatzResearch.WordTrace tailWord_3238582 prefixEnd_3238582 1662949204999353266731039 := by
  unfold tailWord_3238582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7382549347073624663481875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78747193035451996410473333 7382549347073624663481875)
  ·
    refine ⟨11073824020610436995222813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7382549347073624663481875 11073824020610436995222813)
    ·
      refine ⟨4152684007728913873208555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11073824020610436995222813 4152684007728913873208555)
      ·
        refine ⟨6229026011593370809812833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4152684007728913873208555 6229026011593370809812833)
        ·
          refine ⟨4671769508695028107359625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6229026011593370809812833 4671769508695028107359625)
          ·
            refine ⟨3503827131521271080519719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4671769508695028107359625 3503827131521271080519719)
            ·
              refine ⟨5255740697281906620779579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503827131521271080519719 5255740697281906620779579)
              ·
                refine ⟨7883611045922859931169369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5255740697281906620779579 7883611045922859931169369)
                ·
                  refine ⟨5912708284442144948377027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7883611045922859931169369 5912708284442144948377027)
                  ·
                    refine ⟨8869062426663217422565541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5912708284442144948377027 8869062426663217422565541)
                    ·
                      refine ⟨1662949204999353266731039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8869062426663217422565541 1662949204999353266731039)
                      ·
                        rfl

theorem cell23_3238582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3238582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238582 prefixEnd_3238582 := by exact prefixLift 3238582
  have htrace : WordTrace (prefixWord ++ tailWord_3238582) baseStart_3238582 baseEnd_3238582 := by
    simpa [prefixWord, tailWord_3238582, baseEnd_3238582] using wordTrace_append hprefix tailTrace_3238582
  have hstable : (prefixWord ++ tailWord_3238582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238582).length < 2 ^ (prefixWord ++ tailWord_3238582).sum := by decide
  have hdescent : baseEnd_3238582 < baseStart_3238582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238615 : List Nat := [1, 1, 3, 2, 1, 4, 2, 4, 1, 1, 3]
def baseStart_3238615 : Nat := 118140960795 + 3238615 * 2 ^ 59
def prefixEnd_3238615 : Nat := 4983230072969 + 3 ^ 40 * 3238615 * 2
def baseEnd_3238615 : Nat := 1662966149860951637618387

theorem tailTrace_3238615 : CollatzResearch.WordTrace tailWord_3238615 prefixEnd_3238615 1662966149860951637618387 := by
  unfold tailWord_3238615
  simp only [CollatzResearch.WordTrace]
  refine ⟨118121993162058441251661299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78747995441372294167774199 118121993162058441251661299)
  ·
    refine ⟨177182989743087661877491949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118121993162058441251661299 177182989743087661877491949)
    ·
      refine ⟨66443621153657873204059481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177182989743087661877491949 66443621153657873204059481)
      ·
        refine ⟨49832715865243404903044611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66443621153657873204059481 49832715865243404903044611)
        ·
          refine ⟨74749073797865107354566917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49832715865243404903044611 74749073797865107354566917)
          ·
            refine ⟨14015451337099707628981297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74749073797865107354566917 14015451337099707628981297)
            ·
              refine ⟨10511588502824780721735973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14015451337099707628981297 10511588502824780721735973)
              ·
                refine ⟨1970922844279646385325495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10511588502824780721735973 1970922844279646385325495)
                ·
                  refine ⟨2956384266419469577988243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970922844279646385325495 2956384266419469577988243)
                  ·
                    refine ⟨4434576399629204366982365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2956384266419469577988243 4434576399629204366982365)
                    ·
                      refine ⟨1662966149860951637618387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4434576399629204366982365 1662966149860951637618387)
                      ·
                        rfl

theorem cell23_3238615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_3238615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238615 prefixEnd_3238615 := by exact prefixLift 3238615
  have htrace : WordTrace (prefixWord ++ tailWord_3238615) baseStart_3238615 baseEnd_3238615 := by
    simpa [prefixWord, tailWord_3238615, baseEnd_3238615] using wordTrace_append hprefix tailTrace_3238615
  have hstable : (prefixWord ++ tailWord_3238615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238615).length < 2 ^ (prefixWord ++ tailWord_3238615).sum := by decide
  have hdescent : baseEnd_3238615 < baseStart_3238615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238638 : List Nat := [4, 1, 2, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_3238638 : Nat := 118140960795 + 3238638 * 2 ^ 59
def prefixEnd_3238638 : Nat := 4983230072969 + 3 ^ 40 * 3238638 * 2
def baseEnd_3238638 : Nat := 1662977959916005047630781

theorem tailTrace_3238638 : CollatzResearch.WordTrace tailWord_3238638 prefixEnd_3238638 1662977959916005047630781 := by
  unfold tailWord_3238638
  simp only [CollatzResearch.WordTrace]
  refine ⟨14765354005121889522468571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78748554693983410786499045 14765354005121889522468571)
  ·
    refine ⟨22148031007682834283702857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14765354005121889522468571 22148031007682834283702857)
    ·
      refine ⟨16611023255762125712777143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22148031007682834283702857 16611023255762125712777143)
      ·
        refine ⟨24916534883643188569165715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16611023255762125712777143 24916534883643188569165715)
        ·
          refine ⟨37374802325464782853748573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24916534883643188569165715 37374802325464782853748573)
          ·
            refine ⟨14015550872049293570155715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37374802325464782853748573 14015550872049293570155715)
            ·
              refine ⟨21023326308073940355233573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14015550872049293570155715 21023326308073940355233573)
              ·
                refine ⟨3941873682763863816606295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21023326308073940355233573 3941873682763863816606295)
                ·
                  refine ⟨5912810524145795724909443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941873682763863816606295 5912810524145795724909443)
                  ·
                    refine ⟨8869215786218693587364165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5912810524145795724909443 8869215786218693587364165)
                    ·
                      refine ⟨1662977959916005047630781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8869215786218693587364165 1662977959916005047630781)
                      ·
                        rfl

theorem cell23_3238638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_3238638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238638 prefixEnd_3238638 := by exact prefixLift 3238638
  have htrace : WordTrace (prefixWord ++ tailWord_3238638) baseStart_3238638 baseEnd_3238638 := by
    simpa [prefixWord, tailWord_3238638, baseEnd_3238638] using wordTrace_append hprefix tailTrace_3238638
  have hstable : (prefixWord ++ tailWord_3238638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238638).length < 2 ^ (prefixWord ++ tailWord_3238638).sum := by decide
  have hdescent : baseEnd_3238638 < baseStart_3238638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238658 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3238658 : Nat := 118140960795 + 3238658 * 2 ^ 59
def prefixEnd_3238658 : Nat := 4983230072969 + 3 ^ 40 * 3238658 * 2
def baseEnd_3238658 : Nat := 1662988229529094969380689

theorem tailTrace_3238658 : CollatzResearch.WordTrace tailWord_3238658 prefixEnd_3238658 1662988229529094969380689 := by
  unfold tailWord_3238658
  simp only [CollatzResearch.WordTrace]
  refine ⟨29530890375225664898869157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78749041000601773063651085 29530890375225664898869157)
  ·
    refine ⟨5537041945354812168537967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29530890375225664898869157 5537041945354812168537967)
    ·
      refine ⟨8305562918032218252806951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5537041945354812168537967 8305562918032218252806951)
      ·
        refine ⟨12458344377048327379210427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8305562918032218252806951 12458344377048327379210427)
        ·
          refine ⟨18687516565572491068815641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12458344377048327379210427 18687516565572491068815641)
          ·
            refine ⟨14015637424179368301611731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18687516565572491068815641 14015637424179368301611731)
            ·
              refine ⟨21023456136269052452417597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14015637424179368301611731 21023456136269052452417597)
              ·
                refine ⟨7883796051100894669656599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21023456136269052452417597 7883796051100894669656599)
                ·
                  refine ⟨11825694076651342004484899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7883796051100894669656599 11825694076651342004484899)
                  ·
                    refine ⟨17738541114977013006727349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11825694076651342004484899 17738541114977013006727349)
                    ·
                      refine ⟨1662988229529094969380689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17738541114977013006727349 1662988229529094969380689)
                      ·
                        rfl

theorem cell23_3238658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3238658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238658 prefixEnd_3238658 := by exact prefixLift 3238658
  have htrace : WordTrace (prefixWord ++ tailWord_3238658) baseStart_3238658 baseEnd_3238658 := by
    simpa [prefixWord, tailWord_3238658, baseEnd_3238658] using wordTrace_append hprefix tailTrace_3238658
  have hstable : (prefixWord ++ tailWord_3238658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238658).length < 2 ^ (prefixWord ++ tailWord_3238658).sum := by decide
  have hdescent : baseEnd_3238658 < baseStart_3238658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238692 : List Nat := [2, 3, 1, 3, 3, 2, 1, 2, 1, 2, 3]
def baseStart_3238692 : Nat := 118140960795 + 3238692 * 2 ^ 59
def prefixEnd_3238692 : Nat := 4983230072969 + 3 ^ 40 * 3238692 * 2
def baseEnd_3238692 : Nat := 1663005687871347836355533

theorem tailTrace_3238692 : CollatzResearch.WordTrace tailWord_3238692 prefixEnd_3238692 1663005687871347836355533 := by
  unfold tailWord_3238692
  simp only [CollatzResearch.WordTrace]
  refine ⟨59062400791389741701107165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78749867721852988934809553 59062400791389741701107165)
  ·
    refine ⟨22148400296771153137915187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59062400791389741701107165 22148400296771153137915187)
    ·
      refine ⟨33222600445156729706872781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22148400296771153137915187 33222600445156729706872781)
      ·
        refine ⟨12458475166933773640077293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33222600445156729706872781 12458475166933773640077293)
        ·
          refine ⟨4671928187600165115028985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12458475166933773640077293 4671928187600165115028985)
          ·
            refine ⟨3503946140700123836271739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4671928187600165115028985 3503946140700123836271739)
            ·
              refine ⟨5255919211050185754407609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503946140700123836271739 5255919211050185754407609)
              ·
                refine ⟨3941939408287639315805707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5255919211050185754407609 3941939408287639315805707)
                ·
                  refine ⟨5912909112431458973708561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941939408287639315805707 5912909112431458973708561)
                  ·
                    refine ⟨4434681834323594230281421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5912909112431458973708561 4434681834323594230281421)
                    ·
                      refine ⟨1663005687871347836355533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4434681834323594230281421 1663005687871347836355533)
                      ·
                        rfl

theorem cell23_3238692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_3238692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238692 prefixEnd_3238692 := by exact prefixLift 3238692
  have htrace : WordTrace (prefixWord ++ tailWord_3238692) baseStart_3238692 baseEnd_3238692 := by
    simpa [prefixWord, tailWord_3238692, baseEnd_3238692] using wordTrace_append hprefix tailTrace_3238692
  have hstable : (prefixWord ++ tailWord_3238692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238692).length < 2 ^ (prefixWord ++ tailWord_3238692).sum := by decide
  have hdescent : baseEnd_3238692 < baseStart_3238692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238728 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 3, 4, 2]
def baseStart_3238728 : Nat := 118140960795 + 3238728 * 2 ^ 59
def prefixEnd_3238728 : Nat := 4983230072969 + 3 ^ 40 * 3238728 * 2
def baseEnd_3238728 : Nat := 1663024173174909695505367

theorem tailTrace_3238728 : CollatzResearch.WordTrace tailWord_3238728 prefixEnd_3238728 1663024173174909695505367 := by
  unfold tailWord_3238728
  simp only [CollatzResearch.WordTrace]
  refine ⟨59063057305324530775262419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78750743073766041033683225 59063057305324530775262419)
  ·
    refine ⟨88594585957986796162893629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59063057305324530775262419 88594585957986796162893629)
    ·
      refine ⟨33222969734245048561085111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88594585957986796162893629 33222969734245048561085111)
      ·
        refine ⟨49834454601367572841627667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33222969734245048561085111 49834454601367572841627667)
        ·
          refine ⟨74751681902051359262441501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49834454601367572841627667 74751681902051359262441501)
          ·
            refine ⟨28031880713269259723415563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74751681902051359262441501 28031880713269259723415563)
            ·
              refine ⟨42047821069903889585123345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28031880713269259723415563 42047821069903889585123345)
              ·
                refine ⟨31535865802427917188842509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42047821069903889585123345 31535865802427917188842509)
                ·
                  refine ⟨11825949675910468945815941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31535865802427917188842509 11825949675910468945815941)
                  ·
                    refine ⟨2217365564233212927340489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11825949675910468945815941 2217365564233212927340489)
                    ·
                      refine ⟨1663024173174909695505367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217365564233212927340489 1663024173174909695505367)
                      ·
                        rfl

theorem cell23_3238728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_3238728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238728 prefixEnd_3238728 := by exact prefixLift 3238728
  have htrace : WordTrace (prefixWord ++ tailWord_3238728) baseStart_3238728 baseEnd_3238728 := by
    simpa [prefixWord, tailWord_3238728, baseEnd_3238728] using wordTrace_append hprefix tailTrace_3238728
  have hstable : (prefixWord ++ tailWord_3238728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238728).length < 2 ^ (prefixWord ++ tailWord_3238728).sum := by decide
  have hdescent : baseEnd_3238728 < baseStart_3238728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238745 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 1, 4, 2]
def baseStart_3238745 : Nat := 118140960795 + 3238745 * 2 ^ 59
def prefixEnd_3238745 : Nat := 4983230072969 + 3 ^ 40 * 3238745 * 2
def baseEnd_3238745 : Nat := 1663032902346036128992789

theorem tailTrace_3238745 : CollatzResearch.WordTrace tailWord_3238745 prefixEnd_3238745 1663032902346036128992789 := by
  unfold tailWord_3238745
  simp only [CollatzResearch.WordTrace]
  refine ⟨118126734651587473453893689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78751156434391648969262459 118126734651587473453893689)
  ·
    refine ⟨88595050988690605090420267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118126734651587473453893689 88595050988690605090420267)
    ·
      refine ⟨132892576483035907635630401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88595050988690605090420267 132892576483035907635630401)
      ·
        refine ⟨99669432362276930726722801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132892576483035907635630401 99669432362276930726722801)
        ·
          refine ⟨74752074271707698045042101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99669432362276930726722801 74752074271707698045042101)
          ·
            refine ⟨7008006962972596691722697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74752074271707698045042101 7008006962972596691722697)
            ·
              refine ⟨5256005222229447518792023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7008006962972596691722697 5256005222229447518792023)
              ·
                refine ⟨7884007833344171278188035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5256005222229447518792023 7884007833344171278188035)
                ·
                  refine ⟨11826011750016256917282053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7884007833344171278188035 11826011750016256917282053)
                  ·
                    refine ⟨2217377203128048171990385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11826011750016256917282053 2217377203128048171990385)
                    ·
                      refine ⟨1663032902346036128992789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217377203128048171990385 1663032902346036128992789)
                      ·
                        rfl

theorem cell23_3238745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 4, 2].length) (baseStart_3238745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238745 prefixEnd_3238745 := by exact prefixLift 3238745
  have htrace : WordTrace (prefixWord ++ tailWord_3238745) baseStart_3238745 baseEnd_3238745 := by
    simpa [prefixWord, tailWord_3238745, baseEnd_3238745] using wordTrace_append hprefix tailTrace_3238745
  have hstable : (prefixWord ++ tailWord_3238745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238745).length < 2 ^ (prefixWord ++ tailWord_3238745).sum := by decide
  have hdescent : baseEnd_3238745 < baseStart_3238745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238751 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 7]
def baseStart_3238751 : Nat := 118140960795 + 3238751 * 2 ^ 59
def prefixEnd_3238751 : Nat := 4983230072969 + 3 ^ 40 * 3238751 * 2
def baseEnd_3238751 : Nat := 184781775914440345057529

theorem tailTrace_3238751 : CollatzResearch.WordTrace tailWord_3238751 prefixEnd_3238751 184781775914440345057529 := by
  unfold tailWord_3238751
  simp only [CollatzResearch.WordTrace]
  refine ⟨118126953489565736478612107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78751302326377157652408071 118126953489565736478612107)
  ·
    refine ⟨177190430234348604717918161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118126953489565736478612107 177190430234348604717918161)
    ·
      refine ⟨132892822675761453538438621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177190430234348604717918161 132892822675761453538438621)
      ·
        refine ⟨49834808503410545076914483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132892822675761453538438621 49834808503410545076914483)
        ·
          refine ⟨74752212755115817615371725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49834808503410545076914483 74752212755115817615371725)
          ·
            refine ⟨28032079783168431605764397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74752212755115817615371725 28032079783168431605764397)
            ·
              refine ⟨10512029918688161852161649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28032079783168431605764397 10512029918688161852161649)
              ·
                refine ⟨7884022439016121389121237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10512029918688161852161649 7884022439016121389121237)
                ·
                  refine ⟨184781775914440345057529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7884022439016121389121237 184781775914440345057529)
                  ·
                    rfl

theorem cell23_3238751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 7].length) (baseStart_3238751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238751 prefixEnd_3238751 := by exact prefixLift 3238751
  have htrace : WordTrace (prefixWord ++ tailWord_3238751) baseStart_3238751 baseEnd_3238751 := by
    simpa [prefixWord, tailWord_3238751, baseEnd_3238751] using wordTrace_append hprefix tailTrace_3238751
  have hstable : (prefixWord ++ tailWord_3238751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238751).length < 2 ^ (prefixWord ++ tailWord_3238751).sum := by decide
  have hdescent : baseEnd_3238751 < baseStart_3238751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238766 : List Nat := [4, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_3238766 : Nat := 118140960795 + 3238766 * 2 ^ 59
def prefixEnd_3238766 : Nat := 4983230072969 + 3 ^ 40 * 3238766 * 2
def baseEnd_3238766 : Nat := 1663043685439780546830193

theorem tailTrace_3238766 : CollatzResearch.WordTrace tailWord_3238766 prefixEnd_3238766 1663043685439780546830193 := by
  unfold tailWord_3238766
  simp only [CollatzResearch.WordTrace]
  refine ⟨14765937573063924255051019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78751667056340929360272101 14765937573063924255051019)
  ·
    refine ⟨22148906359595886382576529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14765937573063924255051019 22148906359595886382576529)
    ·
      refine ⟨16611679769696914786932397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22148906359595886382576529 16611679769696914786932397)
      ·
        refine ⟨6229379913636343045099649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16611679769696914786932397 6229379913636343045099649)
        ·
          refine ⟨4672034935227257283824737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6229379913636343045099649 4672034935227257283824737)
          ·
            refine ⟨3504026201420442962868553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4672034935227257283824737 3504026201420442962868553)
            ·
              refine ⟨2628019651065332222151415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3504026201420442962868553 2628019651065332222151415)
              ·
                refine ⟨3942029476597998333227123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2628019651065332222151415 3942029476597998333227123)
                ·
                  refine ⟨5913044214896997499840685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3942029476597998333227123 5913044214896997499840685)
                  ·
                    refine ⟨2217391580586374062440257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5913044214896997499840685 2217391580586374062440257)
                    ·
                      refine ⟨1663043685439780546830193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217391580586374062440257 1663043685439780546830193)
                      ·
                        rfl

theorem cell23_3238766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_3238766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238766 prefixEnd_3238766 := by exact prefixLift 3238766
  have htrace : WordTrace (prefixWord ++ tailWord_3238766) baseStart_3238766 baseEnd_3238766 := by
    simpa [prefixWord, tailWord_3238766, baseEnd_3238766] using wordTrace_append hprefix tailTrace_3238766
  have hstable : (prefixWord ++ tailWord_3238766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238766).length < 2 ^ (prefixWord ++ tailWord_3238766).sum := by decide
  have hdescent : baseEnd_3238766 < baseStart_3238766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238768 : List Nat := [2, 1, 1, 1, 4, 1, 3, 5, 5]
def baseStart_3238768 : Nat := 118140960795 + 3238768 * 2 ^ 59
def prefixEnd_3238768 : Nat := 4983230072969 + 3 ^ 40 * 3238768 * 2
def baseEnd_3238768 : Nat := 184782745822343282111687

theorem tailTrace_3238768 : CollatzResearch.WordTrace tailWord_3238768 prefixEnd_3238768 184782745822343282111687 := by
  unfold tailWord_3238768
  simp only [CollatzResearch.WordTrace]
  refine ⟨59063786765252074190990479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78751715687002765587987305 59063786765252074190990479)
  ·
    refine ⟨88595680147878111286485719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59063786765252074190990479 88595680147878111286485719)
    ·
      refine ⟨132893520221817166929728579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88595680147878111286485719 132893520221817166929728579)
      ·
        refine ⟨199340280332725750394592869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132893520221817166929728579 199340280332725750394592869)
        ·
          refine ⟨37376302562386078198986163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199340280332725750394592869 37376302562386078198986163)
          ·
            refine ⟨56064453843579117298479245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37376302562386078198986163 56064453843579117298479245)
            ·
              refine ⟨21024170191342168986929717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56064453843579117298479245 21024170191342168986929717)
              ·
                refine ⟨1971015955438328342524661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21024170191342168986929717 1971015955438328342524661)
                ·
                  refine ⟨184782745822343282111687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1971015955438328342524661 184782745822343282111687)
                  ·
                    rfl

theorem cell23_3238768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 5].length) (baseStart_3238768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238768 prefixEnd_3238768 := by exact prefixLift 3238768
  have htrace : WordTrace (prefixWord ++ tailWord_3238768) baseStart_3238768 baseEnd_3238768 := by
    simpa [prefixWord, tailWord_3238768, baseEnd_3238768] using wordTrace_append hprefix tailTrace_3238768
  have hstable : (prefixWord ++ tailWord_3238768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238768).length < 2 ^ (prefixWord ++ tailWord_3238768).sum := by decide
  have hdescent : baseEnd_3238768 < baseStart_3238768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238821 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_3238821 : Nat := 118140960795 + 3238821 * 2 ^ 59
def prefixEnd_3238821 : Nat := 4983230072969 + 3 ^ 40 * 3238821 * 2
def baseEnd_3238821 : Nat := 1663071926875777831642439

theorem tailTrace_3238821 : CollatzResearch.WordTrace tailWord_3238821 prefixEnd_3238821 1663071926875777831642439 := by
  unfold tailWord_3238821
  simp only [CollatzResearch.WordTrace]
  refine ⟨118129506599312138433660317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78753004399541425622440211 118129506599312138433660317)
  ·
    refine ⟨44298564974742051912622619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118129506599312138433660317 44298564974742051912622619)
    ·
      refine ⟨66447847462113077868933929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44298564974742051912622619 66447847462113077868933929)
      ·
        refine ⟨49835885596584808401700447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66447847462113077868933929 49835885596584808401700447)
        ·
          refine ⟨74753828394877212602550671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49835885596584808401700447 74753828394877212602550671)
          ·
            refine ⟨112130742592315818903826007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74753828394877212602550671 112130742592315818903826007)
            ·
              refine ⟨168196113888473728355739011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112130742592315818903826007 168196113888473728355739011)
              ·
                refine ⟨252294170832710592533608517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168196113888473728355739011 252294170832710592533608517)
                ·
                  refine ⟨47305157031133236100051597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252294170832710592533608517 47305157031133236100051597)
                  ·
                    refine ⟨17739433886674963537519349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47305157031133236100051597 17739433886674963537519349)
                    ·
                      refine ⟨1663071926875777831642439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17739433886674963537519349 1663071926875777831642439)
                      ·
                        rfl

theorem cell23_3238821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_3238821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238821 prefixEnd_3238821 := by exact prefixLift 3238821
  have htrace : WordTrace (prefixWord ++ tailWord_3238821) baseStart_3238821 baseEnd_3238821 := by
    simpa [prefixWord, tailWord_3238821, baseEnd_3238821] using wordTrace_append hprefix tailTrace_3238821
  have hstable : (prefixWord ++ tailWord_3238821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238821).length < 2 ^ (prefixWord ++ tailWord_3238821).sum := by decide
  have hdescent : baseEnd_3238821 < baseStart_3238821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238831 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 6]
def baseStart_3238831 : Nat := 118140960795 + 3238831 * 2 ^ 59
def prefixEnd_3238831 : Nat := 4983230072969 + 3 ^ 40 * 3238831 * 2
def baseEnd_3238831 : Nat := 1663077061682322792517393

theorem tailTrace_3238831 : CollatzResearch.WordTrace tailWord_3238831 prefixEnd_3238831 1663077061682322792517393 := by
  unfold tailWord_3238831
  simp only [CollatzResearch.WordTrace]
  refine ⟨118129871329275910141524347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78753247552850606761016231 118129871329275910141524347)
  ·
    refine ⟨177194806993913865212286521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118129871329275910141524347 177194806993913865212286521)
    ·
      refine ⟨132896105245435398909214891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177194806993913865212286521 132896105245435398909214891)
      ·
        refine ⟨199344157868153098363822337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132896105245435398909214891 199344157868153098363822337)
        ·
          refine ⟨149508118401114823772866753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199344157868153098363822337 149508118401114823772866753)
          ·
            refine ⟨112131088800836117829650065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149508118401114823772866753 112131088800836117829650065)
            ·
              refine ⟨84098316600627088372237549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112131088800836117829650065 84098316600627088372237549)
              ·
                refine ⟨31536868725235158139589081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84098316600627088372237549 31536868725235158139589081)
                ·
                  refine ⟨23652651543926368604691811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31536868725235158139589081 23652651543926368604691811)
                  ·
                    refine ⟨35478977315889552907037717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23652651543926368604691811 35478977315889552907037717)
                    ·
                      refine ⟨1663077061682322792517393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35478977315889552907037717 1663077061682322792517393)
                      ·
                        rfl

theorem cell23_3238831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_3238831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238831 prefixEnd_3238831 := by exact prefixLift 3238831
  have htrace : WordTrace (prefixWord ++ tailWord_3238831) baseStart_3238831 baseEnd_3238831 := by
    simpa [prefixWord, tailWord_3238831, baseEnd_3238831] using wordTrace_append hprefix tailTrace_3238831
  have hstable : (prefixWord ++ tailWord_3238831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238831).length < 2 ^ (prefixWord ++ tailWord_3238831).sum := by decide
  have hdescent : baseEnd_3238831 < baseStart_3238831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238935 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 1, 6]
def baseStart_3238935 : Nat := 118140960795 + 3238935 * 2 ^ 59
def prefixEnd_3238935 : Nat := 4983230072969 + 3 ^ 40 * 3238935 * 2
def baseEnd_3238935 : Nat := 554376821223463461872305

theorem tailTrace_3238935 : CollatzResearch.WordTrace tailWord_3238935 prefixEnd_3238935 554376821223463461872305 := by
  unfold tailWord_3238935
  simp only [CollatzResearch.WordTrace]
  refine ⟨118133664520899135903310259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78755776347266090602206839 118133664520899135903310259)
  ·
    refine ⟨177200496781348703854965389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118133664520899135903310259 177200496781348703854965389)
    ·
      refine ⟨66450186293005763945612021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177200496781348703854965389 66450186293005763945612021)
      ·
        refine ⟨6229704964969290369901127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66450186293005763945612021 6229704964969290369901127)
        ·
          refine ⟨9344557447453935554851691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6229704964969290369901127 9344557447453935554851691)
          ·
            refine ⟨14016836171180903332277537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9344557447453935554851691 14016836171180903332277537)
            ·
              refine ⟨10512627128385677499208153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14016836171180903332277537 10512627128385677499208153)
              ·
                refine ⟨7884470346289258124406115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10512627128385677499208153 7884470346289258124406115)
                ·
                  refine ⟨11826705519433887186609173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7884470346289258124406115 11826705519433887186609173)
                  ·
                    refine ⟨554376821223463461872305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11826705519433887186609173 554376821223463461872305)
                    ·
                      rfl

theorem cell23_3238935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_3238935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238935 prefixEnd_3238935 := by exact prefixLift 3238935
  have htrace : WordTrace (prefixWord ++ tailWord_3238935) baseStart_3238935 baseEnd_3238935 := by
    simpa [prefixWord, tailWord_3238935, baseEnd_3238935] using wordTrace_append hprefix tailTrace_3238935
  have hstable : (prefixWord ++ tailWord_3238935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238935).length < 2 ^ (prefixWord ++ tailWord_3238935).sum := by decide
  have hdescent : baseEnd_3238935 < baseStart_3238935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238969 : List Nat := [1, 2, 1, 5, 2, 2, 3, 1, 2, 4]
def baseStart_3238969 : Nat := 118140960795 + 3238969 * 2 ^ 59
def prefixEnd_3238969 : Nat := 4983230072969 + 3 ^ 40 * 3238969 * 2
def baseEnd_3238969 : Nat := 554382640670881084197253

theorem tailTrace_3238969 : CollatzResearch.WordTrace tailWord_3238969 prefixEnd_3238969 554382640670881084197253 := by
  unfold tailWord_3238969
  simp only [CollatzResearch.WordTrace]
  refine ⟨118134904602775959710047961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78756603068517306473365307 118134904602775959710047961)
  ·
    refine ⟨88601178452081969782535971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118134904602775959710047961 88601178452081969782535971)
    ·
      refine ⟨132901767678122954673803957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88601178452081969782535971 132901767678122954673803957)
      ·
        refine ⟨12459540719824027000669121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132901767678122954673803957 12459540719824027000669121)
        ·
          refine ⟨9344655539868020250501841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12459540719824027000669121 9344655539868020250501841)
          ·
            refine ⟨7008491654901015187876381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9344655539868020250501841 7008491654901015187876381)
            ·
              refine ⟨2628184370587880695453643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7008491654901015187876381 2628184370587880695453643)
              ·
                refine ⟨3942276555881821043180465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2628184370587880695453643 3942276555881821043180465)
                ·
                  refine ⟨2956707416911365782385349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3942276555881821043180465 2956707416911365782385349)
                  ·
                    refine ⟨554382640670881084197253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2956707416911365782385349 554382640670881084197253)
                    ·
                      rfl

theorem cell23_3238969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 2, 4].length) (baseStart_3238969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238969 prefixEnd_3238969 := by exact prefixLift 3238969
  have htrace : WordTrace (prefixWord ++ tailWord_3238969) baseStart_3238969 baseEnd_3238969 := by
    simpa [prefixWord, tailWord_3238969, baseEnd_3238969] using wordTrace_append hprefix tailTrace_3238969
  have hstable : (prefixWord ++ tailWord_3238969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238969).length < 2 ^ (prefixWord ++ tailWord_3238969).sum := by decide
  have hdescent : baseEnd_3238969 < baseStart_3238969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238972 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 1, 2, 4]
def baseStart_3238972 : Nat := 118140960795 + 3238972 * 2 ^ 59
def prefixEnd_3238972 : Nat := 4983230072969 + 3 ^ 40 * 3238972 * 2
def baseEnd_3238972 : Nat := 1663149462454606740854245

theorem tailTrace_3238972 : CollatzResearch.WordTrace tailWord_3238972 prefixEnd_3238972 1663149462454606740854245 := by
  unfold tailWord_3238972
  simp only [CollatzResearch.WordTrace]
  refine ⟨59067507010882545611203585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78756676014510060814938113 59067507010882545611203585)
  ·
    refine ⟨44300630258161909208402689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59067507010882545611203585 44300630258161909208402689)
    ·
      refine ⟨33225472693621431906302017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44300630258161909208402689 33225472693621431906302017)
      ·
        refine ⟨24919104520216073929726513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33225472693621431906302017 24919104520216073929726513)
        ·
          refine ⟨18689328390162055447294885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24919104520216073929726513 18689328390162055447294885)
          ·
            refine ⟨3504249073155385396367791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18689328390162055447294885 3504249073155385396367791)
            ·
              refine ⟨5256373609733078094551687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504249073155385396367791 5256373609733078094551687)
              ·
                refine ⟨7884560414599617141827531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5256373609733078094551687 7884560414599617141827531)
                ·
                  refine ⟨11826840621899425712741297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7884560414599617141827531 11826840621899425712741297)
                  ·
                    refine ⟨8870130466424569284555973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11826840621899425712741297 8870130466424569284555973)
                    ·
                      refine ⟨1663149462454606740854245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8870130466424569284555973 1663149462454606740854245)
                      ·
                        rfl

theorem cell23_3238972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_3238972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238972 prefixEnd_3238972 := by exact prefixLift 3238972
  have htrace : WordTrace (prefixWord ++ tailWord_3238972) baseStart_3238972 baseEnd_3238972 := by
    simpa [prefixWord, tailWord_3238972, baseEnd_3238972] using wordTrace_append hprefix tailTrace_3238972
  have hstable : (prefixWord ++ tailWord_3238972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238972).length < 2 ^ (prefixWord ++ tailWord_3238972).sum := by decide
  have hdescent : baseEnd_3238972 < baseStart_3238972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238982 : List Nat := [6, 1, 1, 1, 1, 3, 1, 9]
def baseStart_3238982 : Nat := 118140960795 + 3238982 * 2 ^ 59
def prefixEnd_3238982 : Nat := 4983230072969 + 3 ^ 40 * 3238982 * 2
def baseEnd_3238982 : Nat := 61598318417079692656637

theorem tailTrace_3238982 : CollatzResearch.WordTrace tailWord_3238982 prefixEnd_3238982 61598318417079692656637 := by
  unfold tailWord_3238982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3691730585991526966570975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78756919167819241953514133 3691730585991526966570975)
  ·
    refine ⟨5537595878987290449856463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3691730585991526966570975 5537595878987290449856463)
    ·
      refine ⟨8306393818480935674784695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5537595878987290449856463 8306393818480935674784695)
      ·
        refine ⟨12459590727721403512177043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8306393818480935674784695 12459590727721403512177043)
        ·
          refine ⟨18689386091582105268265565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12459590727721403512177043 18689386091582105268265565)
          ·
            refine ⟨7008519784343289475599587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18689386091582105268265565 7008519784343289475599587)
            ·
              refine ⟨10512779676514934213399381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7008519784343289475599587 10512779676514934213399381)
              ·
                refine ⟨61598318417079692656637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10512779676514934213399381 61598318417079692656637)
                ·
                  rfl

theorem cell23_3238982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_3238982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3238982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3238982 prefixEnd_3238982 := by exact prefixLift 3238982
  have htrace : WordTrace (prefixWord ++ tailWord_3238982) baseStart_3238982 baseEnd_3238982 := by
    simpa [prefixWord, tailWord_3238982, baseEnd_3238982] using wordTrace_append hprefix tailTrace_3238982
  have hstable : (prefixWord ++ tailWord_3238982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238982).length < 2 ^ (prefixWord ++ tailWord_3238982).sum := by decide
  have hdescent : baseEnd_3238982 < baseStart_3238982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239010 : List Nat := [3, 3, 2, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_3239010 : Nat := 118140960795 + 3239010 * 2 ^ 59
def prefixEnd_3239010 : Nat := 4983230072969 + 3 ^ 40 * 3239010 * 2
def baseEnd_3239010 : Nat := 1663168974719477592179071

theorem tailTrace_3239010 : CollatzResearch.WordTrace tailWord_3239010 prefixEnd_3239010 1663168974719477592179071 := by
  unfold tailWord_3239010
  simp only [CollatzResearch.WordTrace]
  refine ⟨29534099998906855928072621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78757599997084949141526989 29534099998906855928072621)
  ·
    refine ⟨11075287499590070973027233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29534099998906855928072621 11075287499590070973027233)
    ·
      refine ⟨8306465624692553229770425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11075287499590070973027233 8306465624692553229770425)
      ·
        refine ⟨6229849218519414922327819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8306465624692553229770425 6229849218519414922327819)
        ·
          refine ⟨9344773827779122383491729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6229849218519414922327819 9344773827779122383491729)
          ·
            refine ⟨7008580370834341787618797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9344773827779122383491729 7008580370834341787618797)
            ·
              refine ⟨2628217639062878170357049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7008580370834341787618797 2628217639062878170357049)
              ·
                refine ⟨1971163229297158627767787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2628217639062878170357049 1971163229297158627767787)
                ·
                  refine ⟨2956744843945737941651681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971163229297158627767787 2956744843945737941651681)
                  ·
                    refine ⟨2217558632959303456238761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2956744843945737941651681 2217558632959303456238761)
                    ·
                      refine ⟨1663168974719477592179071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217558632959303456238761 1663168974719477592179071)
                      ·
                        rfl

theorem cell23_3239010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_3239010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239010 prefixEnd_3239010 := by exact prefixLift 3239010
  have htrace : WordTrace (prefixWord ++ tailWord_3239010) baseStart_3239010 baseEnd_3239010 := by
    simpa [prefixWord, tailWord_3239010, baseEnd_3239010] using wordTrace_append hprefix tailTrace_3239010
  have hstable : (prefixWord ++ tailWord_3239010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239010).length < 2 ^ (prefixWord ++ tailWord_3239010).sum := by decide
  have hdescent : baseEnd_3239010 < baseStart_3239010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239066 : List Nat := [3, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2]
def baseStart_3239066 : Nat := 118140960795 + 3239066 * 2 ^ 59
def prefixEnd_3239066 : Nat := 4983230072969 + 3 ^ 40 * 3239066 * 2
def baseEnd_3239066 : Nat := 1663197729636129373078813

theorem tailTrace_3239066 : CollatzResearch.WordTrace tailWord_3239066 prefixEnd_3239066 1663197729636129373078813 := by
  unfold tailWord_3239066
  simp only [CollatzResearch.WordTrace]
  refine ⟨29534610620856136319082263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78758961655616363517552701 29534610620856136319082263)
  ·
    refine ⟨44301915931284204478623395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29534610620856136319082263 44301915931284204478623395)
    ·
      refine ⟨66452873896926306717935093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44301915931284204478623395 66452873896926306717935093)
      ·
        refine ⟨6229956927836841254806415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66452873896926306717935093 6229956927836841254806415)
        ·
          refine ⟨9344935391755261882209623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6229956927836841254806415 9344935391755261882209623)
          ·
            refine ⟨14017403087632892823314435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9344935391755261882209623 14017403087632892823314435)
            ·
              refine ⟨21026104631449339234971653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14017403087632892823314435 21026104631449339234971653)
              ·
                refine ⟨3942394618396751106557185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21026104631449339234971653 3942394618396751106557185)
                ·
                  refine ⟨2956795963797563329917889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3942394618396751106557185 2956795963797563329917889)
                  ·
                    refine ⟨2217596972848172497438417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2956795963797563329917889 2217596972848172497438417)
                    ·
                      refine ⟨1663197729636129373078813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217596972848172497438417 1663197729636129373078813)
                      ·
                        rfl

theorem cell23_3239066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_3239066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239066 prefixEnd_3239066 := by exact prefixLift 3239066
  have htrace : WordTrace (prefixWord ++ tailWord_3239066) baseStart_3239066 baseEnd_3239066 := by
    simpa [prefixWord, tailWord_3239066, baseEnd_3239066] using wordTrace_append hprefix tailTrace_3239066
  have hstable : (prefixWord ++ tailWord_3239066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239066).length < 2 ^ (prefixWord ++ tailWord_3239066).sum := by decide
  have hdescent : baseEnd_3239066 < baseStart_3239066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239072 : List Nat := [2, 1, 1, 4, 2, 1, 3, 4, 5]
def baseStart_3239072 : Nat := 118140960795 + 3239072 * 2 ^ 59
def prefixEnd_3239072 : Nat := 4983230072969 + 3 ^ 40 * 3239072 * 2
def baseEnd_3239072 : Nat := 184800090057784038844865

theorem tailTrace_3239072 : CollatzResearch.WordTrace tailWord_3239072 prefixEnd_3239072 184800090057784038844865 := by
  unfold tailWord_3239072
  simp only [CollatzResearch.WordTrace]
  refine ⟨59069330660701404150523735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78759107547601872200698313 59069330660701404150523735)
  ·
    refine ⟨88603995991052106225785603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59069330660701404150523735 88603995991052106225785603)
    ·
      refine ⟨132905993986578159338678405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88603995991052106225785603 132905993986578159338678405)
      ·
        refine ⟨24919873872483404876002201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132905993986578159338678405 24919873872483404876002201)
        ·
          refine ⟨18689905404362553657001651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24919873872483404876002201 18689905404362553657001651)
          ·
            refine ⟨28034858106543830485502477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18689905404362553657001651 28034858106543830485502477)
            ·
              refine ⟨10513071789953936432063429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28034858106543830485502477 10513071789953936432063429)
              ·
                refine ⟨1971200960616363081011893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10513071789953936432063429 1971200960616363081011893)
                ·
                  refine ⟨184800090057784038844865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1971200960616363081011893 184800090057784038844865)
                  ·
                    rfl

theorem cell23_3239072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 5].length) (baseStart_3239072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239072 prefixEnd_3239072 := by exact prefixLift 3239072
  have htrace : WordTrace (prefixWord ++ tailWord_3239072) baseStart_3239072 baseEnd_3239072 := by
    simpa [prefixWord, tailWord_3239072, baseEnd_3239072] using wordTrace_append hprefix tailTrace_3239072
  have hstable : (prefixWord ++ tailWord_3239072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239072).length < 2 ^ (prefixWord ++ tailWord_3239072).sum := by decide
  have hdescent : baseEnd_3239072 < baseStart_3239072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239102 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_3239102 : Nat := 118140960795 + 3239102 * 2 ^ 59
def prefixEnd_3239102 : Nat := 4983230072969 + 3 ^ 40 * 3239102 * 2
def baseEnd_3239102 : Nat := 554405404979897077409549

theorem tailTrace_3239102 : CollatzResearch.WordTrace tailWord_3239102 prefixEnd_3239102 554405404979897077409549 := by
  unfold tailWord_3239102
  simp only [CollatzResearch.WordTrace]
  refine ⟨14767469438911765428079945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78759837007529415616426373 14767469438911765428079945)
  ·
    refine ⟨11075602079183824071059959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14767469438911765428079945 11075602079183824071059959)
    ·
      refine ⟨16613403118775736106589939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11075602079183824071059959 16613403118775736106589939)
      ·
        refine ⟨24920104678163604159884909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16613403118775736106589939 24920104678163604159884909)
        ·
          refine ⟨9345039254311351559956841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24920104678163604159884909 9345039254311351559956841)
          ·
            refine ⟨7008779440733513669967631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9345039254311351559956841 7008779440733513669967631)
            ·
              refine ⟨10513169161100270504951447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7008779440733513669967631 10513169161100270504951447)
              ·
                refine ⟨15769753741650405757427171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10513169161100270504951447 15769753741650405757427171)
                ·
                  refine ⟨23654630612475608636140757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15769753741650405757427171 23654630612475608636140757)
                  ·
                    refine ⟨554405404979897077409549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23654630612475608636140757 554405404979897077409549)
                    ·
                      rfl

theorem cell23_3239102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_3239102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239102 prefixEnd_3239102 := by exact prefixLift 3239102
  have htrace : WordTrace (prefixWord ++ tailWord_3239102) baseStart_3239102 baseEnd_3239102 := by
    simpa [prefixWord, tailWord_3239102, baseEnd_3239102] using wordTrace_append hprefix tailTrace_3239102
  have hstable : (prefixWord ++ tailWord_3239102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239102).length < 2 ^ (prefixWord ++ tailWord_3239102).sum := by decide
  have hdescent : baseEnd_3239102 < baseStart_3239102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239117 : List Nat := [1, 6, 2, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_3239117 : Nat := 118140960795 + 3239117 * 2 ^ 59
def prefixEnd_3239117 : Nat := 4983230072969 + 3 ^ 40 * 3239117 * 2
def baseEnd_3239117 : Nat := 1663223917149508673541079

theorem tailTrace_3239117 : CollatzResearch.WordTrace tailWord_3239117 prefixEnd_3239117 1663223917149508673541079 := by
  unfold tailWord_3239117
  simp only [CollatzResearch.WordTrace]
  refine ⟨118140302606239780986435605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78760201737493187324290403 118140302606239780986435605)
  ·
    refine ⟨5537826684667489733739169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 118140302606239780986435605 5537826684667489733739169)
    ·
      refine ⟨4153370013500617300304377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5537826684667489733739169 4153370013500617300304377)
      ·
        refine ⟨3115027510125462975228283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4153370013500617300304377 3115027510125462975228283)
        ·
          refine ⟨4672541265188194462842425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3115027510125462975228283 4672541265188194462842425)
          ·
            refine ⟨3504405948891145847131819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4672541265188194462842425 3504405948891145847131819)
            ·
              refine ⟨5256608923336718770697729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504405948891145847131819 5256608923336718770697729)
              ·
                refine ⟨3942456692502539078023297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5256608923336718770697729 3942456692502539078023297)
                ·
                  refine ⟨2956842519376904308517473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3942456692502539078023297 2956842519376904308517473)
                  ·
                    refine ⟨2217631889532678231388105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2956842519376904308517473 2217631889532678231388105)
                    ·
                      refine ⟨1663223917149508673541079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217631889532678231388105 1663223917149508673541079)
                      ·
                        rfl

theorem cell23_3239117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_3239117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239117 prefixEnd_3239117 := by exact prefixLift 3239117
  have htrace : WordTrace (prefixWord ++ tailWord_3239117) baseStart_3239117 baseEnd_3239117 := by
    simpa [prefixWord, tailWord_3239117, baseEnd_3239117] using wordTrace_append hprefix tailTrace_3239117
  have hstable : (prefixWord ++ tailWord_3239117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239117).length < 2 ^ (prefixWord ++ tailWord_3239117).sum := by decide
  have hdescent : baseEnd_3239117 < baseStart_3239117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239122 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3239122 : Nat := 118140960795 + 3239122 * 2 ^ 59
def prefixEnd_3239122 : Nat := 4983230072969 + 3 ^ 40 * 3239122 * 2
def baseEnd_3239122 : Nat := 1663226484552781153978555

theorem tailTrace_3239122 : CollatzResearch.WordTrace tailWord_3239122 prefixEnd_3239122 1663226484552781153978555 := by
  unfold tailWord_3239122
  simp only [CollatzResearch.WordTrace]
  refine ⟨29535121242805416710091905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78760323314147777893578413 29535121242805416710091905)
  ·
    refine ⟨22151340932104062532568929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29535121242805416710091905 22151340932104062532568929)
    ·
      refine ⟨16613505699078046899426697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22151340932104062532568929 16613505699078046899426697)
      ·
        refine ⟨12460129274308535174570023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16613505699078046899426697 12460129274308535174570023)
        ·
          refine ⟨18690193911462802761855035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12460129274308535174570023 18690193911462802761855035)
          ·
            refine ⟨28035290867194204142782553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18690193911462802761855035 28035290867194204142782553)
            ·
              refine ⟨21026468150395653107086915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28035290867194204142782553 21026468150395653107086915)
              ·
                refine ⟨31539702225593479660630373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21026468150395653107086915 31539702225593479660630373)
                ·
                  refine ⟨5913694167298777436368195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31539702225593479660630373 5913694167298777436368195)
                  ·
                    refine ⟨8870541250948166154552293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5913694167298777436368195 8870541250948166154552293)
                    ·
                      refine ⟨1663226484552781153978555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8870541250948166154552293 1663226484552781153978555)
                      ·
                        rfl

theorem cell23_3239122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3239122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239122 prefixEnd_3239122 := by exact prefixLift 3239122
  have htrace : WordTrace (prefixWord ++ tailWord_3239122) baseStart_3239122 baseEnd_3239122 := by
    simpa [prefixWord, tailWord_3239122, baseEnd_3239122] using wordTrace_append hprefix tailTrace_3239122
  have hstable : (prefixWord ++ tailWord_3239122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239122).length < 2 ^ (prefixWord ++ tailWord_3239122).sum := by decide
  have hdescent : baseEnd_3239122 < baseStart_3239122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239149 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_3239149 : Nat := 118140960795 + 3239149 * 2 ^ 59
def prefixEnd_3239149 : Nat := 4983230072969 + 3 ^ 40 * 3239149 * 2
def baseEnd_3239149 : Nat := 554413449510150849446977

theorem tailTrace_3239149 : CollatzResearch.WordTrace tailWord_3239149 prefixEnd_3239149 554413449510150849446977 := by
  unfold tailWord_3239149
  simp only [CollatzResearch.WordTrace]
  refine ⟨118141469742123850451600501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78760979828082566967733667 118141469742123850451600501)
  ·
    refine ⟨11075762788324110979837547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118141469742123850451600501 11075762788324110979837547)
    ·
      refine ⟨16613644182486166469756321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11075762788324110979837547 16613644182486166469756321)
      ·
        refine ⟨12460233136864624852317241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16613644182486166469756321 12460233136864624852317241)
        ·
          refine ⟨9345174852648468639237931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12460233136864624852317241 9345174852648468639237931)
          ·
            refine ⟨14017762278972702958856897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9345174852648468639237931 14017762278972702958856897)
            ·
              refine ⟨10513321709229527219142673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14017762278972702958856897 10513321709229527219142673)
              ·
                refine ⟨7884991281922145414357005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10513321709229527219142673 7884991281922145414357005)
                ·
                  refine ⟨2956871730720804530383877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7884991281922145414357005 2956871730720804530383877)
                  ·
                    refine ⟨554413449510150849446977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2956871730720804530383877 554413449510150849446977)
                    ·
                      rfl

theorem cell23_3239149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_3239149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239149 prefixEnd_3239149 := by exact prefixLift 3239149
  have htrace : WordTrace (prefixWord ++ tailWord_3239149) baseStart_3239149 baseEnd_3239149 := by
    simpa [prefixWord, tailWord_3239149, baseEnd_3239149] using wordTrace_append hprefix tailTrace_3239149
  have hstable : (prefixWord ++ tailWord_3239149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239149).length < 2 ^ (prefixWord ++ tailWord_3239149).sum := by decide
  have hdescent : baseEnd_3239149 < baseStart_3239149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239195 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 4]
def baseStart_3239195 : Nat := 118140960795 + 3239195 * 2 ^ 59
def prefixEnd_3239195 : Nat := 4983230072969 + 3 ^ 40 * 3239195 * 2
def baseEnd_3239195 : Nat := 1663263968640559368365719

theorem tailTrace_3239195 : CollatzResearch.WordTrace tailWord_3239195 prefixEnd_3239195 1663263968640559368365719 := by
  unfold tailWord_3239195
  simp only [CollatzResearch.WordTrace]
  refine ⟨118143147499957200307775039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78762098333304800205183359 118143147499957200307775039)
  ·
    refine ⟨177214721249935800461662559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118143147499957200307775039 177214721249935800461662559)
    ·
      refine ⟨265822081874903700692493839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177214721249935800461662559 265822081874903700692493839)
      ·
        refine ⟨398733122812355551038740759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265822081874903700692493839 398733122812355551038740759)
        ·
          refine ⟨598099684218533326558111139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398733122812355551038740759 598099684218533326558111139)
          ·
            refine ⟨897149526327799989837166709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598099684218533326558111139 897149526327799989837166709)
            ·
              refine ⟨84107768093231249047234379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 897149526327799989837166709 84107768093231249047234379)
              ·
                refine ⟨126161652139846873570851569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84107768093231249047234379 126161652139846873570851569)
                ·
                  refine ⟨94621239104885155178138677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126161652139846873570851569 94621239104885155178138677)
                  ·
                    refine ⟨8870741166082983297950501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94621239104885155178138677 8870741166082983297950501)
                    ·
                      refine ⟨1663263968640559368365719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8870741166082983297950501 1663263968640559368365719)
                      ·
                        rfl

theorem cell23_3239195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 4].length) (baseStart_3239195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239195 prefixEnd_3239195 := by exact prefixLift 3239195
  have htrace : WordTrace (prefixWord ++ tailWord_3239195) baseStart_3239195 baseEnd_3239195 := by
    simpa [prefixWord, tailWord_3239195, baseEnd_3239195] using wordTrace_append hprefix tailTrace_3239195
  have hstable : (prefixWord ++ tailWord_3239195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239195).length < 2 ^ (prefixWord ++ tailWord_3239195).sum := by decide
  have hdescent : baseEnd_3239195 < baseStart_3239195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239239 : List Nat := [1, 1, 4, 1, 2, 3, 1, 4, 2, 4]
def baseStart_3239239 : Nat := 118140960795 + 3239239 * 2 ^ 59
def prefixEnd_3239239 : Nat := 4983230072969 + 3 ^ 40 * 3239239 * 2
def baseEnd_3239239 : Nat := 554428853929785732071839

theorem tailTrace_3239239 : CollatzResearch.WordTrace tailWord_3239239 prefixEnd_3239239 554428853929785732071839 := by
  unfold tailWord_3239239
  simp only [CollatzResearch.WordTrace]
  refine ⟨118144752311797795822376771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78763168207865197214917847 118144752311797795822376771)
  ·
    refine ⟨177217128467696693733565157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118144752311797795822376771 177217128467696693733565157)
    ·
      refine ⟨33228211587693130075043467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177217128467696693733565157 33228211587693130075043467)
      ·
        refine ⟨49842317381539695112565201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33228211587693130075043467 49842317381539695112565201)
        ·
          refine ⟨37381738036154771334423901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49842317381539695112565201 37381738036154771334423901)
          ·
            refine ⟨14018151763558039250408963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37381738036154771334423901 14018151763558039250408963)
            ·
              refine ⟨21027227645337058875613445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14018151763558039250408963 21027227645337058875613445)
              ·
                refine ⟨3942605183500698539177521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21027227645337058875613445 3942605183500698539177521)
                ·
                  refine ⟨2956953887625523904383141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3942605183500698539177521 2956953887625523904383141)
                  ·
                    refine ⟨554428853929785732071839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2956953887625523904383141 554428853929785732071839)
                    ·
                      rfl

theorem cell23_3239239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_3239239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239239 prefixEnd_3239239 := by exact prefixLift 3239239
  have htrace : WordTrace (prefixWord ++ tailWord_3239239) baseStart_3239239 baseEnd_3239239 := by
    simpa [prefixWord, tailWord_3239239, baseEnd_3239239] using wordTrace_append hprefix tailTrace_3239239
  have hstable : (prefixWord ++ tailWord_3239239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239239).length < 2 ^ (prefixWord ++ tailWord_3239239).sum := by decide
  have hdescent : baseEnd_3239239 < baseStart_3239239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239246 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2]
def baseStart_3239246 : Nat := 118140960795 + 3239246 * 2 ^ 59
def prefixEnd_3239246 : Nat := 4983230072969 + 3 ^ 40 * 3239246 * 2
def baseEnd_3239246 : Nat := 1663290156153938668827985

theorem tailTrace_3239246 : CollatzResearch.WordTrace tailWord_3239246 prefixEnd_3239246 1663290156153938668827985 := by
  unfold tailWord_3239246
  simp only [CollatzResearch.WordTrace]
  refine ⟨14768125952846554502235199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78763338415181624011921061 14768125952846554502235199)
  ·
    refine ⟨22152188929269831753352799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14768125952846554502235199 22152188929269831753352799)
    ·
      refine ⟨33228283393904747630029199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22152188929269831753352799 33228283393904747630029199)
      ·
        refine ⟨49842425090857121445043799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33228283393904747630029199 49842425090857121445043799)
        ·
          refine ⟨74763637636285682167565699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49842425090857121445043799 74763637636285682167565699)
          ·
            refine ⟨112145456454428523251348549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74763637636285682167565699 112145456454428523251348549)
            ·
              refine ⟨21027273085205348109627853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112145456454428523251348549 21027273085205348109627853)
              ·
                refine ⟨7885227406952005541110445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21027273085205348109627853 7885227406952005541110445)
                ·
                  refine ⟨2956960277607002077916417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7885227406952005541110445 2956960277607002077916417)
                  ·
                    refine ⟨2217720208205251558437313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2956960277607002077916417 2217720208205251558437313)
                    ·
                      refine ⟨1663290156153938668827985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217720208205251558437313 1663290156153938668827985)
                      ·
                        rfl

theorem cell23_3239246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_3239246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239246 prefixEnd_3239246 := by exact prefixLift 3239246
  have htrace : WordTrace (prefixWord ++ tailWord_3239246) baseStart_3239246 baseEnd_3239246 := by
    simpa [prefixWord, tailWord_3239246, baseEnd_3239246] using wordTrace_append hprefix tailTrace_3239246
  have hstable : (prefixWord ++ tailWord_3239246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239246).length < 2 ^ (prefixWord ++ tailWord_3239246).sum := by decide
  have hdescent : baseEnd_3239246 < baseStart_3239246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239266 : List Nat := [3, 3, 2, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_3239266 : Nat := 118140960795 + 3239266 * 2 ^ 59
def prefixEnd_3239266 : Nat := 4983230072969 + 3 ^ 40 * 3239266 * 2
def baseEnd_3239266 : Nat := 1663300425767028590577893

theorem tailTrace_3239266 : CollatzResearch.WordTrace tailWord_3239266 prefixEnd_3239266 1663300425767028590577893 := by
  unfold tailWord_3239266
  simp only [CollatzResearch.WordTrace]
  refine ⟨29536434270674994858402413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78763824721799986289073101 29536434270674994858402413)
  ·
    refine ⟨11076162851503123071900905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29536434270674994858402413 11076162851503123071900905)
    ·
      refine ⟨8307122138627342303925679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11076162851503123071900905 8307122138627342303925679)
      ·
        refine ⟨12460683207941013455888519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8307122138627342303925679 12460683207941013455888519)
        ·
          refine ⟨18691024811911520183832779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12460683207941013455888519 18691024811911520183832779)
          ·
            refine ⟨28036537217867280275749169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18691024811911520183832779 28036537217867280275749169)
            ·
              refine ⟨21027402913400460206811877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28036537217867280275749169 21027402913400460206811877)
              ·
                refine ⟨3942638046262586288777227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21027402913400460206811877 3942638046262586288777227)
                ·
                  refine ⟨5913957069393879433165841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3942638046262586288777227 5913957069393879433165841)
                  ·
                    refine ⟨4435467802045409574874381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5913957069393879433165841 4435467802045409574874381)
                    ·
                      refine ⟨1663300425767028590577893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4435467802045409574874381 1663300425767028590577893)
                      ·
                        rfl

theorem cell23_3239266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_3239266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239266 prefixEnd_3239266 := by exact prefixLift 3239266
  have htrace : WordTrace (prefixWord ++ tailWord_3239266) baseStart_3239266 baseEnd_3239266 := by
    simpa [prefixWord, tailWord_3239266, baseEnd_3239266] using wordTrace_append hprefix tailTrace_3239266
  have hstable : (prefixWord ++ tailWord_3239266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239266).length < 2 ^ (prefixWord ++ tailWord_3239266).sum := by decide
  have hdescent : baseEnd_3239266 < baseStart_3239266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239279 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 4, 1, 3]
def baseStart_3239279 : Nat := 118140960795 + 3239279 * 2 ^ 59
def prefixEnd_3239279 : Nat := 4983230072969 + 3 ^ 40 * 3239279 * 2
def baseEnd_3239279 : Nat := 1663307101015537039715333

theorem tailTrace_3239279 : CollatzResearch.WordTrace tailWord_3239279 prefixEnd_3239279 1663307101015537039715333 := by
  unfold tailWord_3239279
  simp only [CollatzResearch.WordTrace]
  refine ⟨118146211231652882653832891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78764140821101921769221927 118146211231652882653832891)
  ·
    refine ⟨177219316847479323980749337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118146211231652882653832891 177219316847479323980749337)
    ·
      refine ⟨132914487635609492985562003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177219316847479323980749337 132914487635609492985562003)
      ·
        refine ⟨199371731453414239478343005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132914487635609492985562003 199371731453414239478343005)
        ·
          refine ⟨74764399295030339804378627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199371731453414239478343005 74764399295030339804378627)
          ·
            refine ⟨112146598942545509706567941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74764399295030339804378627 112146598942545509706567941)
            ·
              refine ⟨21027487301727283069981489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112146598942545509706567941 21027487301727283069981489)
              ·
                refine ⟨15770615476295462302486117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21027487301727283069981489 15770615476295462302486117)
                ·
                  refine ⟨2956990401805399181716147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15770615476295462302486117 2956990401805399181716147)
                  ·
                    refine ⟨4435485602708098772574221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2956990401805399181716147 4435485602708098772574221)
                    ·
                      refine ⟨1663307101015537039715333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4435485602708098772574221 1663307101015537039715333)
                      ·
                        rfl

theorem cell23_3239279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 1, 3].length) (baseStart_3239279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239279 prefixEnd_3239279 := by exact prefixLift 3239279
  have htrace : WordTrace (prefixWord ++ tailWord_3239279) baseStart_3239279 baseEnd_3239279 := by
    simpa [prefixWord, tailWord_3239279, baseEnd_3239279] using wordTrace_append hprefix tailTrace_3239279
  have hstable : (prefixWord ++ tailWord_3239279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239279).length < 2 ^ (prefixWord ++ tailWord_3239279).sum := by decide
  have hdescent : baseEnd_3239279 < baseStart_3239279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
